//! Payment module: the PDF's "smart mid-price" (f.1) with real per-batch cost accounting.
//!
//! List prices from the PDF: $0.006 per transfer, $0.025 per DeFi swap (weighted average about
//! $0.015). The PDF stresses this is not a race to the bottom and that a safety buffer must
//! survive L1 gas spikes. So the price of a transaction is
//!
//! ```text
//! fee = max(list_price, cost_per_tx * (1 + safety_buffer))
//! ```
//!
//! i.e. we never settle a batch below cost, and in normal conditions we charge the list price.
//! All costs are computed from inputs that can be measured (settlement gas from the Foundry
//! gas report, blob gas, prover seconds from the benchmarks), not assumed.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TxKind {
    Transfer,
    Swap,
}

/// Prices in micro-USD (1e-6 USD) so that accounting is exact.
#[derive(Clone, Copy, Debug)]
pub struct FeeSchedule {
    pub transfer_micro_usd: u64,
    pub swap_micro_usd: u64,
    pub safety_buffer_bps: u64,
}

impl Default for FeeSchedule {
    fn default() -> Self {
        Self { transfer_micro_usd: 6_000, swap_micro_usd: 25_000, safety_buffer_bps: 2_000 }
    }
}

impl FeeSchedule {
    pub fn list_price(&self, kind: TxKind) -> u64 {
        match kind {
            TxKind::Transfer => self.transfer_micro_usd,
            TxKind::Swap => self.swap_micro_usd,
        }
    }

    /// max(list, cost * (1 + buffer)), rounded up.
    pub fn price(&self, kind: TxKind, cost_per_tx_micro_usd: u64) -> u64 {
        let floor = (cost_per_tx_micro_usd * (10_000 + self.safety_buffer_bps)).div_ceil(10_000);
        self.list_price(kind).max(floor)
    }
}

/// Everything that costs money for one batch.
#[derive(Clone, Copy, Debug)]
pub struct CostModel {
    /// Gas of `verifyAndSettleBatchV2` (measure with `forge test --gas-report`).
    pub settle_gas: u64,
    pub gas_price_gwei: f64,
    /// One EIP-4844 blob = 131072 blob gas.
    pub blob_gas: u64,
    pub blob_gas_price_gwei: f64,
    pub eth_usd: f64,
    /// Measured prover time per batch and the hourly price of that hardware.
    pub prover_seconds: f64,
    pub prover_usd_per_hour: f64,
    /// Batches whose proofs are aggregated into one L1 verification (1 = no aggregation).
    pub batches_per_settlement: u32,
}

impl Default for CostModel {
    fn default() -> Self {
        Self {
            settle_gas: 240_000,
            gas_price_gwei: 1.0,
            blob_gas: 131_072,
            blob_gas_price_gwei: 0.001,
            eth_usd: 3_000.0,
            prover_seconds: 4.0,
            prover_usd_per_hour: 2.0,
            batches_per_settlement: 1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BatchCost {
    pub l1_usd: f64,
    pub blob_usd: f64,
    pub prover_usd: f64,
}

impl BatchCost {
    pub fn total(&self) -> f64 {
        self.l1_usd + self.blob_usd + self.prover_usd
    }
}

impl CostModel {
    pub fn batch_cost(&self) -> BatchCost {
        let gwei_usd = self.eth_usd * 1e-9;
        BatchCost {
            l1_usd: self.settle_gas as f64 * self.gas_price_gwei * gwei_usd / self.batches_per_settlement.max(1) as f64,
            blob_usd: self.blob_gas as f64 * self.blob_gas_price_gwei * gwei_usd,
            prover_usd: self.prover_seconds / 3600.0 * self.prover_usd_per_hour,
        }
    }

    pub fn cost_per_tx_micro_usd(&self, txs: usize) -> u64 {
        (self.batch_cost().total() * 1e6 / txs.max(1) as f64).ceil() as u64
    }
}

#[derive(Clone, Debug)]
pub struct BatchEconomics {
    pub txs: usize,
    pub transfers: usize,
    pub swaps: usize,
    pub revenue_usd: f64,
    pub cost: BatchCost,
    pub cost_per_tx_usd: f64,
    pub avg_fee_usd: f64,
    pub net_margin_pct: f64,
    /// True when gas was high enough that the cost floor, not the list price, set the fee.
    pub floor_active: bool,
}

pub fn batch_economics(kinds: &[TxKind], schedule: &FeeSchedule, model: &CostModel) -> BatchEconomics {
    let txs = kinds.len();
    let cost_tx = model.cost_per_tx_micro_usd(txs);
    let revenue_micro: u64 = kinds.iter().map(|&k| schedule.price(k, cost_tx)).sum();
    let floor_active = kinds.iter().any(|&k| schedule.price(k, cost_tx) > schedule.list_price(k));
    let cost = model.batch_cost();
    let revenue_usd = revenue_micro as f64 / 1e6;
    BatchEconomics {
        txs,
        transfers: kinds.iter().filter(|&&k| k == TxKind::Transfer).count(),
        swaps: kinds.iter().filter(|&&k| k == TxKind::Swap).count(),
        revenue_usd,
        cost,
        cost_per_tx_usd: cost.total() / txs.max(1) as f64,
        avg_fee_usd: revenue_usd / txs.max(1) as f64,
        net_margin_pct: if revenue_usd > 0.0 { 100.0 * (revenue_usd - cost.total()) / revenue_usd } else { 0.0 },
        floor_active,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 1000 tx with the mix that gives the PDF's ~$0.015 weighted average.
    fn pdf_mix() -> Vec<TxKind> {
        (0..1000).map(|i| if i < 526 { TxKind::Transfer } else { TxKind::Swap }).collect()
    }

    #[test]
    fn list_prices_match_pdf() {
        let e = batch_economics(&pdf_mix(), &FeeSchedule::default(), &CostModel::default());
        assert!((e.avg_fee_usd - 0.015).abs() < 0.0002, "avg {}", e.avg_fee_usd);
        assert!(!e.floor_active);
    }

    #[test]
    fn normal_gas_gives_high_margin() {
        // 1 gwei, ETH $3000, 240k gas, 4 s on a $2/h GPU: batch cost ~ $0.72, under the PDF's
        // conservative $1.60 reserve, so the net margin is above the PDF's 89.3%.
        let e = batch_economics(&pdf_mix(), &FeeSchedule::default(), &CostModel::default());
        assert!(e.cost.total() < 1.60, "cost {}", e.cost.total());
        assert!(e.net_margin_pct > 89.3, "margin {}", e.net_margin_pct);
    }

    #[test]
    fn gas_spike_never_sells_below_cost() {
        let spike = CostModel { gas_price_gwei: 60.0, ..CostModel::default() };
        let s = FeeSchedule::default();
        let e = batch_economics(&pdf_mix(), &s, &spike);
        assert!(e.floor_active);
        // Every tx pays at least cost * (1 + buffer), so margin >= buffer / (1 + buffer).
        let min_margin = 100.0 * s.safety_buffer_bps as f64 / (10_000 + s.safety_buffer_bps) as f64;
        assert!(e.net_margin_pct >= min_margin - 0.01, "margin {} < {}", e.net_margin_pct, min_margin);
    }

    #[test]
    fn aggregation_cuts_l1_cost() {
        let one = CostModel::default().batch_cost();
        let ten = CostModel { batches_per_settlement: 10, ..CostModel::default() }.batch_cost();
        assert!((one.l1_usd / ten.l1_usd - 10.0).abs() < 1e-9);
    }

    #[test]
    fn price_rounds_up() {
        let s = FeeSchedule { transfer_micro_usd: 1, swap_micro_usd: 1, safety_buffer_bps: 1 };
        assert_eq!(s.price(TxKind::Transfer, 10_001), 10_003); // 10001 * 1.0001 = 10002.0001 -> 10003
    }
}
