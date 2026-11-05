// kernels/ss_rap_v2_barrett.cu
// Kernel CUDA i Korrigjuar për SS-RAP v2.0 (Zero `%` Division, 100% Register-Resident Barrett Reduction)
#include <cuda_runtime.h>
#include <stdint.h>

__constant__ uint32_t D_MODULI[5] = {
    2013265921u, // m_1: BabyBear  (15 * 2^27 + 1)
    2130706433u, // m_2: KoalaBear (127 * 2^24 + 1)
    2113929217u, // m_3: Prime-3   (63 * 2^25 + 1)
    1811939329u, // m_4: Prime-4   (27 * 2^26 + 1)
    1711276033u  // m_5: Prime-5   (51 * 2^25 + 1)
};

__constant__ uint64_t D_BARRETT_MU[5] = {
    9162596893ULL,  // floor(2^64 / m_1)
    8657571868ULL,  // floor(2^64 / m_2)
    8726282755ULL,  // floor(2^64 / m_3)
    10180663214ULL, // floor(2^64 / m_4)
    10779525756ULL  // floor(2^64 / m_5)
};

__device__ __forceinline__ uint32_t barrett_reduce_u64(uint64_t val, int ch) {
    uint64_t m  = (uint64_t)D_MODULI[ch];
    uint64_t mu = D_BARRETT_MU[ch];
    // __umul64hi llogarit (val * mu) >> 64 në 1 instruksion të vetëm harduerik PTX!
    uint64_t q  = __umul64hi(val, mu);
    uint64_t r  = val - q * m;
    if (r >= m) r -= m;
    if (r >= m) r -= m;
    return (uint32_t)r;
}

extern "C" __global__ void ss_rap_v2_decompose_and_eval_kernel(
    const uint64_t* __restrict__ d_a,
    const uint64_t* __restrict__ d_b,
    uint32_t* __restrict__ d_out_ch0,
    uint32_t* __restrict__ d_out_ch1,
    uint32_t* __restrict__ d_out_ch2,
    uint32_t* __restrict__ d_out_ch3,
    uint32_t* __restrict__ d_out_ch4,
    size_t n
) {
    size_t idx = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        uint64_t a = d_a[idx];
        uint64_t b = d_b[idx];

        uint32_t a0 = barrett_reduce_u64(a, 0), b0 = barrett_reduce_u64(b, 0);
        uint32_t a1 = barrett_reduce_u64(a, 1), b1 = barrett_reduce_u64(b, 1);
        uint32_t a2 = barrett_reduce_u64(a, 2), b2 = barrett_reduce_u64(b, 2);
        uint32_t a3 = barrett_reduce_u64(a, 3), b3 = barrett_reduce_u64(b, 3);
        uint32_t a4 = barrett_reduce_u64(a, 4), b4 = barrett_reduce_u64(b, 4);

        d_out_ch0[idx] = barrett_reduce_u64((uint64_t)a0 * b0, 0);
        d_out_ch1[idx] = barrett_reduce_u64((uint64_t)a1 * b1, 1);
        d_out_ch2[idx] = barrett_reduce_u64((uint64_t)a2 * b2, 2);
        d_out_ch3[idx] = barrett_reduce_u64((uint64_t)a3 * b3, 3);
        d_out_ch4[idx] = barrett_reduce_u64((uint64_t)a4 * b4, 4);
    }
}
