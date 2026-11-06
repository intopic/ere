// BN254 G1 and G2 multi-scalar multiplications on CUDA with sppark (Supranational, Apache-2.0).
// No license server: built from source with nvcc when the `sppark` feature is on.
//
// Layouts shared with Rust (gpu/src/sppark.rs), all field elements Montgomery (R = 2^256),
// the same representation as arkworks' Fp:
//   affine  G1: { x[4], y[4] } u64 limbs, the point at infinity is x = y = 0
//   affine  G2: { x.c0[4], x.c1[4], y.c0[4], y.c1[4] }
//   jacobian out: { X, Y, Z }, infinity when Z = 0 (arkworks' Projective is Jacobian too)
//   scalars: Fr Montgomery limbs (mont = true: sppark converts them on the device)

#include <cuda.h>

#include <ec/jacobian_t.hpp>
#include <ec/xyzz_t.hpp>
#include <ff/alt_bn128-fp2.hpp>

using namespace alt_bn128;

typedef jacobian_t<fp_t> point_t;
typedef xyzz_t<fp_t> bucket_t;
typedef bucket_t::affine_t affine_t;
typedef fr_t scalar_t;

typedef jacobian_t<fp2_t> point_fp2_t;
typedef xyzz_t<fp2_t> bucket_fp2_t;
typedef bucket_fp2_t::affine_t affine_fp2_t;

#include <msm/pippenger.cuh>

// pippenger.cuh instantiates its kernels for bucket_t / affine_t; the same for G2
template __global__
void accumulate<bucket_fp2_t, affine_fp2_t::mem_t>(bucket_fp2_t::mem_t buckets_[],
                                                   uint32_t nwins, uint32_t wbits,
                                                   /*const*/ affine_fp2_t::mem_t points_[],
                                                   const vec2d_t<uint32_t> digits,
                                                   const vec2d_t<uint32_t> histogram,
                                                   uint32_t sid);
template __global__
void batch_addition<bucket_fp2_t>(bucket_fp2_t::mem_t buckets[],
                                  const affine_fp2_t::mem_t points[], size_t npoints,
                                  const uint32_t digits[], const uint32_t& ndigits);
template __global__
void integrate<bucket_fp2_t>(bucket_fp2_t::mem_t buckets_[], uint32_t nwins,
                             uint32_t wbits, uint32_t nbits);

extern "C" RustError ss_rap_sppark_msm_g1(point_t* out, const affine_t points[], size_t npoints,
                                          const scalar_t scalars[])
{
    return mult_pippenger<bucket_t>(out, points, npoints, scalars, true, sizeof(affine_t));
}

extern "C" RustError ss_rap_sppark_msm_g2(point_fp2_t* out, const affine_fp2_t points[], size_t npoints,
                                          const scalar_t scalars[])
{
    return mult_pippenger<bucket_fp2_t>(out, points, npoints, scalars, true, sizeof(affine_fp2_t));
}
