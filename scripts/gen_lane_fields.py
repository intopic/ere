import random, math
def is_prime(n):
    if n<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def rho(n):
    if n%2==0: return 2
    while True:
        c=random.randrange(1,n);f=lambda x:(x*x+c)%n
        x=y=random.randrange(2,n);d=1
        while d==1:
            x=f(x);y=f(f(y));d=math.gcd(abs(x-y),n)
        if d!=n: return d
def factor(n,out):
    if n==1: return
    if is_prime(n): out.add(n); return
    d=rho(n); factor(d,out); factor(n//d,out)
def primes_of(n):
    s=set(); factor(n,s); return sorted(s)

def emul(a,b,W,p):
    r=[0]*7
    for i in range(4):
        for j in range(4): r[i+j]+=a[i]*b[j]
    return [(r[i]+(W*r[i+4] if i+4<7 else 0))%p for i in range(4)]
def epow(a,e,W,p):
    res=[1,0,0,0]
    while e:
        if e&1: res=emul(res,a,W,p)
        a=emul(a,a,W,p); e>>=1
    return res
def sqrt_mod(a,p):
    # Tonelli-Shanks
    a%=p
    if pow(a,(p-1)//2,p)!=1: return None
    q=p-1;s=0
    while q%2==0:q//=2;s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m=s;c=pow(z,q,p);t=pow(a,q,p);r=pow(a,(q+1)//2,p)
    while t!=1:
        i=0;tt=t
        while tt!=1: tt=tt*tt%p;i+=1
        b=pow(c,1<<(m-i-1),p);m=i;c=b*b%p;t=t*c%p;r=r*b%p
    return r

def params(p,W,name,check=None):
    S=0;r=p-1
    while r%2==0:r//=2;S+=1
    pf=primes_of(p-1)
    g=2
    while any(pow(g,(p-1)//q,p)==1 for q in pf): g+=1
    w=pow(g,r,p)
    gens=[pow(w,1<<(S-i),p) for i in range(S+1)]
    assert gens[0]==1 and all(gens[i]*gens[i]%p==gens[i-1] for i in range(1,S+1))
    inv=lambda x:pow(x,p-2,p)
    r8=[pow(gens[3],k,p) for k in range(4)]; ir8=[inv(x) for x in r8]
    r16=[pow(gens[4],k,p) for k in range(8)]; ir16=[inv(x) for x in r16]
    assert pow(W,(p-1)//2,p)==p-1, "W must be a non-square"
    dth=pow(W,(p-1)//4,p)
    # two-adic extension generators
    c=sqrt_mod(gens[S]*inv(W)%p,p); assert c is not None
    a=[0,0,c,0]; assert emul(a,a,W,p)==[gens[S],0,0,0]
    b=None
    for cc in (c,p-c):
        a=[0,0,cc,0]
        d=sqrt_mod(cc*inv(W)%p,p)
        if d is not None: b=[0,0,0,d]; c=cc; break
        d=sqrt_mod(cc,p)
        if d is not None: b=[0,d,0,0]; c=cc; break
    assert b is not None and emul(b,b,W,p)==a and emul(a,a,W,p)==[gens[S],0,0,0]
    N=p**4-1; ef=primes_of(N)
    k=1
    while True:
        e=[k,1,0,0]
        if all(epow(e,N//q,W,p)!=[1,0,0,0] for q in ef): break
        k+=1
    mu=pow(p,-1,1<<32)
    if check: print(name,"check dth",dth,check)
    return dict(p=p,S=S,g=g,gens=gens,r8=r8,ir8=ir8,r16=r16,ir16=ir16,W=W,dth=dth,a=a,b=b,k=k,mu=mu)

# sanity vs BabyBear published constants
bb=params(2013265921,11,"bb",check=1728404513)
print("bb ext gen",bb['k'],"(p3: 8)", "a,b",bb['a'],bb['b'],"(p3: [0,0,1996171314,0],[0,0,0,124907976] or -)", "mu",hex(bb['mu']),"g",bb['g'])

def rust(n,P,Wv):
    x=params(P,Wv,n)
    T=n.upper()
    arr=lambda v:", ".join(hex(t) for t in v)
    return f'''
// ---- {n}: p = {P} = {(P-1)>>x['S']} * 2^{x['S']} + 1
pub type {n} = MontyField31<{n}Parameters>;

#[derive(Copy, Clone, Default, Debug, Eq, Hash, PartialEq)]
pub struct {n}Parameters;

impl MontyParameters for {n}Parameters {{
    const PRIME: u32 = {hex(P)};
    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = {hex(x['mu'])};
}}

impl PackedMontyParameters for {n}Parameters {{}}
impl BarrettParameters for {n}Parameters {{}}

impl FieldParameters for {n}Parameters {{
    const MONTY_GEN: {n} = {n}::new({x['g']});
}}

impl TwoAdicData for {n}Parameters {{
    const TWO_ADICITY: usize = {x['S']};
    type ArrayLike = &'static [{n}];
    const TWO_ADIC_GENERATORS: Self::ArrayLike = &{n}::new_array([{arr(x['gens'])}]);
    const ROOTS_8: Self::ArrayLike = &{n}::new_array([{arr(x['r8'])}]);
    const INV_ROOTS_8: Self::ArrayLike = &{n}::new_array([{arr(x['ir8'])}]);
    const ROOTS_16: Self::ArrayLike = &{n}::new_array([{arr(x['r16'])}]);
    const INV_ROOTS_16: Self::ArrayLike = &{n}::new_array([{arr(x['ir16'])}]);
}}

impl BinomialExtensionData<4> for {n}Parameters {{
    const W: {n} = {n}::new({Wv});
    const DTH_ROOT: {n} = {n}::new({x['dth']});
    const EXT_GENERATOR: [{n}; 4] = {n}::new_array([{x['k']}, 1, 0, 0]);
    const EXT_TWO_ADICITY: usize = {x['S']+2};
    type ArrayLike = [[{n}; 4]; 2];
    const TWO_ADIC_EXTENSION_GENERATORS: Self::ArrayLike = {n}::new_2d_array([{x['a']}, {x['b']}]);
}}

impl UniformSamplingField for {n}Parameters {{
    const MAX_SINGLE_SAMPLE_BITS: usize = {x['S']};
    const SAMPLING_BITS_M: [u64; 64] = sampling_bits({P});
}}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
impl p3_monty_31::MontyParametersAVX2 for {n}Parameters {{
    const PACKED_P: core::arch::x86_64::__m256i = unsafe {{ core::mem::transmute::<[u32; 8], _>([{hex(P)}; 8]) }};
    const PACKED_MU: core::arch::x86_64::__m256i = unsafe {{ core::mem::transmute::<[u32; 8], _>([{hex(x['mu'])}; 8]) }};
}}
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
impl p3_monty_31::MontyParametersAVX512 for {n}Parameters {{
    const PACKED_P: core::arch::x86_64::__m512i = unsafe {{ core::mem::transmute::<[u32; 16], _>([{hex(P)}; 16]) }};
    const PACKED_MU: core::arch::x86_64::__m512i = unsafe {{ core::mem::transmute::<[u32; 16], _>([{hex(x['mu'])}; 16]) }};
}}
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl p3_monty_31::MontyParametersNeon for {n}Parameters {{
    const PACKED_P: core::arch::aarch64::uint32x4_t = unsafe {{ core::mem::transmute::<[u32; 4], _>([{hex(P)}; 4]) }};
    const PACKED_MU: core::arch::aarch64::int32x4_t = unsafe {{ core::mem::transmute::<[i32; 4], _>([{x['mu'] if x['mu']<2**31 else x['mu']-2**32}; 4]) }};
}}
'''
import sys
out='''//! The three RNS lanes that Plonky3 does not ship (BabyBear and KoalaBear come from p3), as
//! Montgomery-31 fields. GENERATED by scripts/gen_lane_fields.py: generator, two-adic roots,
//! quartic extension x^4 - W (W = ss_rap_v2::EXTENSION_BETA, a non-square), all checked there.
#![allow(clippy::unreadable_literal)]

use p3_monty_31::{BarrettParameters, BinomialExtensionData, FieldParameters, MontyField31, MontyParameters, PackedMontyParameters, TwoAdicData};
use p3_field::UniformSamplingField;

const fn sampling_bits(prime: u64) -> [u64; 64] {
    let mut a = [0u64; 64];
    let mut k = 0;
    while k < 64 {
        a[k] = if k == 0 { prime } else { prime & !((1u64 << k) - 1) };
        k += 1;
    }
    a
}
'''
import re
for n,P,W in [("Lane3",2113929217,int(sys.argv[1])),("Lane4",1811939329,int(sys.argv[2])),("Lane5",1711276033,int(sys.argv[3]))]:
    out+=rust(n,P,W)
open(sys.argv[4],'w').write(out)
