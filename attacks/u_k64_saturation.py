"""Does the k=64 support saturate below the (D2) calibration bound?

(D2): U_k <= C_2 k^alpha.  Under the calibration the audit cites (alpha=1/2,
C_2=2^7) the bound at k=64 is 128*sqrt(64) = 1024.  Table 1 records 786 and the
new measurement at N=1.6e4 gives 856, still rising -- so the question is whether
the observed count saturates below 1024 or keeps going.

Reports, for k=64: distinct meeting distances at N = 1e4 ... 2e5 (marginal), and
the same for three fixed m values (the protocol actually used by the attack).
"""
import json
import random
import time

from u_k_support import d_shortest, sample_pair

K = 64
CHECKPOINTS = [10_000, 30_000, 60_000, 120_000, 200_000]
SEED = 20261118


def marginal():
    rng = random.Random(SEED + K)
    seen, rec = set(), {}
    t0 = time.time()
    for i in range(1, CHECKPOINTS[-1] + 1):
        a, b = sample_pair(K, rng)
        d = d_shortest(a, b)
        if d is not None:
            seen.add(d)
        if i in CHECKPOINTS:
            rec[i] = len(seen)
            print(f"[marginal k={K}] N={i:7d}  distinct={len(seen):5d}  {time.time()-t0:6.1f}s", flush=True)
    return rec


def fixed_m(n_m=3, n_samples=50_000):
    rng = random.Random(SEED + 7 + K)
    lo, hi = 1 << (K - 1), (1 << K) - 1
    out = []
    for j in range(n_m):
        a, b = sample_pair(K, rng)
        m = abs(a - b)
        seen = set()
        t0 = time.time()
        for i in range(1, n_samples + 1):
            ap = rng.randint(lo, hi)
            bp = ap + m if ap + m <= hi else ap - m
            if bp < lo:
                continue
            d = d_shortest(ap, bp)
            if d is not None:
                seen.add(d)
            if i in (10_000, 50_000):
                print(f"[fixed-m {j} k={K}] N={i:6d}  distinct={len(seen):5d}  {time.time()-t0:6.1f}s", flush=True)
        out.append({"m_bits": m.bit_length(), "at_1e4": None, "final": len(seen)})
    return out


if __name__ == "__main__":
    t0 = time.time()
    marg = marginal()
    fm = fixed_m()
    json.dump({"k": K, "marginal": {str(k): v for k, v in marg.items()}, "fixed_m": fm},
              open("u_k64_saturation.json", "w"), indent=1)
    print(f"done in {time.time()-t0:.0f}s; written u_k64_saturation.json")
