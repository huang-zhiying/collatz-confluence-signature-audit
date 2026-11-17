"""k=64, fixed m, N=1e5: does the conditional support cross the 1024 bound?

One question, three independent m values, the protocol the attack actually uses.
"""
import json
import random
import time

from u_k_support import d_shortest, sample_pair

K = 64
N = 100_000
CHECK = [10_000, 20_000, 50_000, 100_000]
SEED = 20261119

rng = random.Random(SEED)
lo, hi = 1 << (K - 1), (1 << K) - 1
out = []
for j in range(3):
    a, b = sample_pair(K, rng)
    m = abs(a - b)
    seen = set()
    rec = {}
    t0 = time.time()
    for i in range(1, N + 1):
        ap = rng.randint(lo, hi)
        bp = ap + m if ap + m <= hi else ap - m
        if bp < lo:
            continue
        d = d_shortest(ap, bp)
        if d is not None:
            seen.add(d)
        if i in CHECK:
            rec[i] = len(seen)
            print(f"[m{j}] N={i:6d}  distinct={len(seen):5d}  {time.time()-t0:5.1f}s", flush=True)
    out.append({"m_bits": m.bit_length(), "counts": rec})

json.dump({"k": K, "N": N, "runs": out}, open("u_k64_n100k.json", "w"), indent=1)
print("written u_k64_n100k.json")
