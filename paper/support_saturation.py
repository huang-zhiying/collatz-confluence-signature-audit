"""Support-count saturation and a Chao1 check on U_k.

The paper's U_k is the expected number of distinct shortest-meeting distances at a
fixed difference m.  The readings in Table S5 are averages over m and are lower
bounds: more samples can only reveal more values.  This script asks how far the
observed count is from the total, by

  * growing N at a fixed honest m and recording the accumulation curve, and
  * estimating the unseen support with Chao1, S_chao1 = S_obs + f1^2 / (2 f2),
    where f1/f2 count values seen once/twice.

Chao1 is a lower bound on the total under an exchangeable-samples model; it is a
heuristic here, but it converts "the readings are lower bounds" into a number.

Read-only: prints a table, writes nothing.  Runtime about ten minutes.

Usage:  python support_saturation.py
"""
import random
import time

SEED = 20261128
BUDGET = 3300.0                      # seconds for the whole run


def T(x):
    return x // 2 if x % 2 == 0 else 3 * x + 1


def d_shortest(a, b, max_steps=50000):
    """Shortest total step count to the first common value, or None."""
    va, vb = {a: 0}, {b: 0}
    ca, cb = a, b
    for tot in range(1, max_steps + 1):
        ca = T(ca)
        if ca in vb:
            return tot + vb[ca]
        va[ca] = tot
        cb = T(cb)
        if cb in va:
            return va[cb] + tot
        vb[cb] = tot
    return None


def keygen(k):
    """One honest instance: two k-bit starts and their meeting distance."""
    while True:
        a = random.randint(1 << (k - 1), (1 << k) - 1)
        b = random.randint(1 << (k - 1), (1 << k) - 1)
        if a == b:
            continue
        r = d_shortest(a, b)
        if r is not None:
            return a, b, r


def block(k, nmax, marks, t0):
    a0, b0, _ = keygen(k)
    m = abs(a0 - b0)
    lo, hi = 1 << (k - 1), 1 << k
    cnt = {}
    for i in range(1, nmax + 1):
        if time.time() - t0 > BUDGET:
            print(f"  (time budget reached inside k={k}, N={i})")
            break
        a = random.randint(lo, hi - 1)
        for b in (a + m, a - m):
            if not (lo <= b < hi):
                continue
            d = d_shortest(a, b)
            if d is not None:
                cnt[d] = cnt.get(d, 0) + 1
        if i in marks:
            print(f"  k={k:4d} N={i:7d}  observed={len(cnt):5d}", flush=True)
    f1 = sum(1 for v in cnt.values() if v == 1)
    f2 = sum(1 for v in cnt.values() if v == 2)
    s = len(cnt)
    chao = s + (f1 * f1) / (2 * f2) if f2 else float("inf")
    print(f"  k={k}: S_obs={s}  f1={f1}  f2={f2}  Chao1={chao:.0f}  "
          f"unseen={100 * (chao - s) / s:.1f}%", flush=True)


def main():
    random.seed(SEED)
    t0 = time.time()
    plan = [
        (64, 400000, [1000, 3000, 10000, 30000, 100000, 200000, 400000]),
        (256, 150000, [1000, 3000, 10000, 30000, 100000, 150000]),
        (512, 40000, [1000, 3000, 10000, 30000, 40000]),
        (1024, 12000, [1000, 3000, 10000, 12000]),
    ]
    for k, nmax, marks in plan:
        print(f"== k={k} (N up to {nmax}) ==", flush=True)
        block(k, nmax, marks, t0)
    print(f"total runtime {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
