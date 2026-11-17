"""Support of the meeting-distance distribution: marginal vs fixed-m conditional.

Two questions, both empirical:

  A. Is U_k (the number of distinct meeting distances d(a,b)) a genuine plateau,
     or an artefact of the sample size?  If the support keeps growing roughly
     linearly with N, the reported ~10^3 is sampling-limited and the true support
     is larger.
  B. The attack fixes m = |a-b| from the public key and samples a' with
     b' = a' +- m.  Does the conditional distribution d(a',b') | (|a'-b'| = m)
     have the same support as the marginal D_k?  The paper claims the two are
     statistically indistinguishable; this measures U_{k,m} directly.

d(a,b) is computed exactly as in attacks/round4_m_only.py (interleaved walk, first
collision = minimal s+t, valid because Collatz orbits merge and never split).
"""
import json
import random
import statistics
import sys

MAX_STEPS = 30000


def T(x):
    return x // 2 if x % 2 == 0 else 3 * x + 1


def d_shortest(a, b, max_steps=MAX_STEPS):
    """min s + t over all pairs with T^s(a) = T^t(b).

    The published scripts walk the two orbits in lockstep and return at the first
    collision.  That returns the first *lockstep* hit, which need not minimise
    s + t: for a=2, b=491 the walk returns 141 (found at t=139) while the minimum
    is 140 (a's step 0 meets b's step 140).  Here both orbits are walked once,
    each value recorded at its first visit, and the minimum is taken over the
    intersection -- exact, because s >= va[v] and t >= vb[v] for any meeting at v.
    """
    def walk(x):
        steps = {}
        cur, i = x, 0
        while i <= max_steps and cur not in steps:
            steps[cur] = i
            cur = T(cur)
            i += 1
        return steps

    va, vb = walk(a), walk(b)
    common = va.keys() & vb.keys()
    return min((va[v] + vb[v] for v in common), default=None)


def sample_pair(k, rng):
    lo, hi = 1 << (k - 1), (1 << k) - 1
    a = rng.randint(lo, hi)
    b = rng.randint(lo, hi)
    while b == a:
        b = rng.randint(lo, hi)
    return a, b


def part_a(ks, checkpoints, seed=20261117):
    out = {}
    for k in ks:
        rng = random.Random(seed + k)
        seen = set()
        rec = {}
        n = 0
        for i in range(1, max(checkpoints) + 1):
            a, b = sample_pair(k, rng)
            d = d_shortest(a, b)
            if d is not None:
                seen.add(d)
                n += 1
            if i in checkpoints:
                rec[i] = len(seen)
        out[k] = {"distinct": rec, "pairs_used": n}
        print(f"[A] k={k:4d}  " + "  ".join(f"N={c}:{rec[c]}" for c in checkpoints), flush=True)
    return out


def part_b(ks, per_k=5, n_samples=2000, seed=20261118):
    out = {}
    for k in ks:
        rng = random.Random(seed + k)
        rows = []
        for _ in range(per_k):
            a, b = sample_pair(k, rng)
            m = abs(a - b)
            lo, hi = 1 << (k - 1), (1 << k) - 1
            seen = set()
            used = 0
            for _ in range(n_samples):
                ap = rng.randint(lo, hi)
                bp = ap + m if ap + m <= hi else ap - m
                if bp < lo:
                    continue
                d = d_shortest(ap, bp)
                if d is not None:
                    seen.add(d)
                    used += 1
            rows.append({"m_bits": m.bit_length(), "distinct": len(seen), "used": used})
        vals = [r["distinct"] for r in rows]
        out[k] = {"rows": rows, "min": min(vals), "median": statistics.median(vals), "max": max(vals)}
        print(f"[B] k={k:4d}  U_(k,m) over {per_k} fixed m: min={min(vals)} "
              f"median={statistics.median(vals)} max={max(vals)}", flush=True)
    return out


if __name__ == "__main__":
    ks_a = [64, 128, 256, 512]
    checkpoints = [1000, 2000, 4000, 8000, 16000]
    a = part_a(ks_a, checkpoints)
    b = part_b([64, 128, 256])
    json.dump({"A": {str(k): v for k, v in a.items()},
               "B": {str(k): v for k, v in b.items()}},
              open("u_k_support.json", "w"), indent=1)
    print("written: u_k_support.json")
