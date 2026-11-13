# Guessing-cost identities — the algebraic layer of `thm:guess`

Companion to `../collatz_lean0/lean/Collatz.lean`. That project is dependency-free and
covers §2.4 plus obstacle one; this one covers the *algebra* of the paper's
Theorem `thm:guess` and therefore needs Mathlib (`ℚ`, `Finset`).

**Pinned:** Lean `4.32.2` · Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`
(2026-07-28) · axiom output in `AXIOMS.txt`.

## What is proved

| Paper statement | Lean name | Content |
|---|---|---|
| `thm:guess`, infimum | `Guess.cost_isLeast` | `IsLeast (range (1/p)) (1/p_max)` — the mode's cost `2^{H_inf}` is the least cost |
| `thm:guess`, supremum | `Guess.cost_isGreatest` | `IsGreatest (range (1/p)) (1/p_min)` — the least probable instance is the most expensive |
| `thm:guess`, average | `Guess.cost_avg` | `∑ i, p i * (1 / p i) = n = U` |

Axiom footprint: `[propext, Classical.choice, Quot.sound]` for all three; no `sorry`,
no `native_decide`.

## The error this found

The paper's original first identity was

```
max_x E[N(x)] = 1 / max_x p(x)        -- FALSE
```

Counterexample: `p = (9/10, 1/10)` gives `E[N] = (10/9, 10)`, so the two sides are
`10` and `10/9`. Since `1/p` is antitone, the maximum of `1/p` sits at the *minimum*
of `p`. The corrected statement is two-sided:

```
min_x E[N(x)] = 1 / max_x p(x) = 2^{H_inf}(D)
max_x E[N(x)] = 1 / min_x p(x)
```

Proving the original form is impossible; the corrected paper states the two-sided
version, and `cost_isLeast` / `cost_isGreatest` are exactly its two halves.

## What is *not* formalized

- **The geometric expectation itself** (`N(x) ~ Geom(p(x)) ⟹ E[N(x)] = 1/p(x)`). That
  is an infinite series (`tsum`), and the paper never uses the derivation — only the
  resulting identities. Layer 3 of the project plan; deliberately skipped.
- **`2^{H_inf}` as a logarithm.** `H_inf = -log2 (max p)` needs `Real.log`; the Lean
  statements stay on the algebraic side (`1/p_max`), which is what the audit uses.

## Build

Three routes, in order of preference:

```bash
./lake-verify.sh                      # canonical here: rev check, then lake build
lake build                            # same, without the rev check
lake exe cache get && lake build      # from scratch, on a networked machine
./build.sh                            # fallback: no Lake, no junction
```

Because the package directory is shared and mutable, `lake build` alone trusts the
manifest and will silently compile against a different Mathlib if the shared
checkout moved. `lake-verify.sh` compares the two revisions first and exits
non-zero on any mismatch — use it, or `build.sh`, whenever the shared directory
may have changed.

`lake build` works here because `.lake/packages` is a **directory junction** to the
prebuilt package set of a sibling project (`pvsnp-code`), and `lake-manifest.json`
pins all nine package revisions. Measured: 923 jobs, 28 s from an empty
`.lake/build`, no network.

Diagnosis worth keeping: the blocker was the **manifest**, not the junction. With
no manifest, Lake insists on resolving the rev and fails with `invalid index-pack
output` — "cannot reach GitHub, but refuses to use the local copy" — even when the
packages are present and built. A complete `lake-manifest.json` plus a package
directory is what makes the offline build work.

Two things to know about that junction:

- it is local only (`.lake/` is gitignored) and is **not** part of the artifact;
- it shares mutable state with the sibling project. Both pin Mathlib at
  `905b95818e`, so nothing drifts today, but a `lake build` here can check out
  that rev in the shared directory. `build.sh` hard-fails on rev drift, so use it
  when in doubt.

On a machine without the junction, `lake exe cache get && lake build` fetches the
pinned Mathlib and rebuilds; `./build.sh` is the offline fallback that borrows a
clone via `LEAN_PATH` and refuses to compile if the rev or Lean version differs.

Oleans are deliberately **not** vendored: they are version- and platform-specific,
and a GB-sized blob in the supplementary material would hurt more than help.
