# Lean formalization of the paper's unconditional layer

`Collatz.lean` machine-checks the part of the accompanying paper (*Structural
Obstacles in Trajectory-Confluence Collatz Signatures*) that the paper itself
classifies as **无条件** (unconditional). No Mathlib, no `sorry`.

## Scope

**Formalized**: §3.1 (obstacle one) and the four propositions of §2.4 (explicit
predecessor, explicit preimages, parity, modular projection — the last in its
conditional form). That is every unconditional result of the paper except the
algebra of `thm:guess`, which needs `ℚ` and `Finset` and lives in the sibling
repository `collatz-lean-guess`.

**Out of scope by construction**: §3.2's quantitative core (`U_k`, `H_2(D_k)`
and their growth in `k`). Those statements quantify over the distance
distribution of real trajectories; their truth is a numerical fact about a
finite object of size `2^k`, decidable per `k` by enumeration, not provable for
general `k`. The conditional shadows that *are* provable carry no information —
the hypothesis carries all the content.

## What is proved

| Paper label | Statement | Lean name |
|---|---|---|
| — | `T(x) = x/2` even, `3x+1` odd | `T` |
| — | `T^n`, additivity | `Tit`, `Tit_add`, `Tit_succ'` |
| — | cycle `1 → 4 → 2 → 1` | `T_four`, `T_two`, `T_one`, `T_three`, `cycle_iter` |
| `prop:ladder` | `T^d(2^d y) = y` | `ladder` |
| `prop:parity` | no adjacent `1`-`1` | `parity`, `parity_no_adjacent`, `parity_sequence` |
| `prop:modproj` | period `≤ 3` | `modproj` (integer), `modproj_mod` (`mod 2^k`) |
| `prop:compressed` | explicit preimages of `C` | `compressed_one`, `compressed_two`, `compressed_zero`, `compressed_not_unique` |
| `lem:oncycle` | `T^(τ+3r) x = z` | `oncycle` |
| `cor:adjust` | total step count is a free knob | `adjust` |
| `lem:mod3` | residues mod 3 covered | `three_residues_cover`, `off_spec`, `Arr_pairwise`, `Arr_covers`, `S_pairwise`, `S_covers` |
| `τ_z = min` | minimal arrival time | `off_unique`, `Arr_le_of_arrival`, `Arr_is_min`, `Arr_unique` |
| `thm:cyclekill` | Algorithm 1 is correct | `cyclekill_core`, `cyclekill_correct`, `guard_iff` |
| `prop:monotone` | `W_cyc(m,n) ⊆ W_cyc(m,n+3j)` | `monotone`, `Wcyc_mono`, `Wcyc_mono_mul` |

## What `cyclekill_correct` claims, and what it does not

It says: *conditional on a candidate passing the step-2 guard*
`min_z S_z ≤ n - 4`, the returned tuple satisfies `P_pk` — unconditionally,
with no Collatz assumption. The guard is the algorithm's **rejection
condition**, not a hypothesis about Collatz: a failing candidate is thrown
away and redrawn.

Not claimed: that the guard is passed within bounded time. That is the paper's
one measured input (`rem:uncond`). Also not claimed: the `O(k)` cost clause of
the abstract — no complexity model is built here.

The guard is stated untruncated as `S + 4 ≤ n`, whereas the paper writes
`min_z S_z ≤ n - 4` with Nat subtraction. `guard_iff` records that the two
agree for `n ≥ 4`; the truncated regime is degenerate (`n ≈ 14k` in practice).

Non-vacuity is not assumed: the `example` at the end of the file instantiates
all hypotheses at `a'=1, b'=2, m=1, n=5` and discharges them, so the theorem
is known to be non-empty.

## A note on `prop:compressed`

`strip2_pow_two_dvd` supplies the characterization the other lemmas were missing:
`n = 2^k * strip2 n` for some `k`. Together with `strip2_odd` (the result is odd)
and `strip2_dvd` (it divides `n`), this identifies `strip2 n` as the odd part of
`n`, i.e. as `n / 2 ^ v2 n` — so `C` is provably the paper's `C`, not merely
numerically equal to it on test inputs.



The formulas in the paper give *a* preimage of `y` under `C`, not *the* preimage:
`C 1 = C 5 = C 21 = 1` (`compressed_not_unique`), all with odd arguments.  The paper
therefore says "explicit preimages" rather than "closed-form inversion".  The third
case is proved without any parity hypothesis on `y` — stronger than the paper states.

`v₂` is not formalized: `strip2` removes every factor of two directly, which is the
same function on the odd part and needs no well-founded exponent.

## Compiling

Either works:

```powershell
# direct
& 'D:\tools\elan\toolchains\stable\bin\lean.exe' .\collatz_lean\lean\Collatz.lean

# via Lake, from collatz_lean\lean
& 'D:\tools\elan\toolchains\stable\bin\lake.exe' build
```

Lean 4.32.2, exit 0. The `lakefile.toml` + `lean-toolchain` pin
`leanprover/lean4:v4.32.2` (same rev as the local Mathlib clone), so
`thm:guess` can later be added by declaring a Mathlib dependency rather than
by hand-wiring paths.

**Mathlib is not required**, and neither is anything from `Std`:

- `Function.iterate` is absent from this toolchain's prelude — hence the
  hand-rolled `Tit`. (The `T^[n]` notation silently parses as a `List`.)
- `Nat.find` is absent from **both** core `Init` and `Std` (`import Std` does
  not provide it; it is a Mathlib addition). Hence `τ_z` is *characterized*
  via `Arr_is_min` + `Arr_unique` rather than *constructed*. This is not a
  weakening: `Arr` is proved to be an arrival time that is at most every
  arrival time, which is the defining property of the minimum, and any such
  time is proved equal to it.

The elan shims at `D:\tools\elan\bin` are currently broken (they attempt a
download and fail with an SSL error; `elan show` reports an invalid toolchain
`my_lean`). Call the toolchain binaries directly, as above.

## Axiom audit

19 `#print axioms` lines; 15 below budget, 4 needing `Classical.choice`.

```
'Collatz.ladder'             [propext, Quot.sound]
'Collatz.parity_no_adjacent' [propext, Quot.sound]
'Collatz.oncycle'            [propext, Quot.sound]
'Collatz.modproj'            [propext, Quot.sound]
'Collatz.modproj_mod'        [propext, Quot.sound]
'Collatz.adjust'             [propext, Quot.sound]
'Collatz.Arr_is_min'         [propext, Quot.sound]
'Collatz.Arr_unique'         [propext, Quot.sound]
'Collatz.compressed_one'     [propext, Quot.sound]
'Collatz.compressed_two'     [propext, Quot.sound]
'Collatz.compressed_zero'    [propext, Quot.sound]
'Collatz.compressed_not_unique' [propext, Quot.sound]
'Collatz.strip2_pow_two_dvd'   [propext, Quot.sound]
'Collatz.cyclekill_core'     [propext, Quot.sound]
'Collatz.Wcyc_mono_mul'      [propext, Quot.sound]
'Collatz.Arr_covers'         [propext, Classical.choice, Quot.sound]
'Collatz.S_covers'           [propext, Classical.choice, Quot.sound]
'Collatz.cyclekill_correct'  [propext, Classical.choice, Quot.sound]
'Collatz.guard_iff'          [propext, Classical.choice, Quot.sound]
```

Within the project target (`propext / Classical.choice / Quot.sound`); zero
`sorry`, no `native_decide`, no extra trusted constants.

## A note on `lem:mod3` — what changed and what did not

The paper's proof already runs off a *shared base time* `t_x`
(`τ_z(x) = t_x + σ_x(z)`); it does not use the minimality of `τ_z` for the
covering. What this formalization makes explicit is two things:

1. the base time need not be the **first** entry — the covering is uniform in
   it (any `t` with `Tit t x` on the cycle works);
2. the identification with `τ_z = min` does hold when the base *is* the first
   entry (`Arr_is_min`, `Arr_unique`).

So this is a slight weakening of a hypothesis plus a clarification of an
implicit premise. **It is not a correction.** The paper's argument was sound
as written, and an earlier draft of this README overstated it as a
"correction" — that claim has been withdrawn.

## Next

Nothing here. The remaining unconditional layer — the algebra of `thm:guess`
(infimum, supremum and average of `1/p`) — is in `collatz-lean-guess`; the
geometric expectation itself is not formalized, and the paper does not use its
derivation.

## What this repository deliberately does not contain

The manuscript is not included: this repository is the verification artifact
only.
