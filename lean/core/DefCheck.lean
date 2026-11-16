/-
  Definitional audit for `Collatz.lean`.

  Purpose: check that the Lean *definitions* are faithful to the objects the paper
  defines, by testing each against an independent characterisation that does not
  reuse the definition under test.  This complements the axiom audit (`#print
  axioms`): the axiom lines say "no unexplained trust", this file says "and the
  objects are the paper's objects".

    T / Tit    vs  the paper's stated values at x = 27, and Tit as iterated T
    C          vs  "c is odd and 3x+1 = 2^k * c"  — i.e. the paper's
                   (3x+1)/2^(v_2 (3x+1)), with no appeal to `strip2`
    Arr        vs  brute-force min { j | T^j x = z }  — the paper's tau_z
    distEq     vs  Int.natAbs (a - b) = m
    S          vs  pairwise-distinct residues mod 3  — the paper's lem:mod3
    Verifies   vs  the paper's own instance (a',b',m,n) = (1,2,1,5)

  THESE ARE FINITE-DOMAIN EMPIRICAL CHECKS, NOT PROOFS.  Where a proof exists it
  is cited in the docstring of the corresponding check: `Arr_is_min`/`Arr_unique`
  (Arr is tau_z), `strip2_pow_two_dvd` + `strip2_pow_two_mul` (C is the odd part),
  `S_pairwise` (the mod-3 covering).  What this file adds is independence, not
  certainty.

  Run it after the library is built (the file imports the compiled `.olean`):

      cd lean/core
      lake build                    # produce Collatz.olean
      lake env lean DefCheck.lean   # then run these checks

  Expected output: five lines, each ending in `true`.
-/
import Collatz

open Collatz

/-! A local decidability instance, so `Verifies`-adjacent predicates can be
    compared against brute force. -/
instance (a b m : Nat) : Decidable (distEq a b m) := by
  unfold distEq
  infer_instance

/-! ## Independent characterisations (none of them uses the definition tested) -/

/-- `c` is the odd part of `y`: `c` is odd and `y = 2^k * c` for some `k`.
    This is the paper's `y / 2^(v_2 y)` stated without `v_2`. -/
def isOddPart (y c : Nat) : Bool :=
  (c % 2 == 1) && ((List.range 40).any (fun k => 2 ^ k * c == y))

/-- Brute-force first time the orbit of `x` lands in `{1,2,4}`. -/
def firstCycle (x bound : Nat) : Option Nat :=
  (List.range bound).find? (fun j => decide (OnCycle (Tit j x)))

/-- Brute-force first time the orbit of `x` equals `z` — the paper's `tau_z`. -/
def firstArrival (x z bound : Nat) : Option Nat :=
  (List.range bound).find? (fun j => Tit j x == z)

/-! ## The checks -/

/-- `T` agrees with the paper's stated values, and `Tit` is iterated `T`. -/
def mapChecks : Bool :=
  (T 27 == 82) && (T 82 == 41) && (Tit 3 27 == T (T (T 27))) &&
  (Tit 0 27 == 27) && (T 0 == 0)

/-- `C` is the odd part of `3x+1`.
    Backed by proof: `strip2_pow_two_dvd` + `strip2_unique`. -/
def cChecks : Bool := (List.range 3000).all (fun x => isOddPart (3 * x + 1) (C x))

/-- `Arr t zx z`, with `t` the first cycle entry, is the paper's `tau_z`.
    Backed by proof: `Arr_is_min` + `Arr_unique`. -/
def arrChecks : Bool :=
  (List.range 300).all (fun i =>
    match firstCycle (i + 1) 300 with
    | none => true
    | some t =>
      ([1, 2, 4] : List Nat).all (fun z =>
        firstArrival (i + 1) z 300 == some (Arr t (Tit t (i + 1)) z)))

/-- `distEq a b m` is `|a - b| = m` on the integers. -/
def distChecks : Bool :=
  (List.range 50).all (fun a =>
    (List.range 50).all (fun b =>
      (List.range 50).all (fun m =>
        decide (distEq a b m) == (Int.natAbs ((a : Int) - (b : Int)) == m))))

/-- The three sums `S_z` have pairwise distinct residues mod 3 (`lem:mod3`).
    Backed by proof: `S_pairwise`. -/
def mod3Checks : Bool :=
  ([1, 2, 4] : List Nat).all (fun za =>
    ([1, 2, 4] : List Nat).all (fun zb =>
      (List.range 40).all (fun ta =>
        (List.range 40).all (fun tb =>
          let x := S ta za tb zb 1
          let y := S ta za tb zb 4
          let z := S ta za tb zb 2
          (x % 3 != y % 3) && (x % 3 != z % 3) && (y % 3 != z % 3)))))

#eval ("map    : T/Tit vs paper's values  ", mapChecks)
#eval ("C      : C = odd part of 3x+1    ", cChecks)
#eval ("Arr    : Arr = paper's tau_z     ", arrChecks)
#eval ("distEq : distEq = |a-b|          ", distChecks)
#eval ("S      : three sums cover mod 3  ", mod3Checks)

/-! ## `Verifies` against the paper's own instance

`Verifies` is a literal transcription of `P_pk = ∃ s t, T^s a = T^t b ∧ s+t = n
∧ |a-b| = m`; its only non-syntactic component is `distEq`, tested above.  These
two examples pin down that it accepts the paper's instance `(1,2,1,5)` — where the
attack returns `(s',t') = (2,3)` meeting at `2 = T^2(1) = T^3(2)` — and that it is
not vacuous. -/

example : Verifies 1 5 1 2 := ⟨2, 3, rfl, rfl, Or.inr rfl⟩

example : ¬ Verifies 5 0 1 2 := by
  rintro ⟨s, t, _he, hst, hd⟩
  have : s = 0 ∧ t = 0 := by omega
  rcases this with ⟨rfl, rfl⟩
  unfold distEq at hd
  omega
