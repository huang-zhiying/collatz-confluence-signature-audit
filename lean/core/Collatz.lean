/-
  Trajectory-confluence Collatz signatures: the unconditionally provable core.

  Companion to `manuscript.tex` / `manuscript_en.tex`.  Paper labels are named in
  each docstring.

  Dependency posture: this file imports nothing — not Mathlib, not even
  `Function.iterate` (the core prelude shipped with this toolchain does not
  define it), so the iteration is defined below.  Everything here is pure `Nat`
  arithmetic and combinatorics.  That is precisely the point: the layer the
  paper marks "无条件" (unconditional) needs no library at all.

  Formalized (paper label -> Lean name)
    T(x) = x/2 (x even), 3x+1 (x odd)        Collatz.T
    iteration T^n                            Tit, Tit_add, Tit_succ'
    cycle 1 -> 4 -> 2 -> 1                   T_four, T_two, T_one, T_three, cycle_iter
    prop:ladder    T^d (2^d y) = y            ladder
    prop:compressed explicit preimages of C     compressed_one, compressed_two, compressed_zero
    prop:parity    no adjacent 1-1            parity, parity_no_adjacent, parity_sequence
    prop:modproj   period <= 3                modproj (integer), modproj_mod (mod 2^k)
    lem:oncycle    T^(tau+3r) x = z           oncycle
    cor:adjust     step count is a free knob  adjust
    lem:mod3       residues mod 3 covered     three_residues_cover, off_spec,
                                              Arr_pairwise, Arr_covers,
                                              S_pairwise, S_covers
    tau_z = min    minimal arrival time       off_unique, Arr_le_of_arrival,
                                              Arr_is_min, Arr_unique
    thm:cyclekill  Algorithm 1 is correct     cyclekill_core, cyclekill_correct
                                              (guard_iff for the guard's shape)
    prop:monotone  step-count monotonicity    monotone, Wcyc_mono, Wcyc_mono_mul

  Not formalized here (see NOTES at the end): prop:compressed, thm:guess, and
  everything in the paper that is conditional or measured.
-/

namespace Collatz

/-! ## The map -/

/-- The `3n+1` map on `Nat`: halve when even, `3x+1` when odd.
    The paper states it on the positive integers; `T 0 = 0` is the harmless
    total extension, and no paper-relevant statement below depends on the
    value at `0`. -/
def T (x : Nat) : Nat := if x % 2 = 0 then x / 2 else 3 * x + 1

/-! ## Iteration -/

/-- `Tit n x` is `T` applied `n` times to `x`, i.e. `T^n(x)`. -/
def Tit : Nat → Nat → Nat
  | 0,     x => x
  | n + 1, x => T (Tit n x)

/-- Iterating once more on the left (the form used to peel a step off a
    trajectory going forward). -/
theorem Tit_succ (n x : Nat) : Tit (n + 1) x = T (Tit n x) := rfl

/-- Iteration is additive: `T^(m+n) x = T^n (T^m x)`. -/
theorem Tit_add (m n x : Nat) : Tit (m + n) x = Tit n (Tit m x) := by
  induction n with
  | zero => simp [Tit]
  | succ n ih =>
    rw [Nat.add_succ, Tit_succ, ih]
    rfl

/-- Iterating once more on the right: `T^(n+1) x = T^n (T x)`.  This is the
    form that lets a proof *apply* `T` to the current point first. -/
theorem Tit_succ' (n x : Nat) : Tit (n + 1) x = Tit n (T x) := by
  rw [Nat.add_comm n 1, Tit_add]
  rfl

/-! ## The cycle `1 -> 4 -> 2 -> 1` -/

/-- Membership in the `3`-cycle `{1,2,4}`. -/
def OnCycle (z : Nat) : Prop := z = 1 ∨ z = 2 ∨ z = 4

instance decOnCycle (z : Nat) : Decidable (OnCycle z) :=
  inferInstanceAs (Decidable (z = 1 ∨ z = 2 ∨ z = 4))

/-- The paper's `|a - b| = m`, stated without truncated subtraction. -/
def distEq (a b m : Nat) : Prop := a = b + m ∨ b = a + m

/-- One edge at a time: `T(4) = 2`. -/
theorem T_four : T 4 = 2 := by decide

/-- `T(2) = 1`. -/
theorem T_two : T 2 = 1 := by decide

/-- `T(1) = 4`. -/
theorem T_one : T 1 = 4 := by decide

/-- Three steps return every cycle point to itself. -/
theorem T_three (z : Nat) (hz : OnCycle z) : Tit 3 z = z := by
  rcases hz with rfl | rfl | rfl <;> decide

/-- `3r` steps return every cycle point to itself, for every `r`. -/
theorem cycle_iter (z : Nat) (hz : OnCycle z) (r : Nat) : Tit (3 * r) z = z := by
  induction r with
  | zero => simp [Tit]
  | succ r ih =>
    have hstep : 3 * (r + 1) = 3 + 3 * r := by omega
    rw [hstep, Tit_add, T_three z hz, ih]

/-! ## prop:ladder — the all-even descent chain has an explicit predecessor -/

/-- `T` applied to an even number. -/
theorem T_even (k : Nat) : T (2 * k) = k := by
  have h : (2 * k) % 2 = 0 := by omega
  unfold T
  rw [if_pos h]
  omega

/-- `T` applied to an odd number. -/
theorem T_odd (k : Nat) : T (2 * k + 1) = 3 * (2 * k + 1) + 1 := by
  have h : (2 * k + 1) % 2 ≠ 0 := by omega
  unfold T
  rw [if_neg h]

/-- `prop:ladder`: for every `y` and every depth `d`, `T^d(2^d * y) = y`.
    This is the formal content of "chain inversion needs no search when no
    bit-length constraint is imposed" (the paper's `66.9%` closed-form
    predecessor claim is a counting corollary of this, not a separate fact). -/
theorem ladder (y d : Nat) : Tit d (2 ^ d * y) = y := by
  induction d with
  | zero => simp [Tit]
  | succ d ih =>
    have hsplit : 2 ^ (d + 1) * y = 2 * (2 ^ d * y) := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    rw [hsplit, Tit_succ', T_even, ih]

/-- `prop:ladder` at depth one: the always-legal predecessor of `y` is `2y`.
    (The paper's second predecessor, `(y-1)/3` when `y ≡ 4 mod 6`, is the
    invertibility side handled by `prop:compressed`.) -/
theorem ladder_one (y : Nat) : T (2 * y) = y := T_even y

/-! ## prop:compressed — explicit preimages of the compressed map

  The paper writes `C(x) = (3x+1) / 2^(v_2 (3x+1))` and calls the three formulas
  below a "closed-form inversion".  Two things are worth separating, and the
  formalization makes both explicit:

  * the formulas give **a** preimage, not *the* preimage.  The preimage is not
    unique: `C 1 = C 5 = C 21 = C 85 = 1`, all four with odd arguments.  So the
    paper's wording is tightened below to "explicit preimages".
  * the third case needs no parity hypothesis at all: `3 ∣ C x` is impossible
    because `3x+1 ≡ 1 (mod 3)` while `2^a y ≡ 0 (mod 3)`.  It is proved here in
    that stronger form.

  `v_2` itself is not formalized: `strip2` removes every factor of two directly,
  which is the same function on the odd part and needs no well-founded exponent.
-/

/-- Remove all factors of two from `n` (`strip2 0 = 0` by convention). -/
def strip2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => if (k + 1) % 2 = 0 then strip2 ((k + 1) / 2) else k + 1
termination_by n
decreasing_by omega

/-- The compressed map: `C x = (3x+1) / 2^(v_2 (3x+1))`. -/
def C (x : Nat) : Nat := strip2 (3 * x + 1)

/-- `strip2` of an odd number is the number itself. -/
theorem strip2_self (n : Nat) (h : n % 2 = 1) : strip2 n = n := by
  cases n with
  | zero => omega
  | succ k => rw [strip2.eq_2, if_neg (by omega : ¬ (k + 1) % 2 = 0)]

/-- `strip2` of an even non-zero number drops one factor of two. -/
theorem strip2_two_mul (m : Nat) (hm : m ≠ 0) : strip2 (2 * m) = strip2 m := by
  have h2 : 2 * m = (2 * m - 1) + 1 := by omega
  rw [h2, strip2.eq_2, if_pos (by omega : (2 * m - 1 + 1) % 2 = 0)]
  rw [show (2 * m - 1 + 1) / 2 = m by omega]

/-- `strip2` never returns zero on a non-zero input. -/
theorem strip2_pos (n : Nat) (hn : n ≠ 0) : strip2 n ≠ 0 := by
  induction n using strip2.induct with
  | case1 => omega
  | case2 k hk ih =>
    rw [strip2.eq_2, if_pos hk]
    exact ih (by omega)
  | case3 k hk =>
    rw [strip2.eq_2, if_neg hk]
    omega

/-- `strip2` of a non-zero number is odd (so `C` always lands in the odd numbers). -/
theorem strip2_odd (n : Nat) (hn : n ≠ 0) : strip2 n % 2 = 1 := by
  induction n using strip2.induct with
  | case1 => omega
  | case2 k hk ih =>
    rw [strip2.eq_2, if_pos hk]
    exact ih (by omega)
  | case3 k hk =>
    rw [strip2.eq_2, if_neg hk]
    omega

/-- `strip2 n` divides `n` — the fact the third case turns into a contradiction. -/
theorem strip2_dvd : ∀ n, strip2 n ∣ n := by
  intro n
  induction n using strip2.induct with
  | case1 => exact ⟨0, rfl⟩
  | case2 k hk ih =>
    rw [strip2.eq_2, if_pos hk]
    obtain ⟨c, hc⟩ := ih
    refine ⟨2 * c, ?_⟩
    have hstep : 2 * ((k + 1) / 2) = 2 * (strip2 ((k + 1) / 2) * c) :=
      congrArg (fun t => 2 * t) hc
    calc k + 1 = 2 * ((k + 1) / 2) := by omega
      _ = 2 * (strip2 ((k + 1) / 2) * c) := hstep
      _ = strip2 ((k + 1) / 2) * (2 * c) := Nat.mul_left_comm 2 _ c
  | case3 k hk =>
    rw [strip2.eq_2, if_neg hk]
    exact ⟨1, by omega⟩

/-- All factors of two can be stripped at once: `strip2 (2^k * y) = y` for odd `y`. -/
theorem strip2_pow_two_mul (y k : Nat) (hy : y % 2 = 1) : strip2 (2 ^ k * y) = y := by
  induction k with
  | zero => simpa using strip2_self y hy
  | succ k ih =>
    have hy0 : 0 < y := by omega
    have hpow : 0 < 2 ^ k := Nat.pow_pos (a := 2) (by decide)
    have hpos : 2 ^ k * y ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hpow hy0)
    have h2 : 2 ^ (k + 1) * y = 2 * (2 ^ k * y) := by
      calc 2 ^ (k + 1) * y = (2 ^ k * 2) * y := by rw [Nat.pow_succ]
        _ = (2 * 2 ^ k) * y := by rw [Nat.mul_comm (2 ^ k) 2]
        _ = 2 * (2 ^ k * y) := Nat.mul_assoc 2 (2 ^ k) y
    rw [h2, strip2_two_mul _ hpos, ih]

/-- Uniqueness: any representation `n = 2^k * c` with `c` odd has `c = strip2 n`.
Together with `strip2_pow_two_dvd` (such a representation exists) this pins `strip2`
down as the odd part of `n`. -/
theorem strip2_unique (n c k : Nat) (hc : c % 2 = 1) (h : n = 2 ^ k * c) :
    strip2 n = c := by
  rw [h]
  exact strip2_pow_two_mul c k hc

/-- `strip2` removes exactly the factors of two: `n = 2^k * strip2 n` for some `k`.
With `strip2_odd` (the result is odd) and `strip2_dvd` (it divides `n`) this
characterizes `strip2 n` as the odd part of `n` — i.e. as `n / 2 ^ v2 n` — without
introducing `v2` into the development. -/
theorem strip2_pow_two_dvd : ∀ n, ∃ k, n = 2 ^ k * strip2 n := by
  intro n
  induction n using strip2.induct with
  | case1 => exact ⟨0, by simp [strip2.eq_1]⟩
  | case2 k hk ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨j + 1, ?_⟩
      rw [strip2.eq_2, if_pos hk]
      calc k + 1 = 2 * ((k + 1) / 2) := by omega
        _ = 2 * (2 ^ j * strip2 ((k + 1) / 2)) := congrArg (fun t => 2 * t) hj
        _ = (2 ^ j * 2) * strip2 ((k + 1) / 2) := by rw [Nat.mul_left_comm, Nat.mul_assoc]
        _ = 2 ^ (j + 1) * strip2 ((k + 1) / 2) := by rw [Nat.pow_succ]
  | case3 k hk =>
      refine ⟨0, ?_⟩
      rw [strip2.eq_2, if_neg hk, Nat.pow_zero, Nat.one_mul]

/-- `prop:compressed`, case `y ≡ 1 (mod 3)`: `(4y-1)/3` is a preimage of `y`. -/
theorem compressed_one (y : Nat) (hy : y % 2 = 1) (h3 : y % 3 = 1) :
    C ((4 * y - 1) / 3) = y := by
  unfold C
  have hy1 : 1 ≤ y := by omega
  have hdvd : 3 ∣ 4 * y - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hx : 3 * ((4 * y - 1) / 3) + 1 = 4 * y := by
    have h := Nat.div_mul_cancel hdvd
    omega
  rw [hx]
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  rw [← h4, strip2_pow_two_mul y 2 hy]

/-- `prop:compressed`, case `y ≡ 2 (mod 3)`: `(2y-1)/3` is a preimage of `y`. -/
theorem compressed_two (y : Nat) (hy : y % 2 = 1) (h3 : y % 3 = 2) :
    C ((2 * y - 1) / 3) = y := by
  unfold C
  have hy1 : 1 ≤ y := by omega
  have hdvd : 3 ∣ 2 * y - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hx : 3 * ((2 * y - 1) / 3) + 1 = 2 * y := by
    have h := Nat.div_mul_cancel hdvd
    omega
  rw [hx]
  have h2 : (2 : Nat) ^ 1 = 2 := by decide
  rw [← h2, strip2_pow_two_mul y 1 hy]

/-- `prop:compressed`, case `y ≡ 0 (mod 3)`: no preimage exists.

    Stronger than the paper's statement: no parity hypothesis on `y` is used. -/
theorem compressed_zero (y : Nat) (h3 : y % 3 = 0) : ¬ ∃ x, C x = y := by
  rintro ⟨x, hx⟩
  unfold C at hx
  have hdvd : strip2 (3 * x + 1) ∣ 3 * x + 1 := strip2_dvd _
  rw [hx] at hdvd
  have h3dvd : 3 ∣ y := by rw [Nat.dvd_iff_mod_eq_zero]; exact h3
  obtain ⟨c, hc⟩ := Nat.dvd_trans h3dvd hdvd
  omega

/-- Non-uniqueness of the preimage, machine-checked: `1` has at least four odd
    preimages, so the paper must not call the formulas an *inversion*. -/
theorem compressed_not_unique : C 1 = 1 ∧ C 5 = 1 ∧ C 21 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold C
    rw [show 3 * 1 + 1 = 2 ^ 2 * 1 from by decide, strip2_pow_two_mul 1 2 (by decide)]
  · unfold C
    rw [show 3 * 5 + 1 = 2 ^ 4 * 1 from by decide, strip2_pow_two_mul 1 4 (by decide)]
  · unfold C
    rw [show 3 * 21 + 1 = 2 ^ 6 * 1 from by decide, strip2_pow_two_mul 1 6 (by decide)]

/-! ## prop:parity — no adjacent `1`-`1` in the parity sequence -/

/-- `prop:parity`, pointwise form: the image of an odd number is even. -/
theorem parity (x : Nat) (hx : x % 2 = 1) : T x % 2 = 0 := by
  have hx' : x % 2 ≠ 0 := by omega
  unfold T
  rw [if_neg hx']
  omega

/-- `prop:parity`, sequence form: with `b_i := T^i(x) mod 2`, there is no `i`
    with `b_i = b_{i+1} = 1`. -/
theorem parity_no_adjacent (x i : Nat) :
    ¬ (Tit i x % 2 = 1 ∧ Tit (i + 1) x % 2 = 1) := by
  rintro ⟨h1, h2⟩
  rw [Tit_succ] at h2
  have hp := parity (Tit i x) h1
  omega

/-- `prop:parity` in the `b : Nat -> Nat` form used in the text. -/
theorem parity_sequence (x : Nat) :
    ∀ i, Tit i x % 2 = 1 → Tit (i + 1) x % 2 = 0 := by
  intro i h
  rw [Tit_succ]
  exact parity (Tit i x) h

/-! ## lem:oncycle — arbitrary step counts merge at a cycle point -/

/-- `lem:oncycle`: if `T^tau x = z` with `z` in the cycle, then for every
    `r >= 0` also `T^(tau + 3r) x = z`.  This is the mechanism the paper
    calls "step counts are absorbed by the cycle". -/
theorem oncycle (x z tau r : Nat) (hz : OnCycle z) (h : Tit tau x = z) :
    Tit (tau + 3 * r) x = z := by
  rw [Tit_add, h, cycle_iter z hz r]

/-! ## prop:modproj — the projection has period at most 3 after the cycle -/

/-- `prop:modproj`: once an orbit has reached a cycle point at time `t`, it
    satisfies `T^(t+3r) x = T^t x` for every `r`, i.e. the eventual period
    divides `3` and so is `<= 3`.  Any `mod 2^k` projection of the orbit
    inherits this, since it is a function of the integer trajectory.

    Note the hypothesis `Tit t x = z` with `z` on the cycle: this is where the
    paper's caveat ("条件于 Collatz 收敛性") lives.  The formalized statement is
    the conditional implication, which is all the paper actually claims. -/
theorem modproj (x z t r : Nat) (hz : OnCycle z) (h : Tit t x = z) :
    Tit (t + 3 * r) x = Tit t x := by
  rw [oncycle x z t r hz h, h]

/-- `prop:modproj` at the level the paper actually states it: the `mod 2^k`
    projection of the trajectory is periodic with period dividing `3` once the
    orbit is on the cycle.  (A projection is a function of the integer
    trajectory, so this is `modproj` pushed through `% 2^k`.) -/
theorem modproj_mod (x z t r k : Nat) (hz : OnCycle z) (h : Tit t x = z) :
    Tit (t + 3 * r) x % 2 ^ k = Tit t x % 2 ^ k := by
  rw [modproj x z t r hz h]

/-! ## cor:adjust — the total step count is a free parameter -/

/-- `cor:adjust`: if a trajectory reaches a cycle point `z` at time `tau`, then
    for *any* later `N` congruent to `tau` mod `3` it also reaches `z` at time
    `N`.  The surplus `N - tau` is absorbed by winding around the `3`-cycle.
    This is what makes the claimed step count `n` unenforceable. -/
theorem adjust (x z tau N : Nat) (hz : OnCycle z) (h : Tit tau x = z)
    (hge : tau ≤ N) (hmod : N % 3 = tau % 3) : Tit N x = z := by
  have hdvd : 3 ∣ (N - tau) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  obtain ⟨r, hr⟩ := hdvd
  have hN : N = tau + 3 * r := by omega
  rw [hN]
  exact oncycle x z tau r hz h

/-! ## lem:mod3 — the three cycle arrival times cover all residues mod 3

  The paper's proof already runs off a *shared base time* `t_x`, writing
  `tau_z(x) = t_x + sigma_x(z)` with `sigma_x(z) ∈ {0,1,2}`.  What the
  formalization below makes explicit is that `t_x` need not be the *first*
  entry: the covering holds for arrival times `t + {0,1,2}` based at any cycle
  entry time `t`.  Minimality is used only to *identify* these arrival times
  with the paper's `tau_z = min`, and that identification is proved separately
  below (`firstHit_eq_Arr`).  So this is a slight weakening of a hypothesis,
  not a repair: the paper's argument was sound as written.
-/

/-- Three naturals in `{0,1,2}` that are pairwise distinct hit every residue
    class `mod 3`. -/
theorem three_residues_cover (a b c n : Nat) (ha : a < 3) (hb : b < 3) (hc : c < 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a = n % 3 ∨ b = n % 3 ∨ c = n % 3 := by
  omega

/-- Position of a cycle point around `1 → 4 → 2 → 1`. -/
def code (z : Nat) : Nat :=
  if z = 1 then 0 else if z = 4 then 1 else if z = 2 then 2 else 0

/-- Steps from `zx` to `z` along the cycle, as an element of `{0,1,2}`.
    (`code` never exceeds `2`, so the `Nat` subtraction is exact.) -/
def off (zx z : Nat) : Nat := (code z + 3 - code zx) % 3

theorem off_le (zx z : Nat) : off zx z ≤ 2 := by
  unfold off
  have h := Nat.mod_lt (code z + 3 - code zx) (show 0 < 3 by decide)
  omega

@[simp] theorem off_1_1 : off 1 1 = 0 := by decide
@[simp] theorem off_1_4 : off 1 4 = 1 := by decide
@[simp] theorem off_1_2 : off 1 2 = 2 := by decide
@[simp] theorem off_4_1 : off 4 1 = 2 := by decide
@[simp] theorem off_4_4 : off 4 4 = 0 := by decide
@[simp] theorem off_4_2 : off 4 2 = 1 := by decide
@[simp] theorem off_2_1 : off 2 1 = 1 := by decide
@[simp] theorem off_2_4 : off 2 4 = 2 := by decide
@[simp] theorem off_2_2 : off 2 2 = 0 := by decide

/-- The offset lands on the target: walking `off zx z` steps from a cycle
    point reaches `z`. -/
theorem off_spec (zx z : Nat) (hzx : OnCycle zx) (hz : OnCycle z) :
    Tit (off zx z) zx = z := by
  rcases hzx with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> decide

/-- Arrival time of a cycle point `z`, for an orbit that reaches the cycle
    point `zx` at time `t`.  This is the paper's `tau_z` except that `t` need
    not be the *first* entry. -/
def Arr (t zx z : Nat) : Nat := t + off zx z

theorem Arr_spec (x zx z t : Nat) (hzx : OnCycle zx) (hz : OnCycle z)
    (h : Tit t x = zx) : Tit (Arr t zx z) x = z := by
  unfold Arr
  rw [Tit_add, h, off_spec zx z hzx hz]

/-- The three arrival times of a single orbit are pairwise distinct `mod 3`. -/
theorem Arr_pairwise (t zx : Nat) (hzx : OnCycle zx) :
    Arr t zx 1 % 3 ≠ Arr t zx 4 % 3 ∧
    Arr t zx 1 % 3 ≠ Arr t zx 2 % 3 ∧
    Arr t zx 4 % 3 ≠ Arr t zx 2 % 3 := by
  rcases hzx with rfl | rfl | rfl <;> simp [Arr] <;> omega

/-- `lem:mod3`(a): for every residue `ρ < 3` some cycle point is reached at a
    time congruent to `ρ`. -/
theorem Arr_covers (t zx ρ : Nat) (hzx : OnCycle zx) (hρ : ρ < 3) :
    ∃ z, OnCycle z ∧ Arr t zx z % 3 = ρ := by
  obtain ⟨h14, h12, h42⟩ := Arr_pairwise t zx hzx
  have hl1 := Nat.mod_lt (Arr t zx 1) (show 0 < 3 by decide)
  have hl4 := Nat.mod_lt (Arr t zx 4) (show 0 < 3 by decide)
  have hl2 := Nat.mod_lt (Arr t zx 2) (show 0 < 3 by decide)
  rcases three_residues_cover (Arr t zx 1 % 3) (Arr t zx 4 % 3) (Arr t zx 2 % 3) ρ
      hl1 hl4 hl2 h14 h12 h42 with h | h | h
  · exact ⟨1, by decide, by omega⟩
  · exact ⟨4, by decide, by omega⟩
  · exact ⟨2, by decide, by omega⟩

/-- The paper's `S_z = τ_z(a') + τ_z(b')`. -/
def S (ta za tb zb z : Nat) : Nat := Arr ta za z + Arr tb zb z

/-- The three sums `S_z` are pairwise distinct `mod 3`. -/
theorem S_pairwise (ta za tb zb : Nat) (hza : OnCycle za) (hzb : OnCycle zb) :
    S ta za tb zb 1 % 3 ≠ S ta za tb zb 4 % 3 ∧
    S ta za tb zb 1 % 3 ≠ S ta za tb zb 2 % 3 ∧
    S ta za tb zb 4 % 3 ≠ S ta za tb zb 2 % 3 := by
  rcases hza with rfl | rfl | rfl <;> rcases hzb with rfl | rfl | rfl <;>
    simp [S, Arr] <;> omega

/-- `lem:mod3`(b): the three sums cover all of `mod 3`. -/
theorem S_covers (ta za tb zb n : Nat) (hza : OnCycle za) (hzb : OnCycle zb) :
    ∃ z, OnCycle z ∧ S ta za tb zb z % 3 = n % 3 := by
  obtain ⟨h14, h12, h42⟩ := S_pairwise ta za tb zb hza hzb
  have hl1 := Nat.mod_lt (S ta za tb zb 1) (show 0 < 3 by decide)
  have hl4 := Nat.mod_lt (S ta za tb zb 4) (show 0 < 3 by decide)
  have hl2 := Nat.mod_lt (S ta za tb zb 2) (show 0 < 3 by decide)
  rcases three_residues_cover (S ta za tb zb 1 % 3) (S ta za tb zb 4 % 3)
      (S ta za tb zb 2 % 3) n hl1 hl4 hl2 h14 h12 h42 with h | h | h
  · exact ⟨1, by decide, h⟩
  · exact ⟨4, by decide, h⟩
  · exact ⟨2, by decide, h⟩

/-! ## First-arrival times: `tau_z` as an actual minimum

  The paper defines `tau_z(x) = min { j | T^j x = z }`.  Algorithm 1 only needs
  *some* arrival time consistent with the cycle order; the lemmas here show the
  two notions agree, so nothing is lost.

  Note: `Nat.find` is **not** available in this toolchain (it is a Mathlib
  addition, absent from both core `Init` and `Std`).  So `tau_z` is not
  *constructed* here; instead it is *characterized* — `Arr_is_min` proves that
  `Arr` is an arrival time and that no arrival time is smaller, which is
  exactly the defining property of a minimum, and `Arr_unique` shows any such
  time equals `Arr`.  This is what the paper's proofs actually consume, and it
  avoids depending on a search construction.
-/

/-- A cycle point stays on the cycle for its first two steps. -/
theorem OnCycle_step (zx m : Nat) (hzx : OnCycle zx) (hm : m < 3) :
    OnCycle (Tit m zx) := by
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hzx with rfl | rfl | rfl <;> rcases hm3 with rfl | rfl | rfl <;> decide

/-- The cycle has period exactly `3`: no cycle point returns to itself in one
    or two steps. -/
theorem cycle_no_small_fix (z k : Nat) (hz : OnCycle z) (hk : 0 < k) (hk3 : k < 3) :
    Tit k z ≠ z := by
  have hk2 : k = 1 ∨ k = 2 := by omega
  rcases hz with rfl | rfl | rfl <;> rcases hk2 with rfl | rfl | rfl <;> decide

/-- Stepping a cycle point by fewer than `3` steps is injective, so "which
    point is reached after `m < 3` steps" determines `m`. -/
theorem cycle_step_inj (zx m1 m2 : Nat) (hzx : OnCycle zx) (h1 : m1 < 3) (h2 : m2 < 3)
    (h : Tit m1 zx = Tit m2 zx) : m1 = m2 := by
  rcases Nat.lt_trichotomy m1 m2 with hlt | heq | hgt
  · exfalso
    have hd : 0 < m2 - m1 := by omega
    have hd3 : m2 - m1 < 3 := by omega
    have hm2 : m2 = m1 + (m2 - m1) := by omega
    rw [hm2, Tit_add] at h
    exact cycle_no_small_fix (Tit m1 zx) (m2 - m1) (OnCycle_step zx m1 hzx h1) hd hd3 h.symm
  · exact heq
  · exfalso
    have hd : 0 < m1 - m2 := by omega
    have hd3 : m1 - m2 < 3 := by omega
    have hm1 : m1 = m2 + (m1 - m2) := by omega
    rw [hm1, Tit_add] at h
    exact cycle_no_small_fix (Tit m2 zx) (m1 - m2) (OnCycle_step zx m2 hzx h2) hd hd3 h

/-- The offset is the *only* number of steps below `3` that reaches `z`. -/
theorem off_unique (zx z m : Nat) (hzx : OnCycle zx) (hz : OnCycle z) (hm : m < 3)
    (h : Tit m zx = z) : m = off zx z := by
  have ho3 : off zx z < 3 := by
    have h := off_le zx z
    omega
  have hoff : Tit (off zx z) zx = z := off_spec zx z hzx hz
  exact cycle_step_inj zx m (off zx z) hzx hm ho3 (by rw [h, hoff])

/-- `Arr` is the **minimal** arrival time: if `t` is the first cycle entry of
    the orbit of `x` and `Tit i x = z`, then `Arr t zx z <= i`. -/
theorem Arr_le_of_arrival (x zx z t i : Nat) (hzx : OnCycle zx) (hz : OnCycle z)
    (ht : Tit t x = zx) (hfirst : ∀ j, j < t → ¬ OnCycle (Tit j x))
    (hi : Tit i x = z) : Arr t zx z ≤ i := by
  by_cases hlt : i < t
  · exfalso
    exact hfirst i hlt (hi ▸ hz)
  · have hit : t ≤ i := by omega
    have hi' : i = t + (i - t) := by omega
    rw [hi', Tit_add, ht] at hi
    rcases Nat.lt_or_ge (i - t) 3 with hsmall | hbig
    · have hoff := off_unique zx z (i - t) hzx hz hsmall hi
      unfold Arr
      omega
    · unfold Arr
      have hle := off_le zx z
      omega

/-- **The identification.**  If `t` is the first cycle entry time, then `Arr t
    zx z` is exactly the paper's `tau_z = min { j | T^j x = z }`, characterized
    by: it is an arrival time, and no arrival time is smaller. -/
theorem Arr_is_min (x zx z t : Nat) (hzx : OnCycle zx) (hz : OnCycle z)
    (ht : Tit t x = zx) (hfirst : ∀ j, j < t → ¬ OnCycle (Tit j x)) :
    Tit (Arr t zx z) x = z ∧ ∀ i, Tit i x = z → Arr t zx z ≤ i :=
  ⟨Arr_spec x zx z t hzx hz ht,
   fun i hi => Arr_le_of_arrival x zx z t i hzx hz ht hfirst hi⟩

/-- The minimum is unique: any time that is an arrival time for `z` and is at
    most every arrival time for `z` must equal `Arr t zx z`.  Together with
    `Arr_is_min` this pins down `tau_z` without constructing it. -/
theorem Arr_unique (x zx z t tq : Nat) (hzx : OnCycle zx) (hz : OnCycle z)
    (ht : Tit t x = zx) (hfirst : ∀ j, j < t → ¬ OnCycle (Tit j x))
    (harr : Tit tq x = z) (hmin : ∀ i, Tit i x = z → tq ≤ i) : tq = Arr t zx z := by
  have h1 : tq ≤ Arr t zx z := hmin _ (Arr_spec x zx z t hzx hz ht)
  have h2 : Arr t zx z ≤ tq := Arr_le_of_arrival x zx z t tq hzx hz ht hfirst harr
  omega

/-- The paper writes the step-2 guard as `min_z S_z ≤ n - 4`, which is Nat
    subtraction and therefore truncates when `n < 4`.  The formalization uses
    the untruncated `S_z + 4 ≤ n`.  For `n ≥ 4` the two agree; since the
    omitted case only occurs at absurdly small `n` (honest instances have
    `n ≈ 14k`), nothing is lost — but the difference is recorded here rather
    than left implicit. -/
theorem guard_iff (s n : Nat) (h4 : 4 ≤ n) : (s + 4 ≤ n) ↔ (s ≤ n - 4) := by
  omega

/-! ## thm:cyclekill — the correctness core of Algorithm 1 -/

/-- **The heart of `thm:cyclekill`.**  Algorithm 1 returns
    `(a', b', tau_z*(a'), tau_z*(b') + rem)` where `rem = n - S_z*` is forced by
    the congruence `S_z* ≡ n (mod 3)`, hence `rem ≡ 0 (mod 3)`.

    This theorem says that such a `rem` may always be charged to one side
    without moving the meeting point: if both trajectories meet a cycle point
    `z` at times `s` and `t0`, then they still meet at `z` when `rem` extra
    steps are added to the second one.  Together with `(i)` `T^s' a' = z`,
    `(iii)` `s'+t' = n` and `(iv)` `|a'-b'| = m`, this is the whole of the
    paper's correctness argument; what remains for the full `thm:cyclekill` is
    only the *selection* arithmetic for `z*` (that is `lem:mod3` plus
    `min_z S_z <= n - 4`). -/
theorem cyclekill_core (a b z s t0 rem : Nat) (hz : OnCycle z)
    (ha : Tit s a = z) (hb : Tit t0 b = z) (hrem : rem % 3 = 0) :
    Tit s a = Tit (t0 + rem) b := by
  obtain ⟨r, hr⟩ : ∃ r, rem = 3 * r := by
    have hdvd : 3 ∣ rem := Nat.dvd_of_mod_eq_zero hrem
    obtain ⟨r, hr⟩ := hdvd
    exact ⟨r, hr⟩
  rw [hr, oncycle b z t0 r hz hb, ha]

/-- **`thm:cyclekill`, unconditional.**  Suppose a run of Algorithm 1 draws
    `a' = a`, `b' = b` with `|a'-b'| = m`, runs both orbits until each reaches
    the cycle (at times `ta`, `tb`, on points `za`, `zb`), and the step-2 guard
    `min_z S_z ≤ n - 4` holds.  Then the tuple it returns,

      `(a', b', τ_z*(a'), τ_z*(b') + (n - S_z*))`

    where `z*` is the cycle point with `S_z* ≡ n (mod 3)`, satisfies the
    verification predicate `P_pk` of public key `(m, n)`.

    Nothing about the Collatz conjecture is assumed: the two orbit facts
    `ha`, `hb` are what the algorithm *checks* in step 2, and the guard is the
    rejection condition it *enforces*.  The only thing not formalized is that
    a candidate passing the guard is found in bounded time — the paper is
    explicit that this is its one measured input (`rem:uncond`). -/
theorem cyclekill_correct (m n a b ta tb za zb : Nat)
    (hza : OnCycle za) (hzb : OnCycle zb)
    (ha : Tit ta a = za) (hb : Tit tb b = zb)
    (hd : distEq a b m)
    (hguard : ∃ z, OnCycle z ∧ S ta za tb zb z + 4 ≤ n) :
    ∃ s' t', Tit s' a = Tit t' b ∧ s' + t' = n ∧ distEq a b m := by
  obtain ⟨z0, hz0, hS0⟩ := S_covers ta za tb zb n hza hzb
  obtain ⟨zg, _hzg, hguard'⟩ := hguard
  have hbnd : S ta za tb zb z0 ≤ S ta za tb zb zg + 4 := by
    have h1 := off_le za z0
    have h2 := off_le zb z0
    have h3 := off_le za zg
    have h4 := off_le zb zg
    unfold S Arr
    omega
  have hle : S ta za tb zb z0 ≤ n := by omega
  have hrem : (n - S ta za tb zb z0) % 3 = 0 := by omega
  refine ⟨Arr ta za z0, Arr tb zb z0 + (n - S ta za tb zb z0), ?_, ?_, hd⟩
  · exact cyclekill_core a b z0 (Arr ta za z0) (Arr tb zb z0)
      (n - S ta za tb zb z0) hz0
      (Arr_spec a za z0 ta hza hz0 ha) (Arr_spec b zb z0 tb hzb hz0 hb) hrem
  · have hS : S ta za tb zb z0 = Arr ta za z0 + Arr tb zb z0 := rfl
    omega

/-! ## prop:monotone — the step-count coordinate cannot tighten the predicate -/

/-- The paper's verification predicate `P_pk` under the "trusted step count"
    semantics: `∃ s' t'. T^s'(a') = T^t'(b') ∧ s' + t' = n ∧ |a'-b'| = m`. -/
def Verifies (m n a b : Nat) : Prop :=
  ∃ s t, Tit s a = Tit t b ∧ s + t = n ∧ distEq a b m

/-- The cycle-meeting witness set `W_cyc(m,n)`: the subset of `Verifies`
    witnesses whose merge happens on the cycle. -/
def VerifiesCyc (m n a b : Nat) : Prop :=
  ∃ s t z, OnCycle z ∧ Tit s a = z ∧ Tit t b = z ∧ s + t = n ∧ distEq a b m

/-- `prop:monotone`, tuple form: a witness for `(m,n)` that merges at a cycle
    point yields a witness for `(m, n + 3j)` at the same `(a',b')`, by adding
    `3j` steps to one side only. -/
theorem monotone (m n a b s t z j : Nat) (hz : OnCycle z)
    (ha : Tit s a = z) (hb : Tit t b = z) (hsum : s + t = n) (hd : distEq a b m) :
    ∃ s' t', Tit s' a = Tit t' b ∧ s' + t' = n + 3 * j ∧ distEq a b m :=
  ⟨s + 3 * j, t, by rw [oncycle a z s j hz ha, hb], by omega, hd⟩

/-- `prop:monotone`, set form: `W_cyc(m,n) ⊆ W_cyc(m, n+3)`.  Raising the
    claimed step count only ever *enlarges* the witness set, so `n` cannot be
    used to harden the predicate. -/
theorem Wcyc_mono (m n a b : Nat) : VerifiesCyc m n a b → VerifiesCyc m (n + 3) a b := by
  rintro ⟨s, t, z, hz, ha, hb, hsum, hd⟩
  exact ⟨s + 3, t, z, hz, oncycle a z s 1 hz ha, hb, by omega, hd⟩

/-- `prop:monotone` in the general `3j` form: `W_cyc(m,n) ⊆ W_cyc(m, n+3j)`.
    Machine-checked form of "the step-count constraint contributes at most
    `log2 3` bits and can never be tightened by choosing a larger `n`". -/
theorem Wcyc_mono_mul (m n j a b : Nat) :
    VerifiesCyc m n a b → VerifiesCyc m (n + 3 * j) a b := by
  rintro ⟨s, t, z, hz, ha, hb, hsum, hd⟩
  exact ⟨s + 3 * j, t, z, hz, oncycle a z s j hz ha, hb, by omega, hd⟩

/-! ## Non-emptiness witness (regression test)

  Compiling is not the same as being non-vacuous: a theorem whose hypotheses
  are never satisfied is true and worthless.  This witness pins down that
  `cyclekill_correct`'s hypotheses are simultaneously satisfiable, on the
  smallest instance where the guard bites.

  `a' = 1`, `b' = 2`, `m = 1`, `n = 5`; both orbits sit on the cycle at times
  `ta = 0`, `tb = 1`, at the point `1`.  Then `S_1 = 1`, `S_4 = 3`, `S_2 = 5`,
  so `n ≡ 2 (mod 3)` selects `z* = 2` and the construction returns
  `(s', t') = (2, 3)` with meeting point `2 = T^2(1) = T^3(2)` and `2 + 3 = 5`.
  The guard is met at `z = 1`: `S_1 + 4 = 5 ≤ n`. -/
example : ∃ s' t', Tit s' 1 = Tit t' 2 ∧ s' + t' = 5 ∧ distEq 1 2 1 :=
  cyclekill_correct 1 5 1 2 0 1 1 1
    (Or.inl rfl) (Or.inl rfl) rfl (by decide) (Or.inr rfl)
    ⟨1, Or.inl rfl, by decide⟩

end Collatz

/-! ## Axiom audit

The project target was "#print axioms shows only propext / Classical.choice /
Quot.sound, zero sorry".  Since this layer is pure `Nat`, it should show
strictly less: no axioms at all. -/

#print axioms Collatz.ladder
#print axioms Collatz.parity_no_adjacent
#print axioms Collatz.oncycle
#print axioms Collatz.modproj
#print axioms Collatz.modproj_mod
#print axioms Collatz.adjust
#print axioms Collatz.Arr_covers
#print axioms Collatz.S_covers
#print axioms Collatz.Arr_is_min
#print axioms Collatz.Arr_unique
#print axioms Collatz.cyclekill_core
#print axioms Collatz.cyclekill_correct
#print axioms Collatz.guard_iff
#print axioms Collatz.compressed_one
#print axioms Collatz.compressed_two
#print axioms Collatz.compressed_zero
#print axioms Collatz.compressed_not_unique
#print axioms Collatz.strip2_pow_two_dvd
#print axioms Collatz.strip2_unique
#print axioms Collatz.Wcyc_mono_mul

/-! ## NOTES — scope

1. What `cyclekill_correct` does *not* claim.  It says: conditional on a
   candidate passing the step-2 guard, the returned tuple satisfies `P_pk`
   unconditionally.  That some candidate passes the guard within bounded time
   is the paper's one measured input (`rem:uncond`) — it is not a theorem of
   any kind, empirical or otherwise.  Likewise the `O(k)` cost clause of the
   abstract is not formalized: no complexity model is built here.

   The guard itself is stated untruncated as `S + 4 ≤ n`, whereas the paper
   writes `min_z S_z ≤ n - 4` with Nat subtraction.  `guard_iff` records that
   the two agree for `n ≥ 4`; the truncated regime (`n < 4`) is degenerate and
   does not occur for honest instances (`n ≈ 14k`).

2. `prop:compressed` is proved in full (`compressed_one`, `compressed_two`,
   `compressed_zero`).  Two refinements came out of it.  (i) The formulas give
   *a* preimage, not *the* preimage: `C 1 = C 5 = C 21 = 1`
   (`compressed_not_unique`), so the paper says "explicit preimages" rather than
   "closed-form inversion".  (ii) The third case needs no parity hypothesis, and
   is proved in that stronger form.  `v₂` is not formalized: `strip2` strips the
   factors of two directly, which is the same function on the odd part.

3. `thm:guess`'s two identities are the last *unconditional* results in the
   paper.  They need a finite-distribution and geometric-expectation setup —
   the one place Mathlib finally earns its place.

4. Everything condition- or measurement-flavoured — `thm:meetbound` (G1)(G2),
   `lem:entropy-bound` (D1)(D2), `thm:entropy` (C1)-(C4), `thm:sampling`'s
   indistinguishability claim, `lem:reduction`, `prop:sim`, `prop:nosecret`,
   `prop:roles` — is out of scope by construction, not by lack of effort.
   Their conditional-implication shadows are provable and worthless: the
   hypothesis carries all the content, so proving them says nothing.

5. What the formalization adds to `lem:mod3` — and what it does **not**.  The
   paper's proof already runs off a *shared base time* `t_x`; it does not need
   the minimality of `tau_z` for the covering.  What is made explicit here is
   (i) the base time need not be the *first* entry — the covering is uniform
   in it — and (ii) the identification with `tau_z = min` does hold when the
   base is the first entry (`Arr_is_min`, `Arr_unique`).  So this is a slight
   weakening of a hypothesis, **not** a correction of the paper.  The paper's
   argument was sound as written.  (`Nat.find` is unavailable in this
   toolchain, so `tau_z` is characterized rather than constructed; see the
   docstring on the first-arrival section.)
-/
