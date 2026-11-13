/-
  Guessing-cost identities: the algebraic layer of the paper's `thm:guess`.

  Companion to `collatz_lean0/lean/Collatz.lean` (which is dependency-free and
  covers §2.4 + obstacle one).  This file needs Mathlib for `ℚ` and `Finset`,
  because the statements are about finite sums and reciprocals.

  What the paper claims (after correction):

      min_x E[N(x)] = 1 / max_x p(x) = 2^{H_inf}(D)
      max_x E[N(x)] = 1 / min_x p(x)
      E_{x~D} E[N(x)] = U

  The paper's *original* first identity was

      max_x E[N(x)] = 1 / max_x p(x)          -- FALSE

  with counterexample p = (9/10, 1/10): the two sides are 10 and 10/9.
  `1/p` is antitone in `p`, so the maximum of `1/p` sits at the *minimum* of `p`.
  Proving the original form is impossible; the failure is the artifact.

  Scope: only the algebra of `1/p` is formalized.  That `N(x)` is geometric with
  mean `1/p(x)` (an infinite series) is NOT formalized: the paper only ever uses
  the resulting identities, never the derivation of the expectation.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Bounds.Basic

open Finset

namespace Guess

variable {n : ℕ} (p : Fin n → ℚ)

/-- The mode minimizes the cost: `1/max p` is the least value of `1/p`,
    i.e. `2^{H_inf}(D)` is the expected cost of the most probable instance
    and a lower bound for all others. -/
theorem cost_isLeast (hp : ∀ i, 0 < p i) (i₀ : Fin n) (hmax : ∀ i, p i ≤ p i₀) :
    IsLeast (Set.range fun i => 1 / p i) (1 / p i₀) := by
  constructor
  · exact ⟨i₀, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact one_div_le_one_div_of_le (hp i) (hmax i)

/-- The least probable instance is the most expensive one: `1/min p` is the
    greatest value of `1/p`. -/
theorem cost_isGreatest (hp : ∀ i, 0 < p i) (i₁ : Fin n) (hmin : ∀ i, p i₁ ≤ p i) :
    IsGreatest (Set.range fun i => 1 / p i) (1 / p i₁) := by
  constructor
  · exact ⟨i₁, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact one_div_le_one_div_of_le (hp i₁) (hmin i)

/-- The average cost over instances drawn from `D` is the support size `U = n`.
    (Every point of `Fin n` is in the support, since `p` is strictly positive.) -/
theorem cost_avg (hp : ∀ i, 0 < p i) (_h1 : ∑ i, p i = 1) : ∑ i, p i * (1 / p i) = n := by
  have h : ∀ i, p i * (1 / p i) = 1 := fun i => mul_one_div_cancel (ne_of_gt (hp i))
  calc ∑ i, p i * (1 / p i) = ∑ _i : Fin n, (1 : ℚ) := sum_congr rfl fun i _ => h i
    _ = n := by simp

end Guess

#print axioms Guess.cost_isLeast
#print axioms Guess.cost_isGreatest
#print axioms Guess.cost_avg
