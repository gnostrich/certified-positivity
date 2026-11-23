module

public import Mathlib

@[expose] public section

/-!
# ChallengeThresholds.lean — certified horizon thresholds (Mathlib-only statements)

States, with `sorry` as every proof, seven theorems of the Certified Positivity
development about the truncated Weil-type Toeplitz forms at the true prime
atoms `a_p = (log p)/√p`. For windows of size 3, 4 and 5 (primes up to 3, 5
and 7 respectively; entry at distance `k` is the `k`-th prime atom and the
diagonal is `κ`), the form is certified positive definite at one value of `κ`
and certified not positive definite at a slightly smaller one. Since raising
`κ` adds a multiple of the identity, the form is positive definite exactly for
`κ > κ*`, so each pair brackets the threshold `κ*`:

* 3 × 3 (p = 2, 3):       `0.6   ≤ κ* < 0.635`
* 4 × 4 (p = 2, 3, 5):    `0.789 ≤ κ* < 0.790`
* 5 × 5 (p = 2, 3, 5, 7): `0.919 ≤ κ* < 0.921`

The seventh theorem (joint binding) shows `log p/√p < 0.919` for every prime
`p`: the window-4 threshold exceeds every individual atom, so it is produced
by the atoms jointly and not by any single prime.

The file imports **only Mathlib** and inlines every definition it needs,
copied verbatim from the named repository files; the one systematic change is
that all of them live in the single namespace `ChallengeThresholds`. The
sorry-free proofs are in `RequestProject/` (`E5.lean`, `G3.lean`, `G6.lean`),
on `propext`, `Classical.choice` and `Quot.sound` only, without
`native_decide`. This file makes no axiom claim of its own.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`. This file elaborates
with exactly the 7 expected `declaration uses 'sorry'` warnings.
-/

open scoped BigOperators Matrix

namespace ChallengeThresholds

/-! ## Definitions — from `RequestProject/Horizon.lean` (namespace `Horizon`) -/

variable {n : ℕ}

/-- The quadratic form `xᵀ M x`. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `M` is positive definite (quadratic-form definition). -/
def IsPDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x

/-! ## Definitions — from `RequestProject/E5.lean`, `RequestProject/G3.lean`,
`RequestProject/G6.lean` (namespaces `E5`, `G3`, `G6`) -/

/-- The second-window `3 × 3` form. -/
def V (κ u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![κ, u, v; u, κ, u; v, u, κ]

/-- The third-window `4 × 4` form. -/
def U (κ u v w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![κ, u, v, w; u, κ, u, v; v, u, κ, u; w, v, u, κ]

/-- The window-4 `5 × 5` symmetric Toeplitz form. -/
def U5 (κ u v w x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![κ, u, v, w, x; u, κ, u, v, w; v, u, κ, u, v; w, v, u, κ, u; x, w, v, u, κ]

/-! ## Theorems, stated with `sorry` -/

/-- From `RequestProject/E5.lean` (`E5.E5_cert_pos`). The 3 × 3 form with the true atoms `log 2/√2`, `log 3/√3` is positive
definite at diagonal `0.635`. -/
theorem E5_cert_pos :
    IsPDq (V 0.635 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)) := by sorry

/-- From `RequestProject/E5.lean` (`E5.E5_cert_neg`). … and is not positive definite at diagonal `0.6`. -/
theorem E5_cert_neg :
    ¬ IsPDq (V 0.6 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)) := by sorry

/-- From `RequestProject/G3.lean` (`G3.G3_cert_pos`). The 4 × 4 form with the true atoms for `p = 2, 3, 5` is positive definite
at diagonal `0.790`. -/
theorem G3_cert_pos :
    IsPDq (U 0.790 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) := by sorry

/-- From `RequestProject/G3.lean` (`G3.G3_cert_neg`). … and is not positive definite at diagonal `0.789`. -/
theorem G3_cert_neg :
    ¬ IsPDq (U 0.789 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) := by sorry

/-- From `RequestProject/G6.lean` (`G6.G6_cert_pos`). The 5 × 5 form with the true atoms for `p = 2, 3, 5, 7` is positive
definite at diagonal `0.921`. -/
theorem G6_cert_pos :
    IsPDq (U5 0.921 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5) (Real.log 7 / Real.sqrt 7)) := by sorry

/-- From `RequestProject/G6.lean` (`G6.G6_cert_neg`). … and is not positive definite at diagonal `0.919`. -/
theorem G6_cert_neg :
    ¬ IsPDq (U5 0.919 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5) (Real.log 7 / Real.sqrt 7)) := by sorry

/-- From `RequestProject/G6.lean` (`G6.G6_c`). Joint binding: the window-4 failure value `0.919` exceeds the atom
`log p/√p` of every prime `p`, so no single prime's atom accounts for it. -/
theorem G6_c (p : ℕ) (hp : p.Prime) : Real.log p / Real.sqrt p < 0.919 := by sorry

end ChallengeThresholds
