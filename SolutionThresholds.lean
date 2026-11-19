module

public import Mathlib
public import RequestProject.E5
public import RequestProject.G3
public import RequestProject.G6

@[expose] public section

/-!
# SolutionThresholds.lean — comparator bridge for `ChallengeThresholds.lean`

The identical definitions and theorem statements, with each `sorry` replaced
by a term-level appeal to the named repository theorem. No new mathematics is
introduced.
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

/-! ## Theorems, proved by bridging to the repository modules -/

theorem E5_cert_pos :
    IsPDq (V 0.635 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)) :=
  E5.E5_cert_pos

theorem E5_cert_neg :
    ¬ IsPDq (V 0.6 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)) :=
  E5.E5_cert_neg

theorem G3_cert_pos :
    IsPDq (U 0.790 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) :=
  G3.G3_cert_pos

theorem G3_cert_neg :
    ¬ IsPDq (U 0.789 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) :=
  G3.G3_cert_neg

theorem G6_cert_pos :
    IsPDq (U5 0.921 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5) (Real.log 7 / Real.sqrt 7)) :=
  G6.G6_cert_pos

theorem G6_cert_neg :
    ¬ IsPDq (U5 0.919 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5) (Real.log 7 / Real.sqrt 7)) :=
  G6.G6_cert_neg

theorem G6_c (p : ℕ) (hp : p.Prime) : Real.log p / Real.sqrt p < 0.919 :=
  G6.G6_c p hp

end ChallengeThresholds
