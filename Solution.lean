module

public import Mathlib
public import RequestProject.V5_5
public import RequestProject.V5_6

@[expose] public section

/-!
# Solution.lean — comparator bridge

Comparator counterpart of `Challenge.lean`: the identical definitions and
theorem statements (same `Challenge` namespace, same source text), with each
`sorry` replaced by a proof that defers to the corresponding repository
theorem. Comparator verifies that every statement here is byte-identical to
`Challenge.lean`'s and that the proofs stay within the permitted axioms
(`comparator.json`).

Bridge policy: every proof is a term-level appeal to the named repository
theorem. No new mathematics is introduced.
-/

open scoped BigOperators Matrix
open ArithmeticFunction

namespace Challenge

/-! ## Definitions — from `RequestProject/Horizon.lean` (namespace `Horizon`) -/

variable {n : ℕ}

/-- The quadratic form `xᵀ M x`. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `M` is positive definite (quadratic-form definition). -/
def IsPDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x

/-! ## Definitions — from `RequestProject/V5_1.lean` (namespace `V5_1`) -/

/-- The Hurwitz value `ζ(2,1/4)` in the normalization used by Suzuki. -/
noncomputable def C : ℝ := ∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2)

/-- The Hurwitz--Lerch series in the archimedean screw term. -/
noncomputable def L (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-2 * n * t) * (1 / ((n : ℝ) + 1 / 4) ^ 2)

/-- The constant `Γ'/Γ(1/4)`. -/
noncomputable def A : ℝ :=
  -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2

/-- Suzuki's archimedean screw component. -/
noncomputable def PsiArch (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    (t / 2) * (A - Real.log Real.pi) +
    (1 / 4) * (C - Real.exp (-t / 2) * L t)

/-- The finite prime-power contribution at nonnegative `t`. -/
noncomputable def primeSum (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
    (Λ n / Real.sqrt n) * (t - Real.log n)

/-- The nonnegative-half screw function. -/
noncomputable def PsiNonneg (t : ℝ) : ℝ := PsiArch t - primeSum t

/-- The full screw function, extended evenly. -/
noncomputable def Psi (t : ℝ) : ℝ := PsiNonneg |t|

/-- Krein's Gram kernel. -/
noncomputable def G (t u : ℝ) : ℝ := Psi t + Psi u - Psi (t - u)

/-! ## Definitions — from `RequestProject/V5_5.lean` / `RequestProject/V5_6.lean`
(namespaces `V5_5`, `V5_6`) -/

/-- The genuine screw Gram matrix on the grid `(0.2,0.4,0.6)`. -/
noncomputable def M3 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  let t : Fin 3 → ℝ := ![0.2, 0.4, 0.6]
  G (t i) (t j)

noncomputable def M2 : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  let t : Fin 2 → ℝ := ![0.4, 0.9]
  G (t i) (t j)

/-! ## Headline theorems, proved by bridging to the repository modules. -/

theorem true_kernel_grid_margin (x : Fin 3 → ℝ) :
    (0.005 : ℝ) * ∑ i, x i ^ 2 ≤ quadForm M3 x :=
  V5_5.true_kernel_grid_margin x

theorem true_kernel_grid_posdef : IsPDq M3 :=
  V5_5.true_kernel_grid_posdef

theorem true_kernel_first_prime_posdef : IsPDq M2 :=
  V5_6.true_kernel_first_prime_posdef

end Challenge
