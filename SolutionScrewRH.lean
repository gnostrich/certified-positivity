module

public import Mathlib
public import RequestProject.ScrewRH.ExplicitFormula
public import RequestProject.ScrewRH.MainRH

@[expose] public section

/-!
# SolutionScrewRH.lean — comparator bridge for `ChallengeScrewRH.lean`

The identical definitions and theorem statements, with each `sorry` replaced
by a term-level appeal to the named repository theorem. No new mathematics is
introduced.
-/

open scoped BigOperators Matrix
open ArithmeticFunction

namespace ChallengeScrewRH

/-! ## Definitions — from `RequestProject/Horizon.lean` (namespace `Horizon`) -/

variable {n : ℕ}

/-- The quadratic form `xᵀ M x`. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `M` is positive semidefinite (quadratic-form definition). -/
def IsPSDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ quadForm M x

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

/-! ## Definitions — from `RequestProject/ScrewRH/Defs.lean` and
`RequestProject/ScrewRH/SummableZeros.lean` (namespace `ScrewRH`) -/

/-- The nontrivial zeros of `ζ`. -/
def Z : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Multiplicity of a zero of `ζ`. -/
noncomputable def mult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- The summand of the zero sum. -/
noncomputable def zeroTerm (t : ℝ) (ρ : ℂ) : ℂ :=
  (mult ρ : ℂ) * (Complex.exp ((ρ - 1 / 2) * t) - 1) / (ρ - 1 / 2) ^ 2

/-! ## Theorems, proved by bridging to the repository modules -/

theorem Psi_eq_tsum_zeros (t : ℝ) (ht : 0 ≤ t) :
    ((Psi t : ℝ) : ℂ) = ∑' ρ : Z, zeroTerm t ρ :=
  ScrewRH.Psi_eq_tsum_zeros t ht

theorem screw_gram_psd_of_RH (hRH : RiemannHypothesis) (N : ℕ) (t : Fin N → ℝ) :
    IsPSDq (Matrix.of fun i j : Fin N => G (t i) (t j)) :=
  ScrewRH.screw_gram_psd_of_RH hRH N t

end ChallengeScrewRH
