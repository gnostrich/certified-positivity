module

public import Mathlib

@[expose] public section

/-!
# ChallengeScrewRH.lean — the screw function's explicit formula and RH ⇒ Gram positivity
(Mathlib-only statements)

States, with `sorry` as every proof, two theorems of the Certified Positivity
development about Suzuki's screw function `Psi` of the Riemann zeta function
(the same `Psi` and Krein Gram kernel `G t u = Psi t + Psi u - Psi (t - u)` as
in the registered entry's `Challenge.lean`, both copied from
`RequestProject/V5_1.lean`):

* `Psi_eq_tsum_zeros` (unconditional): for every `t ≥ 0`,
  `Psi t = ∑' ρ, m(ρ) (exp ((ρ - ½) t) - 1) / (ρ - ½)²`, the sum running over
  the nontrivial zeros `ρ` of `riemannZeta` (zeros in the open critical strip)
  with `m(ρ)` the analytic order of `riemannZeta` at `ρ`; the sum is an
  unconditional `tsum` over the subtype of zeros (Suzuki, arXiv:2206.03682,
  eq. (1.3)).
* `screw_gram_psd_of_RH` (conditional): assuming Mathlib's
  `RiemannHypothesis`, for every `N` and every grid `t : Fin N → ℝ` the Gram
  matrix `(G (t i) (t j))` is positive semidefinite in the quadratic-form
  sense (the direction RH ⇒ positivity of Suzuki's Theorem 1.2, on finite
  grids).

`RiemannHypothesis` here is Mathlib's own definition, used as a hypothesis;
nothing is assumed or claimed about its truth. Combining the second theorem
with any Lean proof of `RiemannHypothesis` (for example Alpöge's) yields the
unconditional statement that the Gram matrix of `G` is positive semidefinite
on every finite grid.

The file imports **only Mathlib** and inlines every definition it needs,
copied verbatim from the named repository files; the one systematic change is
that all of them live in the single namespace `ChallengeScrewRH`. The
sorry-free proofs are in `RequestProject/ScrewRH/` (`ExplicitFormula.lean`,
`MainRH.lean`). This file makes no axiom claim of its own.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`. This file elaborates
with exactly the 2 expected `declaration uses 'sorry'` warnings.
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

/-! ## Theorems, stated with `sorry` -/

/-- From `RequestProject/ScrewRH/ExplicitFormula.lean` (`ScrewRH.Psi_eq_tsum_zeros`).
Unconditional explicit formula: for `t ≥ 0` the screw function is the sum over the nontrivial
zeros of `ζ`, counted with multiplicity, of `(exp ((ρ - ½) t) - 1) / (ρ - ½)²`. -/
theorem Psi_eq_tsum_zeros (t : ℝ) (ht : 0 ≤ t) :
    ((Psi t : ℝ) : ℂ) = ∑' ρ : Z, zeroTerm t ρ := by sorry

/-- From `RequestProject/ScrewRH/MainRH.lean` (`ScrewRH.screw_gram_psd_of_RH`).
Under Mathlib's `RiemannHypothesis`, Krein's Gram kernel of the screw function is positive
semidefinite on every finite grid. -/
theorem screw_gram_psd_of_RH (hRH : RiemannHypothesis) (N : ℕ) (t : Fin N → ℝ) :
    IsPSDq (Matrix.of fun i j : Fin N => G (t i) (t j)) := by sorry

end ChallengeScrewRH
