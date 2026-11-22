module

public import Mathlib

@[expose] public section

/-!
# Shared definitions for the explicit formula of the screw function

`F z = −ζ'/ζ(½ + z)`, the kernel `e^{zt}/z²`, the set of nontrivial zeros
of `ζ`, and their multiplicities. Used by the files in `RequestProject/ScrewRH/`
that prove `V5_1.Psi t = ∑' ρ, m(ρ) (e^{(ρ-½)t} - 1)/(ρ-½)²` and, under
`RiemannHypothesis`, positive semidefiniteness of the Gram kernel on every grid.
-/

open Complex

namespace ScrewRH

/-- `F z = −ζ'/ζ(½ + z)`. -/
noncomputable def F (z : ℂ) : ℂ :=
  -(deriv riemannZeta (1 / 2 + z) / riemannZeta (1 / 2 + z))

/-- The Perron kernel `e^{zt}/z²`. -/
noncomputable def kern (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * t) / z ^ 2

/-- The nontrivial zeros of `ζ`. -/
def Z : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- Multiplicity of a zero of `ζ`. -/
noncomputable def mult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

end ScrewRH
