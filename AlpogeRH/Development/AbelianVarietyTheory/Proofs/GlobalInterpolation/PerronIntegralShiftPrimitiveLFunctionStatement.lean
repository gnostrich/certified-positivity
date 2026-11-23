-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerronIntegralShiftPrimitiveLFunction
public import Mathlib

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perron_integral_shift_primitive_LFunction : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ in (-T')..T', (-(deriv (LFunction χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / LFunction χ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))) - (if N = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  first | exact @GlobalTheory.PerronShift.perron_shift | exact GlobalTheory.PerronShift.perron_shift | (intros; apply GlobalTheory.PerronShift.perron_shift <;> assumption)
