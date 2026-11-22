-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib
public import AlpogeRH.Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlane

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digamma_log_bound_right_half_plane : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  first | exact @GlobalTheory.CompanionTheory.DigammaBound.digamma_bound | exact GlobalTheory.CompanionTheory.DigammaBound.digamma_bound | (intros; apply GlobalTheory.CompanionTheory.DigammaBound.digamma_bound <;> assumption)
