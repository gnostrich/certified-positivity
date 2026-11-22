module

public import Mathlib
public import RequestProject.V5_1
public import RequestProject.ScrewRH.ZetaHalf
public import RequestProject.ScrewRH.Defs

@[expose] public section

/-!
# ScrewRH.LogDerivHalf: `F(0) = (A - log π)/2` (blueprint lemma 3)

With `F z = -(ζ'/ζ)(1/2 + z)` (`ScrewRH.F`, from `ScrewRH.Defs`), the log-derivative form of the functional equation at the fixed
point `s = 1/2` gives `2 ζ'/ζ(1/2) = log (2π) - ψ(1/2) + (π/2) tan (π/4) = log π - A`, where
`A = -γ - π/2 - 3 log 2 = ψ(1/4)` (`V5_1.A`). This needs `ζ(1/2) ≠ 0` (`ScrewRH.ZetaHalf`).
-/

open Complex

namespace ScrewRH

lemma half_ne_int : ∀ n : ℤ, (1 / 2 : ℂ) ≠ n := by
  intro n h
  have h1 : (1 / 2 : ℂ).re = (n : ℂ).re := by rw [h]
  simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
    Complex.intCast_re] at h1
  have h2 : (2 * n : ℝ) = 1 := by rw [← h1]; norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- `ζ'/ζ(1/2) = (log π - A)/2`. -/
theorem logDeriv_riemannZeta_half :
    logDeriv riemannZeta (1 / 2) = ((Real.log Real.pi - V5_1.A) / 2 : ℝ) := by
  have h := logDeriv_riemannZeta_one_sub half_ne_int riemannZeta_half_ne_zero
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, Complex.digamma_one_half] at h
  have htan : Complex.tan (↑Real.pi * (1 / 2) / 2) = 1 := by
    rw [show (↑Real.pi * (1 / 2) / 2 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_tan, Real.tan_pi_div_four, Complex.ofReal_one]
  have hlog2pi : Complex.log (2 * ↑Real.pi) = ((Real.log 2 + Real.log Real.pi : ℝ) : ℂ) := by
    rw [← Real.log_mul (by norm_num) Real.pi_ne_zero, Complex.ofReal_log (by positivity)]
    push_cast; ring_nf
  have hlog2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [htan, hlog2pi, hlog2] at h
  unfold V5_1.A
  push_cast at h ⊢
  linear_combination (1 / 2 : ℂ) * h

/-- **Blueprint lemma 3.** `F 0 = (A - log π)/2`. -/
theorem F_zero : F 0 = ((V5_1.A - Real.log Real.pi) / 2 : ℝ) := by
  have h := logDeriv_riemannZeta_half
  rw [logDeriv_apply] at h
  simp only [F, add_zero]
  rw [h]
  push_cast
  ring

end ScrewRH
