module

public import Mathlib
public import RequestProject.Horizon
public import RequestProject.V5_1
public import RequestProject.ScrewRH.ExplicitFormula
public import RequestProject.ScrewRH.PSD

@[expose] public section

/-!
# ScrewRH.MainRH: RH implies that Krein's Gram kernel of the screw function is PSD

Under `RiemannHypothesis` (Mathlib's definition), every `ρ ∈ Z` is `½ + iγ`, so the real part of
the explicit formula `Psi_eq_tsum_zeros` reads `Psi t = ∑' ρ, m(ρ)/γ² · (1 - cos (γ t))`
(for `t ≥ 0`, and then for all `t` since `Psi` is even). `isPSDq_G_of_cos_series` finishes.

Combined with a proof `riemannHypothesis : RiemannHypothesis` (for instance Alpöge's), the
headline gives the unconditional statement
`∀ N (t : Fin N → ℝ), Horizon.IsPSDq (Matrix.of fun i j => V5_1.G (t i) (t j))`
as `screw_gram_psd_of_RH riemannHypothesis`.
-/

open Complex

namespace ScrewRH

/-- Elements of `Z` satisfy the hypotheses of Mathlib's `RiemannHypothesis`. -/
lemma re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ Z) : ρ.re = 1 / 2 := by
  obtain ⟨h0, hpos, hlt⟩ := hρ
  refine hRH ρ h0 ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hpos
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  · rintro rfl
    simp at hlt

/-- The zero term on the critical line. -/
lemma zeroTerm_re_of_re_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) :
    (zeroTerm t ρ).re = (mult ρ : ℝ) / ρ.im ^ 2 * (1 - Real.cos (ρ.im * t)) := by
  have e : ρ - 1 / 2 = (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hρ]
  have e2 : zeroTerm t ρ = (((mult ρ : ℝ) / ρ.im ^ 2 : ℝ) : ℂ) *
      (1 - Complex.exp (((ρ.im * t : ℝ) : ℂ) * I)) := by
    rw [zeroTerm, e]
    push_cast
    have : ((ρ.im : ℂ) * I) ^ 2 = -((ρ.im : ℂ) ^ 2) := by rw [mul_pow, I_sq]; ring
    rw [this, div_neg, ← neg_div]
    ring_nf
  rw [e2, Complex.re_ofReal_mul, sub_re, one_re, Complex.exp_ofReal_mul_I_re]

lemma norm_sub_half_sq_of_re_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ - 1 / 2‖ ^ 2 = ρ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [hρ]; ring

/-- **RH ⇒ cosine series.** Under RH, `Psi t = ∑' ρ, m(ρ)/γ² (1 - cos (γ t))` for every real `t`. -/
theorem Psi_hasSum_cos_of_RH (hRH : RiemannHypothesis) (t : ℝ) :
    HasSum (fun ρ : Z => (mult (ρ : ℂ) : ℝ) / (ρ : ℂ).im ^ 2 * (1 - Real.cos ((ρ : ℂ).im * t)))
      (V5_1.Psi t) := by
  have habs : V5_1.Psi t = V5_1.Psi |t| := by simp [V5_1.Psi]
  have h := (summable_zero_term |t|).hasSum
  rw [← Psi_eq_tsum_zeros |t| (abs_nonneg t)] at h
  have h2 := Complex.hasSum_re h
  rw [Complex.ofReal_re, ← habs] at h2
  refine h2.congr_fun (fun ρ => ?_)
  rw [zeroTerm_re_of_re_half (re_eq_half_of_RH hRH ρ.2)]
  congr 2
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
  · rw [h, mul_neg, Real.cos_neg]

/-- **Headline.** Under the Riemann Hypothesis, Krein's Gram kernel `G(t,u) = Ψ(t) + Ψ(u) - Ψ(t-u)`
of Suzuki's screw function is positive semidefinite on every finite grid. -/
theorem screw_gram_psd_of_RH (hRH : RiemannHypothesis) (N : ℕ) (t : Fin N → ℝ) :
    Horizon.IsPSDq (Matrix.of fun i j : Fin N => V5_1.G (t i) (t j)) := by
  refine isPSDq_G_of_cos_series (fun ρ : Z => (mult (ρ : ℂ) : ℝ) / (ρ : ℂ).im ^ 2)
    (fun ρ : Z => (ρ : ℂ).im) (fun ρ => by positivity) ?_ (Psi_hasSum_cos_of_RH hRH) t
  refine summable_zeros.congr (fun ρ => ?_)
  rw [norm_sub_half_sq_of_re_half (re_eq_half_of_RH hRH ρ.2)]

end ScrewRH
