-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TsumOneDivRpowLe
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaWide

theorem scaled : ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (M : ℝ), Differentiable ℂ F → F c ≠ 0 →
    (∀ w, ‖w - c‖ ≤ 15/4 → ‖F w‖ ≤ M) →
    ({w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖))) ∧
    ∀ s : ℂ, ‖s - c‖ ≤ 3 → F s ≠ 0 →
      ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0},
        (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (4/5) (14/15) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun F c M hF hc hM => ?_⟩
  set g : ℂ → ℂ := fun z => c + 15/4 * z with hg
  have hgn : ∀ z, ‖g z - c‖ = 15/4 * ‖z‖ := fun z => by simp [hg]
  have hgd : ∀ z, HasDerivAt g (15/4) z := fun z => by
    have := ((hasDerivAt_id z).const_mul (15/4 : ℂ)).const_add c
    rw [mul_one] at this
    exact this
  have hgD : Differentiable ℂ g := fun z => (hgd z).differentiableAt
  have hfD : Differentiable ℂ (F ∘ g) := hF.comp hgD
  have hg0 : g 0 = c := by simp [hg]
  have hf0 : (F ∘ g) 0 = F c := by simp [hg0]
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ g) M (fun z _ => hfD.analyticAt z) (by rwa [hf0])
    (fun z hz => hM _ (by
      have : ‖z‖ ≤ 1 := by simpa using hz
      rw [hgn]; linarith))
  rw [hf0] at h2 h3
  have hinj : Function.Injective g := fun a b h => by simpa [hg] using h
  have hsur : ∀ w, g ((w - c) * (4/15)) = w := fun w => by simp only [hg]; ring
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0} = g '' {w : ℂ | ‖w‖ ≤ 14/15 ∧ (F ∘ g) w = 0} := by
    ext w
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨(w - c) * (4/15), ⟨?_, by simp only [Function.comp, hsur, hb]⟩, hsur w⟩
      have := hgn ((w - c) * (4/15))
      rw [hsur] at this
      linarith
    · rintro ⟨z, ⟨ha, hb⟩, rfl⟩
      exact ⟨by rw [hgn]; linarith, hb⟩
  have hord : ∀ z, analyticOrderNatAt (F ∘ g) z = analyticOrderNatAt F (g z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hgD.analyticAt z) (by rw [(hgd z).deriv]; norm_num)]
  simp only [hord] at h2 h3
  rw [hset]
  refine ⟨⟨h1.image g, by rwa [finsum_mem_image hinj.injOn]⟩, fun s hs hFs => ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = g z := ⟨_, (hsur s).symm⟩
  rw [hgn] at hs
  have h4 := h3 z (by linarith) hFs
  have hL : 0 ≤ C * (1 + Real.log (M / ‖F c‖)) := (norm_nonneg _).trans h4
  rw [finsum_mem_image hinj.injOn]
  rw [finsum_mem_eq_finite_toFinset_sum _ h1] at h4 ⊢
  have hd : deriv (F ∘ g) z = deriv F (g z) * (15/4) :=
    ((hF (g z)).hasDerivAt.comp z (hgd z)).deriv
  have e : deriv F (g z) / F (g z) - ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (g z - g w)
      = (4/15) * (deriv (F ∘ g) z / (F ∘ g) z -
        ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (z - w)) := by
    rw [hd, mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : g z - g w = 15/4 * (z - w) := by simp only [hg]; ring
      rw [this, div_eq_mul_inv, mul_inv]
      ring
  rw [e, norm_mul]
  have : ‖(4/15 : ℂ)‖ = 4/15 := by simp
  rw [this]
  linarith

theorem zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

theorem order_zeta₁_eq {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta₁ s = analyticOrderNatAt riemannZeta s := by
  unfold analyticOrderNatAt
  have hev : riemannZeta₁ =ᶠ[nhds s] (fun z => z - 1) * riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zeta₁_eq hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul h1 h2,
    h1.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hs), zero_add]

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℝ)) ≤ C * Real.log (|s.im| + 2) ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, H⟩ := scaled
  obtain ⟨B, hB, hBl⟩ := GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le
  set K : ℝ := 2 * (B + 1) * 4 ^ 5 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK1
  refine ⟨C * (2 * (1 + Real.log K) + 5), by positivity, fun s hs1 hs2 hs hz => ?_⟩
  set c : ℂ := 2 + s.im * I with hc
  set T : ℝ := |s.im| + 2 with hT
  have hT2 : 2 ≤ T := by have := abs_nonneg s.im; linarith
  have hcre : c.re = 2 := by simp [hc]
  have hc1 : c ≠ 1 := fun h => by rw [h] at hcre; norm_num at hcre
  have hcn : ‖c‖ ≤ T := by
    refine (norm_add_le _ _).trans ?_
    simp [hT, add_comm]
  have hlow : 1 / 2 ≤ ‖riemannZeta₁ c‖ := by
    have h := GlobalTheory.LLower.norm_LFunction_ge 1 1 c (by rw [hcre]; norm_num)
    rw [LFunction_modOne_eq, hcre] at h
    have h' : 1 ≤ ‖c - 1‖ := by
      have := Complex.re_le_norm (c - 1)
      rw [sub_re, hcre, one_re] at this
      linarith
    rw [zeta₁_eq hc1, norm_mul]
    nlinarith
  have hne : riemannZeta₁ c ≠ 0 := norm_pos_iff.1 (by linarith)
  have hup : ∀ w, ‖w - c‖ ≤ 15/4 → ‖riemannZeta₁ w‖ ≤ (B + 1) * (4 * T) ^ 5 := by
    intro w hw
    have hp : 1 ≤ (4 * T) ^ 5 := one_le_pow₀ (by linarith)
    by_cases h1 : w = 1
    · rw [h1, riemannZeta₁_one, norm_one]
      nlinarith
    · have hre : -(7/4 : ℝ) ≤ w.re := by
        have := Complex.abs_re_le_norm (w - c)
        rw [sub_re, hcre] at this
        have := neg_abs_le (w.re - 2)
        linarith
      have hwn : ‖w‖ + 2 ≤ 4 * T := by
        have := norm_add_le (w - c) c
        rw [sub_add_cancel] at this
        linarith
      rw [zeta₁_eq h1]
      refine (hBl w hre h1).trans ?_
      gcongr
      linarith
  obtain ⟨⟨h1, h2⟩, h3⟩ := H riemannZeta₁ c _ differentiable_riemannZeta₁ hne hup
  have hbound : C * (1 + Real.log ((B + 1) * (4 * T) ^ 5 / ‖riemannZeta₁ c‖))
      ≤ C * (2 * (1 + Real.log K) + 5) * Real.log T := by
    have hlT : 1 / 2 ≤ Real.log T := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log (by norm_num) hT2
      linarith
    have ha : (B + 1) * (4 * T) ^ 5 / ‖riemannZeta₁ c‖ ≤ K * T ^ 5 := by
      calc _ ≤ (B + 1) * (4 * T) ^ 5 / (1 / 2) := by gcongr
        _ = K * T ^ 5 := by rw [hK]; ring
    have hb := Real.log_le_log (by positivity) ha
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hb
    rw [mul_assoc]
    gcongr
    push_cast at hb
    nlinarith
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ riemannZeta₁ w = 0} := by
    ext w
    by_cases hw : w = 1
    · simp [hw]
    · simp [hw, zeta₁_eq hw, sub_ne_zero.2 hw]
  have hne1 : ∀ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ riemannZeta₁ w = 0}, w ≠ 1 := by
    rintro w ⟨_, hw⟩ rfl
    simp at hw
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [hset]
  refine ⟨h1, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) (h2.trans hbound)
    exact finsum_mem_congr rfl fun w hw => by rw [order_zeta₁_eq (hne1 w hw)]
  · have hsc : ‖s - c‖ ≤ 3 := by
      have : s - c = ((s.re - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hz1 : riemannZeta₁ s ≠ 0 := by rw [zeta₁_eq hs]; exact mul_ne_zero hs0 hz
    refine le_trans (le_of_eq ?_) ((h3 s hsc hz1).trans hbound)
    congr 2
    · rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
      field_simp
      ring
    · exact finsum_mem_congr rfl fun w hw => by rw [order_zeta₁_eq (hne1 w hw)]

end GlobalTheory.ZetaWide
