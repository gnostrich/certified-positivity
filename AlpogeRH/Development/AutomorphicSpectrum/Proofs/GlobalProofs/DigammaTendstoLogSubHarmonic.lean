-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Nat Real

namespace GlobalTheory.CompanionTheory.DigammaLimit

theorem euler_seq_le_Gamma {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) ≤ Real.Gamma x := by
  have hfe : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp]
    rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have h := Real.BohrMollerup.ge_logGammaSeq (f := Real.log ∘ Real.Gamma)
    Real.convexOn_log_Gamma hfe hx hn
  have hf1 : (Real.log ∘ Real.Gamma) 1 = 0 := by simp [Real.Gamma_one]
  rw [hf1, zero_add] at h
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hP : ∀ j ∈ Finset.range (n + 1), (0 : ℝ) < x + j := fun j _ => by positivity
  have hPpos : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) := Finset.prod_pos hP
  have hlog : Real.log ((n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ))) =
      Real.BohrMollerup.logGammaSeq x n := by
    rw [Real.log_div (by positivity) hPpos.ne', Real.log_mul (by positivity) hfac.ne',
      Real.log_rpow hn0, Real.log_prod (fun j hj => (hP j hj).ne')]
    rfl
  rw [← hlog] at h
  exact (Real.log_le_log_iff (by positivity) (Real.Gamma_pos_of_pos hx)).1 h

theorem norm_GammaSeq_le {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq w n‖ ≤ Real.Gamma w.re := by
  refine le_trans ?_ (euler_seq_le_Gamma hw hn)
  rw [GammaSeq, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    norm_prod, Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) (Finset.prod_pos fun j _ => by positivity)
  apply Finset.prod_le_prod₀ (fun j _ => by positivity)
  intro j _
  have := Complex.abs_re_le_norm (w + j)
  simp only [add_re, natCast_re] at this
  exact (le_abs_self _).trans this

theorem add_natCast_ne_zero {z : ℂ} (hz : 0 < z.re) (j : ℕ) : z + (j : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [add_re, natCast_re, zero_re] at h1
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem ne_neg_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  exact add_natCast_ne_zero hz m (by rw [h]; ring)

theorem differentiableAt_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  simp only [GammaSeq]
  refine DifferentiableAt.div ?_ ?_ (Finset.prod_ne_zero_iff.2 hP)
  · exact (differentiableAt_id.const_cpow (Or.inl hn')).mul_const _
  · exact DifferentiableAt.fun_finset_prod fun j _ => by fun_prop

theorem logDeriv_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w => GammaSeq w n) z =
      ((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  have hd1 : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w) ((n : ℂ) ^ z * Complex.log n * 1) z :=
    (hasDerivAt_id z).const_cpow (Or.inl hn')
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hcp : (n : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn']
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z :=
    DifferentiableAt.fun_finset_prod fun j _ => by fun_prop
  have e1 : (fun w => GammaSeq w n) =
      fun w => ((n : ℂ) ^ w * (n ! : ℂ)) / ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) := rfl
  have l1 : logDeriv (fun w : ℂ => (n : ℂ) ^ w) z = Complex.log n := by
    rw [logDeriv_apply, hd1.deriv]
    field_simp
  have l2 : ∀ j : ℕ, logDeriv (fun w : ℂ => w + (j : ℂ)) z = 1 / (z + (j : ℂ)) := by
    intro j
    rw [logDeriv_apply]
    simp
  rw [e1, logDeriv_fun_div (f := fun w : ℂ => (n : ℂ) ^ w * (n ! : ℂ))
      (g := fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z
      (mul_ne_zero hcp hfac) (Finset.prod_ne_zero_iff.2 hP)
      (hd1.differentiableAt.mul_const _) hd2,
    logDeriv_fun_mul (f := fun w : ℂ => (n : ℂ) ^ w) (g := fun _ : ℂ => (n ! : ℂ)) z hcp hfac
      hd1.differentiableAt (differentiableAt_const _),
    logDeriv_fun_prod (f := fun (j : ℕ) (w : ℂ) => w + (j : ℂ)) hP (fun j _ => by fun_prop),
    l1, logDeriv_const, Pi.zero_apply, add_zero, Complex.natCast_log]
  simp only [l2]

theorem tendsto_deriv_GammaSeq {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => deriv (fun w => GammaSeq w n) z) atTop (𝓝 (deriv Gamma z)) := by
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = z.re / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  obtain ⟨U, hU_def⟩ : ∃ U : Set ℂ, U = {w : ℂ | 0 < w.re} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU_def]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hre : ∀ w ∈ closedBall z r, z.re / 2 ≤ w.re ∧ w.re ≤ 3 * z.re / 2 := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hw
    have h2 := Complex.abs_re_le_norm (w - z)
    have h3 : |w.re - z.re| ≤ r := by
      have := h2.trans h1
      simpa only [sub_re] using this
    rw [abs_le] at h3
    constructor <;> linarith [h3.1, h3.2]
  have hsub : closedBall z r ⊆ U := fun w hw => by
    have := (hre w hw).1
    rw [hU_def]
    show 0 < w.re
    linarith
  have hGd : DifferentiableOn ℂ Gamma U := fun w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_Gamma w (ne_neg_natCast_of_re_pos hw)).differentiableWithinAt
  have hFd : ∀ n : ℕ, n ≠ 0 → DifferentiableOn ℂ (fun w => GammaSeq w n) U := fun n hn w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_GammaSeq hw hn).differentiableWithinAt
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc (z.re / 2) (3 * z.re / 2), ‖Real.Gamma x‖ ≤ M := by
    refine isCompact_Icc.exists_bound_of_continuousOn fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt.continuousWithinAt
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbd : ∀ n : ℕ, n ≠ 0 → ∀ w ∈ closedBall z r, ‖GammaSeq w n‖ ≤ M := by
    intro n hn w hw
    have h1 := hre w hw
    have h0 : 0 < w.re := by linarith [h1.1]
    exact (norm_GammaSeq_le h0 hn).trans ((le_abs_self _).trans (hM _ ⟨h1.1, h1.2⟩))
  have hc : ∀ θ, circleMap z r θ ∈ closedBall z r := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ)
  have key : Tendsto (fun n : ℕ => ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • GammaSeq w n) atTop
      (𝓝 (∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • Gamma w)) := by
    simp only [circleIntegral]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => r * ((r ^ 2)⁻¹ * M)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      apply Continuous.aestronglyMeasurable
      have hcont : Continuous fun θ : ℝ => GammaSeq (circleMap z r θ) n :=
        (hFd n hn).continuousOn.comp_continuous (continuous_circleMap z r)
          (fun θ => hsub (hc θ))
      have h0 : ∀ θ, (circleMap z r θ - z) ^ 2 ≠ 0 := fun θ =>
        pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).mul continuous_const).smul
        (((((continuous_circleMap z r).sub continuous_const).pow 2).inv₀ h0).smul hcont)
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine Eventually.of_forall fun θ _ => ?_
      simp only [deriv_circleMap, circleMap_sub_center, norm_smul, norm_mul, norm_circleMap_zero,
        Complex.norm_I, norm_inv, norm_pow, abs_of_pos hr, mul_one]
      gcongr
      exact hbd n hn _ (hc θ)
    · refine Eventually.of_forall fun θ _ => ?_
      exact ((GammaSeq_tendsto_Gamma _).const_smul _).const_smul _
  have h2 := key.const_smul ((2 * π * I : ℂ)⁻¹)
  have e : cderiv r Gamma z = deriv Gamma z := cderiv_eq_deriv hUo hGd hr hsub
  rw [← e]
  refine Tendsto.congr' ?_ h2
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact cderiv_eq_deriv hUo (hFd n hn) hr hsub

theorem tendsto_log_sub_sum_digamma : ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto (fun n : ℕ => ((Real.log n : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ))) Filter.atTop (nhds (Complex.digamma z)) := by
  intro z hz
  have h1 := (tendsto_deriv_GammaSeq hz).div (GammaSeq_tendsto_Gamma z)
    (Gamma_ne_zero_of_re_pos hz)
  rw [digamma_def, logDeriv_apply]
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [← logDeriv_GammaSeq hz hn, logDeriv_apply]
  rfl

end GlobalTheory.CompanionTheory.DigammaLimit
