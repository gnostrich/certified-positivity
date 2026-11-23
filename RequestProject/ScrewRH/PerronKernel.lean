module

public import Mathlib

@[expose] public section

/-!
# ScrewRH.PerronKernel: the `1/z²` Perron kernel (blueprint lemma 1)

For `c > 0` and real `x`,
`(1/2π) ∫_ℝ exp ((c + iy) x) / (c + iy)² dy = max x 0`.

Proof: Fourier inversion for `g x = max x 0 · exp (-c x)`, whose Fourier transform is
`𝓕 g ξ = 1 / (c + 2πiξ)²` (computed by the fundamental theorem of calculus on `(0, ∞)`),
followed by the substitution `y = 2πξ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform Real

namespace ScrewRH

/-- The damped ramp `g x = max x 0 · exp (-c x)`. -/
noncomputable def ramp (c : ℝ) (x : ℝ) : ℂ := ((max x 0 * Real.exp (-c * x) : ℝ) : ℂ)

lemma continuous_ramp (c : ℝ) : Continuous (ramp c) := by
  unfold ramp; fun_prop

lemma integrable_ramp {c : ℝ} (hc : 0 < c) : Integrable (ramp c) := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-c * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hc
  have h2 : IntegrableOn (ramp c) (Ioi 0) := by
    refine (h1.ofReal (𝕜 := ℂ)).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : 0 < x := hx
    simp [ramp, Real.rpow_one, max_eq_left hx'.le]
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  have hx' : x ≤ 0 := not_lt.1 hx
  simp [ramp, max_eq_right hx']

/-- `∫_{(0,∞)} x e^{-rx} dx = 1/r²` for `re r > 0`. -/
lemma integral_mul_exp_neg_Ioi {r : ℂ} (hr : 0 < r.re) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) * Complex.exp (-r * x) = 1 / r ^ 2 := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  set F : ℝ → ℂ := fun x => -((x : ℂ) / r + 1 / r ^ 2) * Complex.exp (-r * x) with hF
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F ((x : ℂ) * Complex.exp (-r * x)) x := by
    intro x _
    have h : HasDerivAt (fun z : ℂ => -(z / r + 1 / r ^ 2) * Complex.exp (-r * z))
        ((x : ℂ) * Complex.exp (-r * x)) (x : ℂ) := by
      have h1 : HasDerivAt (fun z : ℂ => -(z / r + 1 / r ^ 2)) (-(1 / r)) (x : ℂ) := by
        have := (((hasDerivAt_id (x : ℂ)).div_const r).add_const (1 / r ^ 2)).fun_neg
        simpa only [id, one_div] using this
      have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-r * z))
          (Complex.exp (-r * x) * (-r)) (x : ℂ) := by
        have := ((hasDerivAt_id (x : ℂ)).const_mul (-r)).cexp
        simpa using this
      convert h1.mul h2 using 1
      field_simp
      ring
    exact h.comp_ofReal
  have hnorm : ∀ x : ℝ, ‖(x : ℂ) * Complex.exp (-r * x)‖ = |x| * Real.exp (-r.re * x) := by
    intro x
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    congr 2
    simp
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (-r * x)) (Ioi 0) := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-r.re * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hr
    refine Integrable.mono' h1 ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => (x : ℂ) * Complex.exp (-r * x))
        |>.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx' : 0 < x := hx
      rw [hnorm, abs_of_pos hx', Real.rpow_one]
  have htend : Tendsto F atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (‖(1 : ℂ) / r‖ * x + ‖(1 : ℂ) / r ^ 2‖) *
        Real.exp (-r.re * x)) atTop (𝓝 0) := by
      have e1 : Tendsto (fun x : ℝ => (r.re * x) ^ 1 * Real.exp (-(r.re * x))) atTop (𝓝 0) :=
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_id.const_mul_atTop hr)
      have e2 : Tendsto (fun x : ℝ => Real.exp (-r.re * x)) atTop (𝓝 0) := by
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
        refine this.congr (fun x => ?_)
        simp [Function.comp, neg_mul]
      have e3 := (e1.const_mul (‖(1 : ℂ) / r‖ / r.re)).add (e2.const_mul ‖(1 : ℂ) / r ^ 2‖)
      simp only [mul_zero, add_zero] at e3
      refine e3.congr (fun x => ?_)
      have : r.re ≠ 0 := hr.ne'
      simp only [pow_one, neg_mul]
      field_simp
    refine squeeze_zero_norm' ((eventually_ge_atTop 0).mono fun x hx0 => ?_) hlim
    rw [hF]
    simp only [norm_mul, norm_neg, Complex.norm_exp]
    have : (-r * (x : ℂ)).re = -r.re * x := by simp
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine (norm_add_le _ _).trans ?_
    gcongr
    rw [div_eq_mul_one_div (x : ℂ), norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    rw [abs_of_nonneg hx0]
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [this, hF]
  simp

/-- The Fourier transform of the damped ramp. -/
lemma fourier_ramp {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (ramp c) ξ = 1 / ((c : ℂ) + 2 * π * ξ * I) ^ 2 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hre : 0 < ((c : ℂ) + 2 * π * ξ * I).re := by simpa using hc
  rw [← integral_mul_exp_neg_Ioi hre]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : 0 < x := hx
    simp only [ramp, max_eq_left hx'.le, smul_eq_mul]
    push_cast
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  · intro x hx
    have hx' : x ≤ 0 := not_lt.1 hx
    simp [ramp, max_eq_right hx']

lemma denom_ne_zero {c : ℝ} (hc : 0 < c) (y : ℝ) : ((c : ℂ) + y * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma integrable_fourier_ramp {c : ℝ} (hc : 0 < c) : Integrable (𝓕 (ramp c)) := by
  rw [show 𝓕 (ramp c) = fun ξ : ℝ => 1 / ((c : ℂ) + 2 * π * ξ * I) ^ 2 from
    funext (fourier_ramp hc)]
  set m : ℝ := min (c ^ 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (1 / m)) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine continuous_const.div (by fun_prop) (fun ξ => pow_ne_zero 2 ?_)
    have := denom_ne_zero hc (2 * π * ξ)
    push_cast at this
    exact this
  · refine Eventually.of_forall (fun ξ => ?_)
    have hn : ‖(c : ℂ) + 2 * π * ξ * I‖ ^ 2 = c ^ 2 + (2 * π * ξ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [norm_div, norm_one, norm_pow, hn]
    have hpi : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hle : m * (1 + ξ ^ 2) ≤ c ^ 2 + (2 * π * ξ) ^ 2 := by
      have h1 : m ≤ c ^ 2 := min_le_left _ _
      have h2 : m ≤ 1 := min_le_right _ _
      have h3 : m * ξ ^ 2 ≤ (2 * π * ξ) ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg ξ]
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = 1 / m * (1 + ξ ^ 2)⁻¹ * (m * (1 + ξ ^ 2)) := by field_simp
      _ ≤ 1 / m * (1 + ξ ^ 2)⁻¹ * (c ^ 2 + (2 * π * ξ) ^ 2) := by gcongr

/-- **Blueprint lemma 1 (Perron kernel).** For `c > 0` and real `x`,
`(1/2π) ∫_ℝ exp ((c + iy) x) / (c + iy)² dy = max x 0`. -/
theorem perron_kernel {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ y : ℝ, Complex.exp ((c + y * I) * x) / (c + y * I) ^ 2 =
      ((max x 0 : ℝ) : ℂ) := by
  have hinv := (integrable_ramp hc).fourierInv_fourier_eq (integrable_fourier_ramp hc)
    (continuous_ramp c).continuousAt (v := x)
  rw [Real.fourierInv_eq'] at hinv
  simp_rw [fourier_ramp hc, smul_eq_mul] at hinv
  -- substitute `y = 2πξ`
  set h : ℝ → ℂ := fun y => Complex.exp (y * x * I) / ((c : ℂ) + y * I) ^ 2 with hh
  have hsub : (∫ ξ : ℝ, Complex.exp (↑(2 * π * inner ℝ ξ x) * I) *
      (1 / ((c : ℂ) + 2 * π * ξ * I) ^ 2)) = ∫ ξ : ℝ, h (2 * π * ξ) := by
    congr 1; ext ξ
    simp only [hh, RCLike.inner_apply, conj_trivial]
    push_cast
    ring_nf
  rw [hsub, Measure.integral_comp_mul_left h (2 * π)] at hinv
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.2 hpi)] at hinv
  have hexp : ∀ y : ℝ, Complex.exp ((c + y * I) * x) / (c + y * I) ^ 2 =
      Complex.exp (c * x) * h y := by
    intro y
    simp only [hh]
    rw [mul_div_assoc', ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hexp]
  rw [integral_const_mul, ← mul_assoc, mul_comm _ (Complex.exp _), mul_assoc]
  have hh' : (1 / (2 * π) : ℂ) * ∫ y, h y = ramp c x := by
    rw [← hinv, Complex.real_smul]
    push_cast
    ring
  rw [hh', ramp]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  simp
