-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology

namespace GlobalTheory.ZetaLeft

noncomputable def emT (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (1 - s) - (1 - s) * (x : ℂ) ^ (1 - s - 1) / 2
    + (1 - s) * (1 - s - 1) * (x : ℂ) ^ (1 - s - 1 - 1) / 12

noncomputable def emE (x : ℝ) (s : ℂ) : ℂ :=
  emT (x + 1) s - emT x s - (1 - s) * (x : ℂ) ^ (1 - s - 1)

lemma hasDerivAt_shift_cpow {a t : ℝ} (h : 0 < a + t) (c : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) + z) ^ c) (c * ((a : ℂ) + t) ^ (c - 1)) (t : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add _
  have h2 : ((a : ℂ) + t) ∈ slitPlane := by
    left; simpa using h
  simpa using h1.cpow_const (c := c) h2

lemma norm_emE_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -(15/8 : ℝ) ≤ s.re) :
    ‖emE a s‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
  set w : ℂ := 1 - s with hw
  let G : ℂ → ℂ := fun z => ((a : ℂ) + z) ^ w - (z - 1/2) * (w * ((a : ℂ) + z) ^ (w - 1))
    + (z ^ 2 - z + 1/6) / 2 * (w * (w - 1) * ((a : ℂ) + z) ^ (w - 1 - 1))
    - (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6 * (w * (w - 1) * (w - 1 - 1) * ((a : ℂ) + z) ^ (w - 1 - 1 - 1))
  let G' : ℝ → ℂ := fun t => - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) *
    (w * (w - 1) * (w - 1 - 1) * (w - 1 - 1 - 1) * ((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1))
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y : ℝ => G y) (G' t) t := by
    intro t ht
    have h : 0 < a + t := by linarith
    have p1 : HasDerivAt (fun z : ℂ => z - 1/2) 1 (t : ℂ) := (hasDerivAt_id _).sub_const _
    have p2 : HasDerivAt (fun z : ℂ => (z ^ 2 - z + 1/6) / 2) ((t : ℂ) - 1/2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 2).sub (hasDerivAt_id _)).add_const (1/6)).div_const 2
      exact this.congr_deriv (by simp; ring)
    have p3 : HasDerivAt (fun z : ℂ => (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6)
        (((t : ℂ) ^ 2 - t + 1/6) / 2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 3).sub
        (((hasDerivAt_id (t : ℂ)).pow 2).const_mul (3/2))).add
        ((hasDerivAt_id (t : ℂ)).div_const 2)).div_const 6
      exact this.congr_deriv (by simp; ring)
    have hG : HasDerivAt G (G' t) (t : ℂ) := by
      have := (((hasDerivAt_shift_cpow h w).sub
        (p1.mul ((hasDerivAt_shift_cpow h (w - 1)).const_mul w))).add
        (p2.mul ((hasDerivAt_shift_cpow h (w - 1 - 1)).const_mul (w * (w - 1))))).sub
        (p3.mul ((hasDerivAt_shift_cpow h (w - 1 - 1 - 1)).const_mul (w * (w - 1) * (w - 1 - 1))))
      exact this.congr_deriv (by simp only [G']; ring)
    exact hG.comp_ofReal
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖G' t‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
    intro t ht
    have h : 0 < a + t := by linarith [ht.1]
    have b1 : ‖- (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)‖ ≤ 1 := by
      have : - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)
          = ((- ((t ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h4 : 0 ≤ t ^ 2 := by positivity
      have h5 : 0 ≤ t ^ 3 := pow_nonneg ht.1 _
      constructor <;> linarith [ht.1, ht.2]
    have key : ∀ c : ℝ, |c| ≤ 2 → ‖(c : ℂ) - s‖ ≤ ‖s‖ + 2 := by
      intro c hc
      have := norm_sub_le (c : ℂ) s
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have c0 : ‖w‖ ≤ ‖s‖ + 2 := by simpa using key 1 (by norm_num)
    have c1 : ‖w - 1‖ ≤ ‖s‖ + 2 := by
      convert key 0 (by norm_num) using 2; rw [hw]; push_cast; ring
    have c2 : ‖w - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-1) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c3 : ‖w - 1 - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-2) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c4 : ‖((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1)‖ ≤ a ^ (-(9/8 : ℝ)) := by
      rw [← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos h]
      have e : (w - 1 - 1 - 1 - 1).re ≤ -(9/8 : ℝ) := by
        simp [hw]; linarith
      calc _ ≤ (a + t) ^ (-(9/8 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) e
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [ht.1]) (by norm_num)
    simp only [G', norm_mul]
    calc _ ≤ 1 * ((‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * a ^ (-(9/8 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun y : ℝ => G y) (f' := G')
    (fun t ht => (hd t ht.1).hasDerivWithinAt) hb
  refine le_of_eq_of_le (congrArg _ ?_) this
  simp only [G, emE, emT, ← hw]
  push_cast
  simp only [add_zero]
  ring

lemma summable_nine_pow_mul_inv_sq_succ : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(9/8 : ℝ))) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : -(9/8 : ℝ) < -1))
  simpa using this

lemma differentiable_emT {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emT x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  unfold emT
  fun_prop

lemma differentiable_emE {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emE x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  have h1 := differentiable_emT hx
  have h2 := differentiable_emT (x := x + 1) (by linarith)
  unfold emE
  fun_prop

lemma differentiableOn_tsum_emE :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, emE ((n : ℝ) + 1) s) {s : ℂ | -(15/8 : ℝ) < s.re} := by
  intro s hs
  have ho : IsOpen ({z : ℂ | -(15/8 : ℝ) < z.re} ∩ Metric.ball 0 (‖s‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (z : ℂ) => emE ((n : ℝ) + 1) z)
    (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 3) ^ 4))
    (fun n => (differentiable_emE (by positivity)).differentiableOn) ho (by
      intro n z hz
      have h1 : ‖z‖ < ‖s‖ + 1 := by simpa using hz.2
      refine (norm_emE_le (by simp) (le_of_lt hz.1)).trans ?_
      have h2 : ‖z‖ + 2 ≤ ‖s‖ + 3 := by linarith
      gcongr)
  exact (this.differentiableAt (ho.mem_nhds ⟨hs, by simp⟩)).differentiableWithinAt

lemma tendsto_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := (tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp h1
  refine this.congr fun n => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

lemma eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have hsum : Summable (fun n : ℕ => emE ((n : ℝ) + 1) s) :=
    Summable.of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 2) ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have hT : Tendsto (fun n : ℕ => emT ((n : ℝ) + 1) s) atTop (𝓝 0) := by
    have := ((tendsto_cpow_zero (c := 1 - s) (by simp; linarith)).sub
      (((tendsto_cpow_zero (c := 1 - s - 1) (by simp; linarith)).const_mul (1 - s)).div_const 2)).add
      (((tendsto_cpow_zero (c := 1 - s - 1 - 1) (by simp; linarith)).const_mul
        ((1 - s) * (1 - s - 1))).div_const 12)
    simpa [emT] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    exact (by simpa using this : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)).hasSum
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, emE ((n : ℝ) + 1) s =
      emT ((N : ℝ) + 1) s - emT 1 s + (s - 1) * ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ s := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, emE]
      have : (1 - s - 1) = -s := by ring
      rw [this, Complex.cpow_neg]
      push_cast
      ring
  have h1 := (hT.sub_const (emT 1 s)).add (hz.tendsto_sum_nat.const_mul (s - 1))
  have h2 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h2
  rw [tendsto_nhds_unique h2 h1]
  ring

lemma eq_of_lt {s : ℂ} (hs : -(15/8 : ℝ) < s.re) (h1 : s ≠ 1) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have ho : IsOpen {z : ℂ | -(15/8 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ z : ℂ, z ≠ 1 → LFunctionTrivChar₁ 1 z = (z - 1) * riemannZeta z := by
    intro z hz
    rw [LFunctionTrivChar₁, Function.update_of_ne hz, LFunctionTrivChar, LFunction_modOne_eq]
  have hA : AnalyticOnNhd ℂ (LFunctionTrivChar₁ 1) {z : ℂ | -(15/8 : ℝ) < z.re} :=
    (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd ho
  have hB : AnalyticOnNhd ℂ (fun s => emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s)
      {z : ℂ | -(15/8 : ℝ) < z.re} :=
    ((differentiable_emT one_pos).differentiableOn.add differentiableOn_tsum_emE).analyticOnNhd ho
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 2) (by simp; norm_num) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      rw [hf z (by rintro rfl; simp at hz), eq_of_one_lt hz])
  rw [← hf s h1]
  exact this hs

theorem norm_sub_one_mul_riemannZeta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(7/4 : ℝ) ≤ s.re → s ≠ 1 →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 5 := by
  set K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9/8 : ℝ)) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun n => by positivity
  refine ⟨3 + K, by linarith, fun s hs h1 => ?_⟩
  rw [eq_of_lt (by linarith) h1]
  set R := ‖s‖ + 2 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg s; linarith
  have h2 : ‖∑' n : ℕ, emE ((n : ℝ) + 1) s‖ ≤ R ^ 4 * K :=
    tsum_of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.hasSum.mul_left (R ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have c0 : ‖1 - s‖ ≤ R := by
    have := norm_sub_le 1 s
    rw [norm_one] at this; linarith
  have c1 : ‖1 - s - 1‖ ≤ R := by simp [hR]
  have h3 : ‖emT 1 s‖ ≤ 1 + R / 2 + R * R / 12 := by
    simp only [emT, Complex.ofReal_one, Complex.one_cpow, mul_one]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
    · simp only [norm_one, norm_div, Complex.norm_ofNat]; gcongr
    · simp only [norm_mul, norm_div, Complex.norm_ofNat]; gcongr
  have p0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
  have p1 : R ^ 1 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p5 : R ^ 4 * K ≤ R ^ 5 * K := by gcongr
  refine (norm_add_le _ _).trans ?_
  nlinarith

end GlobalTheory.ZetaLeft
