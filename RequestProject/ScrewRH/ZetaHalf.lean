module

public import Mathlib

@[expose] public section

/-!
# ScrewRH.ZetaHalf: `ζ(1/2) < 0`

We prove `riemannZeta (1/2) ≠ 0`, in fact `riemannZeta (1/2) = x` for a real `x < 0`, using the
Dirichlet eta function written as a series of pairs
`η(s) = ∑ₙ ((2n+1)^{-s} - (2n+2)^{-s})`.

* For `re s > 1`, `η(s) = (1 - 2·2^{-s}) ζ(s)` (split `ζ` into odd and even terms).
* The pair series converges locally uniformly on `re s > 0` (mean value theorem), so `η` is
  holomorphic there.
* By the identity theorem, `(s - 1) η(s) = (1 - 2·2^{-s}) ζ₁(s)` on `re s > 0`, where
  `ζ₁ = riemannZeta₁` is Mathlib's entire completion of `(s - 1) ζ(s)`.
* At `s = 1/2` every pair is a positive real number, and `1 - 2·2^{-1/2} = 1 - √2 < 0`.
-/

open Complex Filter Topology

namespace ScrewRH

/-- The `n`-th pair of the Dirichlet eta series. -/
noncomputable def etaTerm (s : ℂ) (n : ℕ) : ℂ :=
  (((2 * n + 1 : ℝ)) : ℂ) ^ (-s) - (((2 * n + 2 : ℝ)) : ℂ) ^ (-s)

/-- The Dirichlet eta function, as a series of pairs. -/
noncomputable def etaPair (s : ℂ) : ℂ := ∑' n, etaTerm s n

/-- Mean value bound for `x ↦ x ^ (-s)` on `[a, b]`. -/
lemma norm_cpow_neg_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s))
      ((-s) * (x : ℂ) ^ (-s - 1)) (Set.Icc a b) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) (x : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (by simp [hx0])).hasDerivAt
    exact h1.comp_ofReal.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc a b, ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    gcongr
    simpa using Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith : -s.re - 1 ≤ 0)
  have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] using this

/-- Bound on a single pair. -/
lemma norm_etaTerm_le (s : ℂ) (hs : 0 ≤ s.re) (n : ℕ) :
    ‖etaTerm s n‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have h := norm_cpow_neg_sub_le (a := 2 * n + 1) (b := 2 * n + 2) (by positivity)
    (by linarith) s hs
  rw [etaTerm, norm_sub_rev]
  refine h.trans ?_
  have h1 : (2 * (n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-s.re - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : (2 * (n : ℝ) + 2) - (2 * n + 1) = 1 := by ring
  rw [h2, mul_one]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

lemma summable_rpow_shift {p : ℝ} (hp : p < -1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hp)
  simpa using this

lemma summable_etaTerm {s : ℂ} (hs : 0 < s.re) : Summable (etaTerm s) := by
  refine Summable.of_norm_bounded ((summable_rpow_shift (p := -s.re - 1) (by linarith)).mul_left
    ‖s‖) (fun n => norm_etaTerm_le s hs.le n)

/-- `η` is holomorphic on the right half-plane. -/
lemma differentiableOn_etaPair : DifferentiableOn ℂ etaPair {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  set δ := s0.re / 2 with hδ
  set R := ‖s0‖ + 1 with hR
  set U : Set ℂ := {s | δ < s.re} ∩ {s | ‖s‖ < R} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hs0U : s0 ∈ U := ⟨by show δ < s0.re; linarith, by simp [hR]⟩
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n, etaTerm w n) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_rpow_shift (p := -δ - 1) (by linarith)).mul_left R) (fun n => ?_) hUo
      (fun n w hw => ?_)
    · intro w _
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold etaTerm
      refine DifferentiableAt.sub ?_ ?_
      · exact (differentiableAt_neg_iff.2 differentiableAt_id).const_cpow
          (Or.inl (by norm_cast))
      · exact (differentiableAt_neg_iff.2 differentiableAt_id).const_cpow
          (Or.inl (by norm_cast))
    · have hwre : δ < w.re := hw.1
      have hwn : ‖w‖ < R := hw.2
      refine (norm_etaTerm_le w (by linarith) n).trans ?_
      gcongr
      all_goals linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  exact (hdiff s0 hs0U).differentiableAt (hUo.mem_nhds hs0U) |>.differentiableWithinAt

/-- For `re s > 1`: `η(s) = (1 - 2·2^{-s}) ζ(s)`. -/
lemma etaPair_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    etaPair s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℂ, f = fun m : ℕ => 1 / ((m : ℂ) + 1) ^ s := ⟨_, rfl⟩
  have hsum : Summable f := by
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    simpa [hf] using this
  have he : Summable (fun k => f (2 * k)) :=
    hsum.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable (fun k => f (2 * k + 1)) :=
    hsum.comp_injective (fun a b h => by simpa using h)
  have hZ : riemannZeta s = (∑' k, f (2 * k)) + ∑' k, f (2 * k + 1) := by
    have h1 : riemannZeta s = ∑' m, f m := by
      rw [hf]; exact zeta_eq_tsum_one_div_nat_add_one_cpow hs
    rw [h1]
    exact (he.hasSum.even_add_odd ho.hasSum).tsum_eq
  have hodd : ∀ k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * f k := by
    intro k
    simp only [hf, one_div]
    have : ((((2 * k + 1 : ℕ)) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), mul_inv,
      Complex.cpow_neg]
    push_cast
    ring
  have hO : (∑' k, f (2 * k + 1)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [tsum_congr hodd, tsum_mul_left, zeta_eq_tsum_one_div_nat_add_one_cpow hs, hf]
  have hterm : ∀ k : ℕ, etaTerm s k = f (2 * k) - f (2 * k + 1) := by
    intro k
    simp only [etaTerm, hf, one_div, Complex.cpow_neg]
    push_cast
    ring_nf
  have hη : etaPair s = (∑' k, f (2 * k)) - ∑' k, f (2 * k + 1) := by
    rw [etaPair, tsum_congr hterm, he.tsum_sub ho]
  rw [hη]
  linear_combination -hZ - 2 * hO

/-- The identity `(s - 1) η(s) = (1 - 2·2^{-s}) ζ₁(s)` on `re s > 0`. -/
lemma etaPair_identity {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * etaPair s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta₁ s := by
  set U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun s => (s - 1) * etaPair s) U :=
    ((differentiableOn_id.sub_const 1).mul differentiableOn_etaPair).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta₁ s) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine DifferentiableOn.mul ?_ differentiable_riemannZeta₁.differentiableOn
    refine (differentiableOn_const _).sub (DifferentiableOn.const_mul ?_ _)
    intro w _
    exact ((differentiableAt_neg_iff.2 differentiableAt_id).const_cpow
      (Or.inl two_ne_zero)).differentiableWithinAt
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have hev : (fun s => (s - 1) * etaPair s) =ᶠ[𝓝 (2 : ℂ)]
      (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta₁ s) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with w hw
    have hw1 : w ≠ 1 := by
      rintro rfl; simp at hw
    have hw' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
    rw [etaPair_eq_of_one_lt hw, riemannZeta_eq_inv_sub_mul hw1]
    field_simp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU h2 hev hs

/-- The real eta pairs at `s = 1/2`. -/
noncomputable def etaHalfTerm (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) - (2 * n + 2 : ℝ) ^ (-(1 / 2 : ℝ))

lemma etaTerm_half (n : ℕ) : etaTerm (1 / 2) n = (etaHalfTerm n : ℂ) := by
  simp only [etaTerm, etaHalfTerm, Complex.ofReal_sub]
  rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
  push_cast
  ring_nf

lemma etaHalfTerm_pos (n : ℕ) : 0 < etaHalfTerm n := by
  unfold etaHalfTerm
  have := Real.rpow_lt_rpow_of_neg (x := 2 * (n : ℝ) + 1) (y := 2 * n + 2) (by positivity)
    (by linarith) (by norm_num : -(1 / 2 : ℝ) < 0)
  linarith

lemma etaPair_half : etaPair (1 / 2) = ((∑' n, etaHalfTerm n : ℝ) : ℂ) := by
  rw [etaPair, tsum_congr etaTerm_half, Complex.ofReal_tsum]

lemma etaHalf_pos : 0 < ∑' n, etaHalfTerm n := by
  have hs : Summable etaHalfTerm := by
    have := summable_etaTerm (s := 1 / 2) (by norm_num)
    rw [show etaTerm (1 / 2) = fun n => (etaHalfTerm n : ℂ) from funext etaTerm_half] at this
    exact Complex.summable_ofReal.1 this
  exact hs.tsum_pos (fun n => (etaHalfTerm_pos n).le) 0 (etaHalfTerm_pos 0)

/-- `2 · 2^{-1/2} = √2` as a complex number. -/
lemma two_mul_two_cpow_neg_half : 2 * (2 : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h : (2 : ℂ) ^ (-(1 / 2 : ℂ)) = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]; push_cast; ring_nf
  rw [h]
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  exact_mod_cast h2

/-- **`ζ(1/2)` is a negative real number.** Explicitly
`ζ(1/2) = η(1/2) / (1 - √2)` with `η(1/2) = ∑ₙ ((2n+1)^{-1/2} - (2n+2)^{-1/2}) > 0`. -/
theorem riemannZeta_half_eq :
    riemannZeta (1 / 2) = (((∑' n, etaHalfTerm n) / (1 - Real.sqrt 2) : ℝ) : ℂ) := by
  have hid := etaPair_identity (s := 1 / 2) (by norm_num)
  rw [riemannZeta_eq_inv_sub_mul (by norm_num : (1 / 2 : ℂ) ≠ 1)]
  have hz1 : riemannZeta₁ (1 / 2) =
      (1 - 2 * (2 : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * ((1 / 2 - 1) * etaPair (1 / 2)) := by
    have hne : (1 - 2 * (2 : ℂ) ^ (-(1 / 2 : ℂ))) ≠ 0 := by
      rw [two_mul_two_cpow_neg_half]
      intro h
      have : ((1 - Real.sqrt 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
      have h' : 1 - Real.sqrt 2 = 0 := by exact_mod_cast this
      have : Real.sqrt 2 = 1 := by linarith
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    rw [hid]; field_simp
  rw [hz1, two_mul_two_cpow_neg_half, etaPair_half]
  have hne : (1 - Real.sqrt 2 : ℝ) ≠ 0 := by
    intro h
    have : Real.sqrt 2 = 1 := by linarith
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hne' : ((1 : ℂ) - ((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hne
  push_cast
  field_simp

lemma one_sub_sqrt_two_neg : 1 - Real.sqrt 2 < 0 := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **`ζ(1/2) < 0`**: `ζ(1/2)` is the image of a negative real number. -/
theorem riemannZeta_half_real_neg : ∃ x : ℝ, x < 0 ∧ riemannZeta (1 / 2) = x :=
  ⟨_, div_neg_of_pos_of_neg etaHalf_pos one_sub_sqrt_two_neg, riemannZeta_half_eq⟩

theorem riemannZeta_half_re_neg : (riemannZeta (1 / 2)).re < 0 := by
  obtain ⟨x, hx, h⟩ := riemannZeta_half_real_neg
  rw [h, Complex.ofReal_re]; exact hx

theorem riemannZeta_half_im : (riemannZeta (1 / 2)).im = 0 := by
  obtain ⟨x, _, h⟩ := riemannZeta_half_real_neg
  rw [h, Complex.ofReal_im]

/-- **`ζ(1/2) ≠ 0`.** -/
theorem riemannZeta_half_ne_zero : riemannZeta (1 / 2) ≠ 0 := by
  intro h
  have := riemannZeta_half_re_neg
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

end ScrewRH
