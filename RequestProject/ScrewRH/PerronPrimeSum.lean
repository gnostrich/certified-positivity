module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import RequestProject.ScrewRH.PerronKernel
public import RequestProject.V5_1

@[expose] public section

/-!
# ScrewRH.PerronPrimeSum: the Perron integral of `F · kern` (blueprint lemma 2)

On the line `re z = 1` (i.e. `re (½ + z) = 3/2`),
`(1/2π) ∫_ℝ F(1 + iy) kern t (1 + iy) dy = primeSum t` for every real `t`.

Proof: expand `F(1 + iy) = ∑ Λ(n) n^{-(3/2 + iy)}`, swap sum and integral (the norms are
`Λ(n) n^{-3/2} e^t/(1+y²)`, summable times integrable), and apply `perron_kernel` with
`c = 1`, `x = t - log n` to each term.
-/

open Complex MeasureTheory ArithmeticFunction
open scoped Real

namespace ScrewRH

/-- The Perron integrand on the line `re z = 1`. -/
noncomputable def perronInt (x y : ℝ) : ℂ := cexp ((1 + y * I) * x) / (1 + y * I) ^ 2

lemma one_add_mul_I_ne_zero (y : ℝ) : (1 + y * I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

lemma norm_perronInt (x y : ℝ) : ‖perronInt x y‖ = Real.exp x * (1 + y ^ 2)⁻¹ := by
  unfold perronInt
  rw [norm_div, Complex.norm_exp, norm_pow]
  have h1 : ((1 + y * I) * (x : ℂ)).re = x := by simp
  have h2 : ‖(1 + y * I : ℂ)‖ ^ 2 = 1 + y ^ 2 := by
    rw [← ofReal_one, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    ring
  rw [h1, h2, div_eq_mul_inv]

lemma continuous_perronInt (x : ℝ) : Continuous (perronInt x) := by
  unfold perronInt
  refine Continuous.div (by fun_prop) (by fun_prop) (fun y => pow_ne_zero 2 ?_)
  exact one_add_mul_I_ne_zero y

lemma integrable_perronInt (x : ℝ) : Integrable (perronInt x) := by
  refine (integrable_inv_one_add_sq.const_mul (Real.exp x)).mono'
    (continuous_perronInt x).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_perronInt]

lemma perron_kernel_one (x : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ y : ℝ, perronInt x y = ((max x 0 : ℝ) : ℂ) := by
  have := perron_kernel (c := 1) one_pos x
  rw [ofReal_one] at this
  exact this

/-- The `n`-th term of the expanded integrand. -/
noncomputable def primeTerm (t : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  ((Λ n / Real.sqrt n : ℝ) : ℂ) * perronInt (t - Real.log n) y

lemma term_mul_kern (t y : ℝ) (n : ℕ) :
    LSeries.term (fun n => (Λ n : ℂ)) (1 / 2 + (1 + y * I)) n * kern t (1 + y * I) =
      primeTerm t n y := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeTerm]
  rw [LSeries.term_of_ne_zero hn]
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set L := Real.log n with hL
  have hlog : Complex.log (n : ℂ) = (L : ℂ) := by
    rw [hL, ← ofReal_natCast, ofReal_log hpos.le]
  have hcpow : (n : ℂ) ^ (1 / 2 + (1 + y * I)) = cexp (L * (1 / 2 + (1 + y * I))) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hn), hlog]
  have hsqrt : Real.sqrt n = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, hL]
    ring_nf
  unfold primeTerm perronInt kern
  rw [hcpow, ofReal_div, hsqrt, ofReal_exp]
  have hz := one_add_mul_I_ne_zero y
  have e1 : cexp (L * (1 / 2 + (1 + y * I))) = cexp ((L / 2 : ℝ) : ℂ) * cexp ((1 + y * I) * L) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : cexp ((1 + y * I) * ((t - L : ℝ) : ℂ)) = cexp ((1 + y * I) * t) / cexp ((1 + y * I) * L) := by
    rw [← Complex.exp_sub]; congr 1; push_cast; ring
  rw [e1, e2]
  field_simp

lemma integrand_eq_tsum (t y : ℝ) :
    F (1 + y * I) * kern t (1 + y * I) = ∑' n, primeTerm t n y := by
  have hs : 1 < (1 / 2 + (1 + y * I) : ℂ).re := by norm_num
  have hF : F (1 + y * I) = LSeries (fun n => (Λ n : ℂ)) (1 / 2 + (1 + y * I)) := by
    rw [F, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div]
  rw [hF, LSeries, ← tsum_mul_right]
  exact tsum_congr fun n => term_mul_kern t y n

lemma integrable_primeTerm (t : ℝ) (n : ℕ) : Integrable (primeTerm t n) :=
  (integrable_perronInt _).const_mul _

lemma integral_norm_primeTerm (t : ℝ) (n : ℕ) :
    ∫ y, ‖primeTerm t n y‖ = Real.exp t * π * ‖LSeries.term (fun n => (Λ n : ℂ)) (3 / 2) n‖ := by
  have h : ∀ y, ‖primeTerm t n y‖ =
      (|Λ n / Real.sqrt n| * Real.exp (t - Real.log n)) * (1 + y ^ 2)⁻¹ := by
    intro y
    rw [primeTerm, norm_mul, norm_perronInt, Complex.norm_real, Real.norm_eq_abs]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_univ_inv_one_add_sq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [hn, ite_false]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.exp_sub, Real.exp_log hpos]
  have h32 : ((3 / 2 : ℂ)).re = 1 + 1 / 2 := by norm_num
  rw [h32, Real.rpow_add hpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have : 0 < Real.sqrt n := Real.sqrt_pos.2 hpos
  field_simp

lemma summable_integral_norm_primeTerm (t : ℝ) :
    Summable fun n => ∫ y, ‖primeTerm t n y‖ := by
  simp_rw [integral_norm_primeTerm]
  have hs : 1 < ((3 / 2 : ℂ)).re := by norm_num
  exact (LSeriesSummable_vonMangoldt hs).norm.mul_left _

lemma max_term_eq (t : ℝ) (n : ℕ) :
    Λ n / Real.sqrt n * max (t - Real.log n) 0 =
      if n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊ then Λ n / Real.sqrt n * (t - Real.log n) else 0 := by
  split_ifs with h
  · obtain ⟨h2, hN⟩ := Finset.mem_Icc.1 h
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hle : (n : ℝ) ≤ Real.exp t := (Nat.le_floor_iff (Real.exp_pos t).le).1 hN
    have : Real.log n ≤ t := by
      rw [Real.log_le_iff_le_exp hpos]; exact hle
    rw [max_eq_left (by linarith)]
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · interval_cases n <;> simp
    · have hlt : Real.exp t < n := Nat.lt_of_floor_lt h
      have hpos : (0 : ℝ) < n := (Real.exp_pos t).trans hlt
      have : t < Real.log n := by
        rw [Real.lt_log_iff_exp_lt hpos]; exact hlt
      rw [max_eq_right (by linarith), mul_zero]

/-- **Blueprint lemma 2 (Perron formula for the prime sum).** On the line `re z = 1`
(`re (½ + z) = 3/2`), for every real `t`,
`(1/2π) ∫_ℝ F(1 + iy) · kern t (1 + iy) dy = primeSum t`. -/
theorem perron_primeSum (t : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ y : ℝ, F (1 + y * I) * kern t (1 + y * I) =
      ((V5_1.primeSum t : ℝ) : ℂ) := by
  simp_rw [integrand_eq_tsum]
  rw [← integral_tsum_of_summable_integral_norm (integrable_primeTerm t)
    (summable_integral_norm_primeTerm t), ← tsum_mul_left]
  have h : ∀ n : ℕ, (1 / (2 * π) : ℂ) * ∫ y, primeTerm t n y =
      ((if n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊ then
        Λ n / Real.sqrt n * (t - Real.log n) else 0 : ℝ) : ℂ) := by
    intro n
    rw [← max_term_eq]
    unfold primeTerm
    rw [integral_const_mul, mul_left_comm, perron_kernel_one]
    push_cast
    rfl
  simp_rw [h]
  rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp t⌋₊) (fun n hn => by simp [hn]),
    V5_1.primeSum]
  push_cast
  exact Finset.sum_congr rfl fun n hn => by simp [hn]

end ScrewRH
