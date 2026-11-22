-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib
public import AlpogeRH.Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaTendstoLogSubHarmonic

@[expose] public section

namespace GlobalTheory.CompanionTheory.DigammaBound

open Finset

lemma add_half_le_norm (z : ℂ) (hz : 1 / 2 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    x + 1 / 2 ≤ ‖z + (x : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (z + (x : ℂ))
  have h2 : (z + (x : ℂ)).re = z.re + x := by simp
  rw [h2] at h
  have := le_abs_self (z.re + x)
  linarith

lemma term_eq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ =
      ‖z‖ / (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) hk
  have h2 : z + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    linarith
  have h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [← hc]
    exact_mod_cast Nat.succ_ne_zero k
  rw [hc]
  have : 1 / (((k : ℝ) + 1 : ℝ) : ℂ) - 1 / (z + (((k : ℝ) + 1 : ℝ) : ℂ)) =
      z / ((((k : ℝ) + 1 : ℝ) : ℂ) * (z + (((k : ℝ) + 1 : ℝ) : ℂ))) := by
    field_simp
    ring
  rw [this, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]

lemma term_le_two (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ 2 * ((k : ℝ) + 1)⁻¹ := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  have hz' : ‖z‖ ≤ ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ + ((k : ℝ) + 1) := by
    have h := norm_sub_le (z + (((k : ℝ) + 1 : ℝ) : ℂ)) (((k : ℝ) + 1 : ℝ) : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha.le] at h
    exact h
  have hNpos : 0 < ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : 2 * ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) =
      2 * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by
    field_simp
  rw [this]
  linarith

lemma term_le_sq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ ‖z‖ / ((k : ℝ) + 1) ^ 2 := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  apply div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
  nlinarith

lemma sum_terms_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (hn : M ≤ n) :
    ∑ i ∈ range n, ‖1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))‖ ≤
      2 * ∑ i ∈ range M, ((i : ℝ) + 1)⁻¹ + ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [sub_self, mul_zero, add_zero, mul_sum]
    exact sum_le_sum fun i _ => term_le_two z hz i
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have ht := term_le_sq z hz n
    have htel : ‖z‖ / ((n : ℝ) + 1) ^ 2 ≤ ‖z‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [this]
      apply inv_anti₀ (by positivity)
      nlinarith
    push_cast
    nlinarith [ih, ht, htel]

lemma harmonic_cast (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]

lemma partial_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (hzM : ‖z‖ ≤ M)
    (n : ℕ) (hn : M ≤ n) :
    ‖((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ))‖ ≤
      6 + 2 * Real.log M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hn1 : 1 ≤ n := hM.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set H : ℝ := ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ with hH
  have hlow : Real.log n ≤ H := by
    have h := log_add_one_le_harmonic n
    rw [harmonic_cast] at h
    have h2 : Real.log n ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hn0 (by linarith)
    push_cast at h
    linarith
  have hup : H ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_cast] at h
    exact h
  have hHc : ((H : ℝ) : ℂ) = ∑ i ∈ range n, 1 / ((i : ℂ) + 1) := by
    rw [hH]
    push_cast
    simp
  have hdecomp : ((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ)) =
      ((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))) - 1 / z := by
    rw [sum_range_succ', sum_sub_distrib, ← hHc]
    push_cast
    simp only [add_zero]
    ring
  have h1 : ‖((Real.log n - H : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h2 : ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ ≤
      2 * (1 + Real.log M) + 1 := by
    refine (norm_sum_le _ _).trans ((sum_terms_le z hz M hM n hn).trans ?_)
    have hHM := harmonic_le_one_add_log M
    rw [harmonic_cast] at hHM
    have h3 : ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) ≤ 1 := by
      have h4 : ‖z‖ * (1 / (M : ℝ)) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hM0).2 hzM
      have h5 : 0 ≤ ‖z‖ * (1 / (n : ℝ)) := by positivity
      rw [mul_sub]
      linarith
    linarith
  have h3 : ‖1 / z‖ ≤ 2 := by
    have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  rw [hdecomp]
  calc _ ≤ ‖((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ ‖((Real.log n - H : ℝ) : ℂ)‖ +
        ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 + 2 * Real.log M := by linarith

theorem digamma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  refine ⟨11, by norm_num, fun z hz => ?_⟩
  have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  set M : ℕ := ⌈‖z‖⌉₊ + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hzM : ‖z‖ ≤ M := by
    rw [hMdef]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hMle : (M : ℝ) ≤ ‖z‖ + 2 := by
    rw [hMdef]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogM : Real.log M ≤ Real.log (‖z‖ + 2) := Real.log_le_log hM0 hMle
  have hlim := (GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma z (by linarith)).norm
  have hbd : ‖Complex.digamma z‖ ≤ 6 + 2 * Real.log M :=
    le_of_tendsto hlim ((Filter.eventually_ge_atTop M).mono fun n hn =>
      partial_le z hz M hM hzM n hn)
  have hL : (2 : ℝ) / 3 ≤ Real.log (‖z‖ + 2) := by
    have h2 : Real.log 2 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  linarith

end GlobalTheory.CompanionTheory.DigammaBound
