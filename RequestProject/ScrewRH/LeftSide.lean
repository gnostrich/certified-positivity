module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import RequestProject.V5_1
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope
public import AlpogeRH.Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlaneStatement
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive

@[expose] public section

/-!
# ScrewRH.LeftSide: `F` on the left half plane (blueprint lemmas 4 and 8)

Interface (namespace `ScrewRH`). Write `sig K = -(2K + 3/2)` and `pk k = -(2(k+1) + 1/2)`.
* `FL z = logDeriv ζ (½ - z) - log (2π) + ψ (½ - z) - (π/2) tan (π (½ - z)/2)`,
  `fkL t z = FL z * kern t z`.
* `F_eq_FL` (`½ - z ∉ ℤ`, `ζ (½ - z) ≠ 0`), `F_eq_FL_of_re_le` (`re z ≤ -1/2`, `½ - z ∉ ℤ`),
  `F_eq_FL_of_re_eq` / `fk_eq_fkL_of_re_eq` (`re z = -1`): `F = FL` (so the shared edge cancels).
* `analyticAt_FL`, `analyticAt_fkL`: analytic at `z` if `re z < -1/2` and `z ≠ -(2k + 1/2)`.
* `FL_expansion k`, `fkL_expansion t k`: simple pole at `pk k`, residues `-1` resp.
  `-kern t (pk k)`, in the format of `GlobalTheory.ResRect.residue_rectangle`.
* `left_rect_identity t K hT`: `bdInt (sig K) (-1) (-T) T (fkL t) =
  2πi · -∑ k ∈ range K, kern t (pk k)` (for every `T > 0`; no zeros of `ζ` are involved).
* `norm_fkL_le`, `norm_fkL_vertical_le`, `norm_integral_left_horizontal_le`: bounds
  `‖fkL t z‖ ≤ A e^{t re z} (1 + ‖z‖)^{-3/2}` where `re z ≤ -1` and `‖tan‖ ≤ 2`
  (true on `re z = sig K` and on `|im z| ≥ 1`).
* `tendsto_left_horizontal_top/bot`: for `t ≥ 0`, `a ≤ -1`,
  `∫ x in a..-1, fkL t (x ± T i) → 0` as `T → ∞`.
* `integrable_fkL_vertical t K` and **`left_limit_K`** (`t > 0`):
  `∫ y : ℝ, fkL t (sig K + y i) → 0` as `K → ∞`.
* `trivial_sum t ht` / `tendsto_trivial_partial`: for `t ≥ 0`,
  `∑ k, kern t (pk k) = ((¼ e^{-t/2} (V5_1.L t - 16) : ℝ) : ℂ)`.

The ported Alpöge infrastructure (`logDeriv_pole`, the digamma bound, `residue_rectangle`) is
credited to Levent Alpöge (used with permission).
-/

open Complex Filter Topology MeasureTheory

namespace ScrewRH

/-- The left-half-plane expression for `F`, from the functional equation. -/
noncomputable def FL (z : ℂ) : ℂ :=
  logDeriv riemannZeta (1 / 2 - z) - Complex.log (2 * Real.pi) + Complex.digamma (1 / 2 - z) -
    Real.pi / 2 * Complex.tan (Real.pi * (1 / 2 - z) / 2)

/-- `FL · kern t`. -/
noncomputable def fkL (t : ℝ) (z : ℂ) : ℂ := FL z * kern t z

theorem F_eq_neg_logDeriv (z : ℂ) : F z = -logDeriv riemannZeta (1 / 2 + z) := by
  rw [F, logDeriv_apply]

/-- **Blueprint lemma 4**: `F = FL` where the functional equation applies. -/
theorem F_eq_FL {z : ℂ} (hz : ∀ n : ℤ, 1 / 2 - z ≠ n) (hζ : riemannZeta (1 / 2 - z) ≠ 0) :
    F z = FL z := by
  have h := logDeriv_riemannZeta_one_sub hz hζ
  have e : (1 : ℂ) - (1 / 2 - z) = 1 / 2 + z := by ring
  rw [e] at h
  rw [F_eq_neg_logDeriv, FL]
  linear_combination -h

theorem F_eq_FL_of_re_le {z : ℂ} (hre : z.re ≤ -1 / 2) (hz : ∀ n : ℤ, 1 / 2 - z ≠ n) :
    F z = FL z :=
  F_eq_FL hz (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))

theorem F_eq_FL_of_re_eq {z : ℂ} (hre : z.re = -1) : F z = FL z := by
  refine F_eq_FL_of_re_le (by rw [hre]; norm_num) (fun n h => ?_)
  have := congrArg Complex.re h
  simp [hre] at this
  have h2 : (n : ℝ) = 3 / 2 := by linarith
  have h3 : (2 * n : ℤ) = 3 := by exact_mod_cast (by linarith : (2 * (n : ℝ)) = 3)
  omega

theorem fk_eq_fkL_of_re_eq (t : ℝ) {z : ℂ} (hre : z.re = -1) :
    F z * kern t z = fkL t z := by
  rw [fkL, F_eq_FL_of_re_eq hre]

/-! ### The trivial-zero residue sum -/

theorem kern_trivial (t : ℝ) (k : ℕ) :
    kern t (-(2 * ((k : ℂ) + 1) + 1 / 2)) =
      (((1 / 4 * Real.exp (-t / 2)) *
        (Real.exp (-2 * ((k + 1 : ℕ) : ℝ) * t) * (1 / (((k + 1 : ℕ) : ℝ) + 1 / 4) ^ 2)) : ℝ) : ℂ) := by
  unfold kern
  push_cast
  have h1 : Complex.exp (-(2 * ((k : ℂ) + 1) + 1 / 2) * t) =
      Complex.exp (-t / 2) * Complex.exp (-2 * ((k : ℂ) + 1) * t) := by
    rw [← Complex.exp_add]; ring_nf
  rw [h1]
  have h2 : (-(2 * ((k : ℂ) + 1) + 1 / 2)) ^ 2 = 4 * (((k : ℂ) + 1) + 1 / 4) ^ 2 := by ring
  rw [h2]
  have h3 : ((k : ℂ) + 1) + 1 / 4 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  field_simp

theorem trivial_sum (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => kern t (-(2 * ((k : ℂ) + 1) + 1 / 2)))
      (((1 / 4 * Real.exp (-t / 2) * (V5_1.L t - 16)) : ℝ) : ℂ) := by
  simp_rw [kern_trivial]
  refine Complex.hasSum_ofReal.2 ?_
  refine HasSum.mul_left _ ?_
  have hs := (V5_1.summable_L t ht).hasSum
  have h := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_mul,
    Real.exp_zero, one_mul, zero_add] at h
  convert h using 2
  unfold V5_1.L; norm_num
  norm_num

/-! ### Bounds for `tan` -/

theorem tan_eq_exp (w : ℂ) :
    Complex.tan w = I * (1 - Complex.exp (2 * w * I)) / (1 + Complex.exp (2 * w * I)) := by
  set a := Complex.exp (w * I) with ha
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  have e1 : Complex.exp (2 * w * I) = a ^ 2 := by
    rw [ha, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have e2 : Complex.exp (-w * I) = a⁻¹ := by rw [ha, ← Complex.exp_neg]; ring_nf
  rw [Complex.tan_eq_sin_div_cos, Complex.sin, Complex.cos, e1, e2]
  have h1 : (a⁻¹ - a) = (1 - a ^ 2) / a := by field_simp
  have h2 : (a + a⁻¹) = (1 + a ^ 2) / a := by field_simp; ring
  rw [h1, h2]
  by_cases hc : 1 + a ^ 2 = 0
  · simp [hc]
  · field_simp

theorem norm_exp_two_mul_I (w : ℂ) : ‖Complex.exp (2 * w * I)‖ = Real.exp (-2 * w.im) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem norm_tan_le_of_norm_q {w : ℂ} (h : ‖Complex.exp (2 * w * I)‖ ≤ 1 / 3) :
    ‖Complex.tan w‖ ≤ 2 := by
  rw [tan_eq_exp, norm_div, norm_mul, Complex.norm_I, one_mul]
  set q := Complex.exp (2 * w * I)
  have h1 : ‖1 - q‖ ≤ 1 + ‖q‖ := by
    calc ‖1 - q‖ ≤ ‖(1 : ℂ)‖ + ‖q‖ := norm_sub_le _ _
      _ = 1 + ‖q‖ := by rw [norm_one]
  have h2 : 1 - ‖q‖ ≤ ‖1 + q‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-q)
    simp only [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have h3 : 0 < ‖1 + q‖ := by linarith
  rw [div_le_iff₀ h3]
  linarith

theorem exp_neg_pi_le : Real.exp (-Real.pi) ≤ 1 / 3 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp Real.pi
  linarith [Real.pi_gt_three]

theorem norm_tan_le_two {w : ℂ} (h : Real.pi / 2 ≤ |w.im|) : ‖Complex.tan w‖ ≤ 2 := by
  rcases le_abs'.1 h with h' | h'
  · have : ‖Complex.tan (-w)‖ ≤ 2 := by
      refine norm_tan_le_of_norm_q ?_
      rw [norm_exp_two_mul_I]
      refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_pi_le
      simp; linarith
    rwa [Complex.tan_neg, norm_neg] at this
  · refine norm_tan_le_of_norm_q ?_
    rw [norm_exp_two_mul_I]
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_pi_le
    linarith

theorem norm_tan_le_one_of_re {w : ℂ} (k : ℤ) (h : w.re = k * Real.pi) : ‖Complex.tan w‖ ≤ 1 := by
  have hq : Complex.exp (2 * w * I) = ((Real.exp (-2 * w.im) : ℝ) : ℂ) := by
    have e : 2 * w * I = ((-2 * w.im : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * I) := by
      apply Complex.ext
      · simp [h]
      · simp [h]; ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.ofReal_exp]
  rw [tan_eq_exp, hq, norm_div, norm_mul, Complex.norm_I, one_mul]
  set r := Real.exp (-2 * w.im)
  have hr : 0 < r := Real.exp_pos _
  have e1 : ‖(1 : ℂ) - (r : ℂ)‖ = |1 - r| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have e2 : ‖(1 : ℂ) + (r : ℂ)‖ = 1 + r := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  rw [e1, e2, div_le_one (by linarith), abs_le]
  constructor <;> linarith

/-! ### Bounds for `logDeriv ζ` and `ψ` -/

open ArithmeticFunction in
theorem norm_logDeriv_zeta_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 3 / 2 ≤ w.re →
    ‖logDeriv riemannZeta w‖ ≤ B := by
  have h32 : (1 : ℝ) < ((3 / 2 : ℝ) : ℂ).re := by simp; norm_num
  have hsum : Summable (fun n => ‖LSeries.term (fun n : ℕ => (Λ n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt h32)
  refine ⟨∑' n, ‖LSeries.term (fun n : ℕ => (Λ n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖,
    tsum_nonneg (fun _ => norm_nonneg _), fun w hw => ?_⟩
  have hw1 : 1 < w.re := by linarith
  rw [logDeriv_apply, ← neg_neg (deriv riemannZeta w / riemannZeta w), ← neg_div,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw1, norm_neg]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun n => ?_) ?_ hsum)
  · exact summable_norm_iff.mpr (LSeriesSummable_vonMangoldt hw1)
  · exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hw) n
  · exact summable_norm_iff.mpr (LSeriesSummable_vonMangoldt hw1)

/-- Bound for `FL` on the part of the left half plane where the `tan` term is bounded. -/
theorem norm_FL_le : ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, z.re ≤ -1 →
    ‖Complex.tan (Real.pi * (1 / 2 - z) / 2)‖ ≤ 2 →
    ‖FL z‖ ≤ A * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := norm_logDeriv_zeta_le
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  set L2 := ‖Complex.log (2 * Real.pi)‖
  refine ⟨B + L2 + 4 * C + Real.pi, by positivity, fun z hz htan => ?_⟩
  set S := (1 + ‖z‖) ^ (1 / 2 : ℝ)
  have hS1 : 1 ≤ S := Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  have hw : (1 / 2 - z).re = 1 / 2 - z.re := by simp
  have h1 : ‖logDeriv riemannZeta (1 / 2 - z)‖ ≤ B := hB _ (by rw [hw]; linarith)
  have h2 : ‖Complex.digamma (1 / 2 - z)‖ ≤ C * Real.log (‖1 / 2 - z‖ + 2) :=
    hC _ (by rw [hw]; linarith)
  have hnorm : ‖1 / 2 - z‖ ≤ ‖z‖ + 1 := by
    calc ‖1 / 2 - z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + 1 := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        linarith
  have hlog : Real.log (‖1 / 2 - z‖ + 2) ≤ 4 * S := by
    have := Real.log_le_rpow_div (x := ‖1 / 2 - z‖ + 2) (ε := 1 / 2) (by positivity)
      (by norm_num)
    have h3 : (‖1 / 2 - z‖ + 2) ^ (1 / 2 : ℝ) ≤ (4 * (1 + ‖z‖)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg z]) (by norm_num)
    have h4 : (4 * (1 + ‖z‖)) ^ (1 / 2 : ℝ) = 2 * S := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have h5 : ‖(Real.pi : ℂ) / 2 * Complex.tan (Real.pi * (1 / 2 - z) / 2)‖ ≤ Real.pi := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [this]
    nlinarith [Real.pi_pos]
  unfold FL
  calc _ ≤ ‖logDeriv riemannZeta (1 / 2 - z)‖ + L2 + ‖Complex.digamma (1 / 2 - z)‖ +
        ‖(Real.pi : ℂ) / 2 * Complex.tan (Real.pi * (1 / 2 - z) / 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ B + L2 + C * (4 * S) + Real.pi := by
        gcongr
        exact h2.trans (by gcongr)
    _ ≤ (B + L2 + 4 * C + Real.pi) * S := by
        have : 0 ≤ L2 := norm_nonneg _
        nlinarith [Real.pi_pos]

/-! ### Analyticity of `FL` -/

theorem analyticAt_zeta {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ riemannZeta w := by
  have : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt)
      isOpen_compl_singleton
  exact this w hw

theorem analyticAt_Gamma {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Complex.Gamma w := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have : AnalyticOnNhd ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hopen
    refine (Complex.differentiableAt_Gamma s fun m h => ?_).differentiableWithinAt
    have : s.re = -(m : ℝ) := by rw [h]; simp
    simp only [Set.mem_ofPred_eq] at hs
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  exact this w hw

theorem analyticAt_digamma {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Complex.digamma w := by
  have h := analyticAt_Gamma hw
  have : Complex.digamma = fun s => deriv Complex.Gamma s / Complex.Gamma s := by
    funext s; rw [Complex.digamma_def, logDeriv_apply]
  rw [this]
  exact h.deriv.div h (Complex.Gamma_ne_zero_of_re_pos hw)

theorem analyticAt_logDeriv_zeta {w : ℂ} (hw : 1 < w.re) :
    AnalyticAt ℂ (logDeriv riemannZeta) w := by
  have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
  have h := analyticAt_zeta hw1
  have : logDeriv riemannZeta = fun s => deriv riemannZeta s / riemannZeta s := by
    funext s; rw [logDeriv_apply]
  rw [this]
  exact h.deriv.div h (riemannZeta_ne_zero_of_one_le_re hw.le)

theorem analyticAt_tan {u : ℂ} (hu : Complex.cos u ≠ 0) : AnalyticAt ℂ Complex.tan u := by
  have : Complex.tan = fun s => Complex.sin s / Complex.cos s := by
    funext s; rw [Complex.tan_eq_sin_div_cos]
  rw [this]
  exact (Complex.analyticAt_sin).div Complex.analyticAt_cos hu

/-- The analytic part of `FL` (everything except the `tan` term). -/
noncomputable def FLreg (z : ℂ) : ℂ :=
  logDeriv riemannZeta (1 / 2 - z) - Complex.log (2 * Real.pi) + Complex.digamma (1 / 2 - z)

theorem FL_eq (z : ℂ) : FL z = FLreg z - Real.pi / 2 * Complex.tan (Real.pi * (1 / 2 - z) / 2) :=
  rfl

theorem analyticAt_FLreg {z : ℂ} (hre : z.re < -1 / 2) : AnalyticAt ℂ FLreg z := by
  have hw : (1 / 2 - z).re = 1 / 2 - z.re := by simp
  have haff : AnalyticAt ℂ (fun z : ℂ => 1 / 2 - z) z := analyticAt_const.sub analyticAt_id
  have h1 : AnalyticAt ℂ (fun z => logDeriv riemannZeta (1 / 2 - z)) z :=
    (analyticAt_logDeriv_zeta (by rw [hw]; linarith)).comp haff
  have h2 : AnalyticAt ℂ (fun z => Complex.digamma (1 / 2 - z)) z :=
    (analyticAt_digamma (by rw [hw]; linarith)).comp haff
  exact (h1.sub analyticAt_const).add h2

theorem cos_ne_zero_of_ne {z : ℂ} (hre : z.re < -1 / 2)
    (hz : ∀ k : ℕ, z ≠ -(2 * (k : ℂ) + 1 / 2)) :
    Complex.cos (Real.pi * (1 / 2 - z) / 2) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.cos_eq_zero_iff.1 h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz' : z = -(2 * (n : ℂ) + 1 / 2) := by
    have : (Real.pi : ℂ) * ((1 / 2 - z) - (2 * n + 1)) = 0 := by linear_combination 2 * hn
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hpi
    · linear_combination -h0
  have hre' : z.re = -(2 * (n : ℝ) + 1 / 2) := by rw [hz']; simp
  have hn0 : 0 ≤ n := by
    by_contra hneg
    push Not at hneg
    have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    linarith
  apply hz n.toNat
  rw [hz']
  congr
  have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
  exact_mod_cast this.symm

theorem analyticAt_FL {z : ℂ} (hre : z.re < -1 / 2)
    (hz : ∀ k : ℕ, z ≠ -(2 * (k : ℂ) + 1 / 2)) : AnalyticAt ℂ FL z := by
  have haff : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * (1 / 2 - z) / 2) z := by fun_prop
  have ht : AnalyticAt ℂ (fun z => Complex.tan (Real.pi * (1 / 2 - z) / 2)) z :=
    AnalyticAt.comp (g := Complex.tan) (f := fun z : ℂ => (Real.pi : ℂ) * (1 / 2 - z) / 2)
      (analyticAt_tan (cos_ne_zero_of_ne hre hz)) haff
  have : FL = fun z => FLreg z - Real.pi / 2 * Complex.tan (Real.pi * (1 / 2 - z) / 2) := by
    funext z; rfl
  rw [this]
  exact (analyticAt_FLreg hre).sub (analyticAt_const.mul ht)

theorem analyticAt_kern' (t : ℝ) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (kern t) z := by
  unfold kern
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.exp (z * t)) z).div (by fun_prop)
    (pow_ne_zero 2 hz)

theorem analyticAt_fkL (t : ℝ) {z : ℂ} (hre : z.re < -1 / 2)
    (hz : ∀ k : ℕ, z ≠ -(2 * (k : ℂ) + 1 / 2)) : AnalyticAt ℂ (fkL t) z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hre; simp at hre; linarith
  exact (analyticAt_FL hre hz).mul (analyticAt_kern' t hz0)

/-! ### Bounds for `fkL` -/

theorem norm_kern_eq (t : ℝ) (z : ℂ) : ‖kern t z‖ = Real.exp (t * z.re) / ‖z‖ ^ 2 := by
  unfold kern
  rw [norm_div, norm_pow, Complex.norm_exp]
  congr 2
  simp [mul_comm]

theorem norm_fkL_le : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ∀ z : ℂ, z.re ≤ -1 →
    ‖Complex.tan (Real.pi * (1 / 2 - z) / 2)‖ ≤ 2 →
    ‖fkL t z‖ ≤ A * Real.exp (t * z.re) * (1 + ‖z‖) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨A, hA, h⟩ := norm_FL_le
  refine ⟨4 * A, by positivity, fun t z hz htan => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [abs_of_neg (by linarith)] at this
    linarith
  set N := ‖z‖
  have hN : 0 < 1 + N := by linarith
  rw [fkL, norm_mul, norm_kern_eq]
  have hsq : (1 + N) ^ (2 : ℝ) / 4 ≤ N ^ 2 := by
    rw [Real.rpow_two]; nlinarith
  have key : (1 + N) ^ (1 / 2 : ℝ) / N ^ 2 ≤ 4 * (1 + N) ^ (-(3 / 2 : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have e : (1 + N) ^ (1 / 2 : ℝ) = (1 + N) ^ (-(3 / 2 : ℝ)) * (1 + N) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hN]; norm_num
    rw [e]
    have : 0 ≤ (1 + N) ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith
  calc ‖FL z‖ * (Real.exp (t * z.re) / N ^ 2)
      ≤ A * (1 + N) ^ (1 / 2 : ℝ) * (Real.exp (t * z.re) / N ^ 2) := by
        gcongr; exact h z hz htan
    _ = A * Real.exp (t * z.re) * ((1 + N) ^ (1 / 2 : ℝ) / N ^ 2) := by ring
    _ ≤ A * Real.exp (t * z.re) * (4 * (1 + N) ^ (-(3 / 2 : ℝ))) := by gcongr
    _ = 4 * A * Real.exp (t * z.re) * (1 + N) ^ (-(3 / 2 : ℝ)) := by ring

/-- The left vertical line `re z = -2K - 3/2`. -/
noncomputable def sig (K : ℕ) : ℝ := -(2 * (K : ℝ) + 3 / 2)

theorem tan_bound_vertical (K : ℕ) (y : ℝ) :
    ‖Complex.tan (Real.pi * (1 / 2 - ((sig K : ℂ) + y * I)) / 2)‖ ≤ 2 := by
  refine (norm_tan_le_one_of_re ((K : ℤ) + 1) ?_).trans (by norm_num)
  simp [sig]; ring

theorem tan_bound_horizontal {x T : ℝ} (hT : 1 ≤ |T|) :
    ‖Complex.tan (Real.pi * (1 / 2 - ((x : ℂ) + T * I)) / 2)‖ ≤ 2 := by
  refine norm_tan_le_two ?_
  have : (Real.pi * (1 / 2 - ((x : ℂ) + T * I)) / 2 : ℂ).im = -(Real.pi * T / 2) := by
    simp; ring
  rw [this, abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  nlinarith [Real.pi_pos]

theorem norm_fkL_vertical_le : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ∀ K : ℕ, ∀ y : ℝ,
    ‖fkL t ((sig K : ℂ) + y * I)‖ ≤ A * Real.exp (t * sig K) * (1 + |y|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨A, hA, h⟩ := norm_fkL_le
  refine ⟨A, hA, fun t K y => ?_⟩
  have hre : ((sig K : ℂ) + y * I).re = sig K := by simp
  have hs : sig K ≤ -1 := by
    unfold sig; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)]
  refine (h t _ (by rw [hre]; exact hs) (tan_bound_vertical K y)).trans ?_
  rw [hre]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
  have := Complex.abs_im_le_norm ((sig K : ℂ) + y * I)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    zero_add, add_zero] at this
  linarith

theorem continuous_fkL_vertical (t : ℝ) (K : ℕ) :
    Continuous (fun y : ℝ => fkL t ((sig K : ℂ) + y * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hre : ((sig K : ℂ) + y * I).re < -1 / 2 := by
    simp [sig]; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)]
  have hz : ∀ k : ℕ, ((sig K : ℂ) + y * I) ≠ -(2 * (k : ℂ) + 1 / 2) := by
    intro k h
    have := congrArg Complex.re h
    simp [sig] at this
    have h2 : (2 * (K : ℤ) + 1 : ℤ) = 2 * k := by
      exact_mod_cast (by linarith : (2 * (K : ℝ) + 1) = 2 * k)
    omega
  exact ContinuousAt.comp (g := fkL t) (f := fun y : ℝ => (sig K : ℂ) + y * I)
    (analyticAt_fkL t hre hz).continuousAt (by fun_prop)

theorem integrable_rpow_one_add_abs :
    Integrable (fun y : ℝ => (1 + |y|) ^ (-(3 / 2 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2)
    (by simp; norm_num)
  simpa [Real.norm_eq_abs] using this

theorem integrable_fkL_vertical (t : ℝ) (K : ℕ) :
    Integrable (fun y : ℝ => fkL t ((sig K : ℂ) + y * I)) := by
  obtain ⟨A, -, h⟩ := norm_fkL_vertical_le
  refine Integrable.mono' ((integrable_rpow_one_add_abs).const_mul (A * Real.exp (t * sig K)))
    (continuous_fkL_vertical t K).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  simpa [mul_assoc] using h t K y

/-- **Blueprint lemma 8 (left line)**: the left vertical integral tends to `0`. -/
theorem left_limit_K {t : ℝ} (ht : 0 < t) :
    Tendsto (fun K : ℕ => ∫ y : ℝ, fkL t ((sig K : ℂ) + y * I)) atTop (𝓝 0) := by
  obtain ⟨A, hA, h⟩ := norm_fkL_vertical_le
  set I0 := ∫ y : ℝ, (1 + |y|) ^ (-(3 / 2 : ℝ))
  have hbound : ∀ K : ℕ, ‖∫ y : ℝ, fkL t ((sig K : ℂ) + y * I)‖ ≤
      A * I0 * Real.exp (t * sig K) := by
    intro K
    refine (norm_integral_le_of_norm_le
      ((integrable_rpow_one_add_abs).const_mul (A * Real.exp (t * sig K)))
      (ae_of_all _ fun y => h t K y)).trans (le_of_eq ?_)
    rw [integral_const_mul]; ring
  refine squeeze_zero_norm hbound ?_
  rw [show (0 : ℝ) = A * I0 * 0 by ring]
  refine Tendsto.const_mul _ ?_
  refine Real.tendsto_exp_atBot.comp ?_
  have : Tendsto (fun K : ℕ => sig K) atTop atBot := by
    unfold sig
    refine tendsto_neg_atTop_atBot.comp ?_
    refine tendsto_atTop_add_const_right _ _ ?_
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  exact this.const_mul_atBot ht

/-- Bound on the horizontal segments of the left rectangle. -/
theorem norm_integral_left_horizontal_le : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 0 ≤ t → ∀ a : ℝ, a ≤ -1 →
    ∀ T : ℝ, 1 ≤ |T| →
    ‖∫ x : ℝ in a..(-1), fkL t ((x : ℂ) + T * I)‖ ≤ A * (1 + |T|) ^ (-(3 / 2 : ℝ)) * (-1 - a) := by
  obtain ⟨A, hA, h⟩ := norm_fkL_le
  refine ⟨A, hA, fun t ht a ha T hT => ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := -1)
    (C := A * (1 + |T|) ^ (-(3 / 2 : ℝ))) (f := fun x : ℝ => fkL t ((x : ℂ) + T * I)) ?_
  · rw [abs_of_nonneg (show (0 : ℝ) ≤ -1 - a by linarith)] at this; exact this
  intro x hx
  rw [Set.uIoc_of_le ha] at hx
  have hre : ((x : ℂ) + T * I).re = x := by simp
  refine (h t _ (by rw [hre]; exact hx.2) (tan_bound_horizontal hT)).trans ?_
  rw [hre]
  have h1 : Real.exp (t * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hx.2])
  have h2 : (1 + ‖(x : ℂ) + T * I‖) ^ (-(3 / 2 : ℝ)) ≤ (1 + |T|) ^ (-(3 / 2 : ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
    have := Complex.abs_im_le_norm ((x : ℂ) + T * I)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      zero_add, add_zero] at this
    linarith
  calc A * Real.exp (t * x) * (1 + ‖(x : ℂ) + T * I‖) ^ (-(3 / 2 : ℝ))
      ≤ A * 1 * (1 + |T|) ^ (-(3 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

theorem tendsto_rpow_horizontal :
    Tendsto (fun T : ℝ => (1 + |T|) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => 1 + |T|) atTop atTop := by
    refine tendsto_atTop_add_const_left _ _ ?_
    exact tendsto_abs_atTop_atTop
  exact (tendsto_rpow_neg_atTop (by norm_num)).comp h1

/-- **Left horizontal edges vanish** as `T → ∞` (upper edge). -/
theorem tendsto_left_horizontal_top {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (ha : a ≤ -1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..(-1), fkL t ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  obtain ⟨A, hA, h⟩ := norm_integral_left_horizontal_le
  refine squeeze_zero_norm' (a := fun T : ℝ => A * (1 + |T|) ^ (-(3 / 2 : ℝ)) * (-1 - a)) ?_
    (by simpa using ((tendsto_rpow_horizontal.const_mul A).mul_const (-1 - a)))
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact h t ht a ha T (by rw [abs_of_nonneg (by linarith)]; exact hT)

/-- **Left horizontal edges vanish** as `T → ∞` (lower edge). -/
theorem tendsto_left_horizontal_bot {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (ha : a ≤ -1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..(-1), fkL t ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop
      (𝓝 0) := by
  obtain ⟨A, hA, h⟩ := norm_integral_left_horizontal_le
  refine squeeze_zero_norm' (a := fun T : ℝ => A * (1 + |T|) ^ (-(3 / 2 : ℝ)) * (-1 - a)) ?_
    (by simpa using ((tendsto_rpow_horizontal.const_mul A).mul_const (-1 - a)))
  filter_upwards [eventually_ge_atTop 1] with T hT
  have := h t ht a ha (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hT)
  rwa [abs_neg] at this

/-! ### The poles `-(2k + 1/2)`, `k ≥ 1` -/

/-- `cos (π (½ - s)/2)`; `(π/2) tan(π(½ - s)/2)` is its logarithmic derivative. -/
noncomputable def hcos (s : ℂ) : ℂ := Complex.cos (Real.pi * (1 / 2 - s) / 2)

theorem hasDerivAt_hcos (s : ℂ) :
    HasDerivAt hcos (-Complex.sin (Real.pi * (1 / 2 - s) / 2) * (Real.pi * (-1) / 2)) s := by
  have h : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) * (1 / 2 - s) / 2) (Real.pi * (-1) / 2) s :=
    (((hasDerivAt_id s).const_sub (1 / 2)).const_mul (Real.pi : ℂ)).div_const 2
  exact h.ccos

theorem tan_eq_logDeriv_hcos (s : ℂ) :
    (Real.pi : ℂ) / 2 * Complex.tan (Real.pi * (1 / 2 - s) / 2) = deriv hcos s / hcos s := by
  rw [(hasDerivAt_hcos s).deriv, hcos, Complex.tan_eq_sin_div_cos]
  ring

/-- The `k`-th trivial pole, `k ≥ 1` written as `k + 1`. -/
noncomputable def pk (k : ℕ) : ℂ := -(2 * ((k : ℂ) + 1) + 1 / 2)

theorem pk_re (k : ℕ) : (pk k).re = -(2 * ((k : ℝ) + 1) + 1 / 2) := by simp [pk]

theorem pk_im (k : ℕ) : (pk k).im = 0 := by simp [pk]

theorem hcos_pk (k : ℕ) : hcos (pk k) = 0 := by
  rw [hcos, Complex.cos_eq_zero_iff]
  exact ⟨(k : ℤ) + 1, by simp [pk]; ring⟩

theorem deriv_hcos_pk_ne (k : ℕ) : deriv hcos (pk k) ≠ 0 := by
  rw [(hasDerivAt_hcos _).deriv]
  have hc : Complex.cos (Real.pi * (1 / 2 - pk k) / 2) = 0 := hcos_pk k
  have hs : Complex.sin (Real.pi * (1 / 2 - pk k) / 2) ≠ 0 := by
    intro h
    have := Complex.sin_sq_add_cos_sq (Real.pi * (1 / 2 - pk k) / 2)
    rw [h, hc] at this
    norm_num at this
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine mul_ne_zero (neg_ne_zero.2 hs) ?_
  refine div_ne_zero (mul_ne_zero hpi (by norm_num)) (by norm_num)

theorem analyticAt_hcos (s : ℂ) : AnalyticAt ℂ hcos s := by
  unfold hcos; fun_prop

theorem analyticOrderAt_hcos (k : ℕ) : analyticOrderAt hcos (pk k) = (1 : ℕ) := by
  refine ((analyticAt_hcos _).analyticOrderAt_eq_natCast).2
    ⟨dslope hcos (pk k), GlobalTheory.ExplicitRect.analyticAt_dslope (analyticAt_hcos _), ?_,
      Eventually.of_forall fun s => ?_⟩
  · rw [dslope_same]; exact deriv_hcos_pk_ne k
  · have := GlobalTheory.ExplicitRect.eq_add_dslope hcos (pk k) s
    rw [hcos_pk, zero_add] at this
    rw [this, pow_one, smul_eq_mul]

theorem analyticOrderNatAt_hcos (k : ℕ) : analyticOrderNatAt hcos (pk k) = 1 := by
  simp [analyticOrderNatAt, analyticOrderAt_hcos]

theorem analyticOrderAt_hcos_ne_top (k : ℕ) : analyticOrderAt hcos (pk k) ≠ ⊤ := by
  rw [analyticOrderAt_hcos]; exact ENat.natCast_ne_top _

/-- `FL` has a simple pole with residue `-1` at `pk k`. -/
theorem FL_expansion (k : ℕ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (pk k) ∧
    ∀ᶠ s in 𝓝[≠] (pk k), FL s = (-1) / (s - pk k) + g s := by
  obtain ⟨g, hg, hφ⟩ := GlobalTheory.ExplicitRect.logDeriv_pole (analyticAt_hcos (pk k))
    (analyticOrderAt_hcos_ne_top k)
  rw [analyticOrderNatAt_hcos] at hφ
  have hre : (pk k).re < -1 / 2 := by
    rw [pk_re]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  refine ⟨fun s => FLreg s - g s, (analyticAt_FLreg hre).sub hg, ?_⟩
  filter_upwards [hφ] with s hs
  rw [FL_eq, tan_eq_logDeriv_hcos, hs]
  push_cast
  ring

/-- Local expansion of `fkL t` at `pk k`: residue `-kern t (pk k)`. -/
theorem fkL_expansion (t : ℝ) (k : ℕ) : ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G (pk k) ∧
    ∀ᶠ s in 𝓝[≠] (pk k), fkL t s = a / (s - pk k) ^ 2 + (-kern t (pk k)) / (s - pk k) + G s := by
  obtain ⟨g, hg, hφ⟩ := FL_expansion k
  have hp0 : pk k ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [pk_re] at this; simp at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hK := analyticAt_kern' t hp0
  refine ⟨0, fun s => -dslope (kern t) (pk k) s + g s * kern t s,
    (GlobalTheory.ExplicitRect.analyticAt_dslope hK).neg.add (hg.mul hK), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  have hsp' : s - pk k ≠ 0 := sub_ne_zero.mpr hsp
  have hexp := GlobalTheory.ExplicitRect.eq_add_dslope (kern t) (pk k) s
  rw [fkL, hs, hexp]
  field_simp
  ring

/-! ### The left rectangle -/

/-- **Left rectangle identity** on `[sig K, -1] × [-T, T]`: the only poles of `fkL t` there are
`pk k`, `k < K`, each with residue `-kern t (pk k)`. -/
theorem left_rect_identity (t : ℝ) (K : ℕ) {T : ℝ} (hT : 0 < T) :
    GlobalTheory.ResRect.bdInt (sig K) (-1) (-T) T (fkL t) =
      2 * Real.pi * I * -∑ k ∈ Finset.range K, kern t (pk k) := by
  classical
  have hinj : Set.InjOn pk (Finset.range K : Set ℕ) := fun a _ b _ h => by
    have := congrArg Complex.re h
    rw [pk_re, pk_re] at this
    exact_mod_cast (by linarith : (a : ℝ) = b)
  set S : Finset ℂ := (Finset.range K).image pk with hS
  let r : ℂ → ℂ := fun p => -kern t p
  have hsigK : sig K = -(2 * (K : ℝ) + 3 / 2) := rfl
  have hins : ∀ p ∈ S, (⟨sig K, -T⟩ : ℂ).re < p.re ∧ p.re < (⟨-1, T⟩ : ℂ).re ∧
      (⟨sig K, -T⟩ : ℂ).im < p.im ∧ p.im < (⟨-1, T⟩ : ℂ).im := by
    intro p hp
    show sig K < p.re ∧ p.re < -1 ∧ -T < p.im ∧ p.im < T
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    have hk' : (k : ℝ) + 1 ≤ K := by
      have := Finset.mem_range.1 hk; exact_mod_cast this
    rw [pk_re, pk_im, hsigK]
    refine ⟨by linarith, by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)], by linarith, hT⟩
  have hdiff : DifferentiableOn ℂ (fkL t) ((Set.Icc (⟨sig K, -T⟩ : ℂ).re (⟨-1, T⟩ : ℂ).re ×ℂ
      Set.Icc (⟨sig K, -T⟩ : ℂ).im (⟨-1, T⟩ : ℂ).im) \ ↑S) := by
    intro z hz
    obtain ⟨hzR, hzS⟩ := hz
    rw [Complex.mem_reProdIm] at hzR
    obtain ⟨⟨hre1, hre2⟩, -⟩ := hzR
    change sig K ≤ z.re at hre1
    change z.re ≤ -1 at hre2
    have hre : z.re < -1 / 2 := by linarith
    have hz : ∀ k : ℕ, z ≠ -(2 * (k : ℂ) + 1 / 2) := by
      intro k hk
      have hre' : z.re = -(2 * (k : ℝ) + 1 / 2) := by rw [hk]; simp
      have hk1 : k ≠ 0 := by rintro rfl; simp at hre'; linarith
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk1
      apply hzS
      refine Finset.mem_image.2 ⟨j, Finset.mem_range.2 ?_, ?_⟩
      · rw [hsigK] at hre1
        push_cast at hre'
        have : (j : ℝ) < K := by linarith
        exact_mod_cast this
      · rw [hk, pk]; push_cast; ring
    exact (analyticAt_fkL t hre hz).differentiableAt.differentiableWithinAt
  have hexp : ∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧
      ∀ᶠ s in nhdsWithin p {p}ᶜ, fkL t s = a / (s - p) ^ 2 + r p / (s - p) + g s := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hp
    exact fkL_expansion t k
  have key := GlobalTheory.ResRect.residue_rectangle (fkL t) ⟨sig K, -T⟩ ⟨-1, T⟩ S r
    (show sig K < -1 by rw [hsigK]; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)])
    (show -T < T by linarith) hins hdiff hexp
  have e : GlobalTheory.ResRect.bdInt (sig K) (-1) (-T) T (fkL t) =
      2 * Real.pi * I * ∑ p ∈ S, r p := key
  rw [e, hS, Finset.sum_image hinj, ← Finset.sum_neg_distrib]

/-- The trivial-pole sum, in the indexing of `left_rect_identity`. -/
theorem tendsto_trivial_partial (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, kern t (pk k)) atTop
      (𝓝 (((1 / 4 * Real.exp (-t / 2) * (V5_1.L t - 16)) : ℝ) : ℂ)) :=
  (trivial_sum t ht).tendsto_sum_nat

end ScrewRH
