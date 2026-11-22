module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import RequestProject.V5_1
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope
public import AlpogeRH.Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlaneStatement

@[expose] public section

/-!
# ScrewRH.LeftSide: `F` on the left half plane (blueprint lemmas 4 and 8)

Interface (namespace `ScrewRH`).
* `FL z = logDeriv ζ (½ - z) - log (2π) + ψ (½ - z) - (π/2) tan (π (½ - z)/2)`, and
  `fkL t z = FL z * kern t z`.
* `F_eq_FL`: `F z = FL z` when `½ - z ∉ ℤ` and `ζ (½ - z) ≠ 0`;
  `F_eq_FL_of_re_le` : the same for `re z ≤ -1/2`, `½ - z ∉ ℤ`;
  `fk_eq_fkL_of_re_eq` : `F z * kern t z = fkL t z` on the line `re z = -1`.
* `trivial_sum t ht`: `HasSum (fun k : ℕ => kern t (-(2 (k+1) + ½)))
  ((¼ e^{-t/2} (V5_1.L t - 16) : ℝ) : ℂ)` for `t ≥ 0`.
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

end ScrewRH
