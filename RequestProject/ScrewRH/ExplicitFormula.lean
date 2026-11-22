module

public import Mathlib
public import RequestProject.V5_1
public import RequestProject.ScrewRH.Defs
public import RequestProject.ScrewRH.PerronPrimeSum
public import RequestProject.ScrewRH.LogDerivHalf
public import RequestProject.ScrewRH.SummableZeros
public import RequestProject.ScrewRH.ShiftLimit
public import RequestProject.ScrewRH.LeftSide

@[expose] public section

/-!
# ScrewRH.ExplicitFormula: the explicit formula for the screw function (blueprint lemma 10)

Unconditionally (no RH), for every `t ≥ 0`,
`V5_1.Psi t = ∑' ρ : Z, mult ρ · (e^{(ρ-½)t} - 1)/(ρ-½)²`.

Route, for fixed `t > 0`:
* `perron_primeSum`: `∫ fk t (1 + y I) dy = 2π · primeSum t`;
* `shift_limit'`: along good heights `T j`, `∫_{-T j}^{T j} fk t (-1 + y I) dy → ∫right - 2π Res`;
* `left_rect_identity` (with `fk = fkL` on `re z = -1`) and `tendsto_left_horizontal_top/bot`:
  the same truncated integrals tend to `∫ fkL t (sig K + y I) dy - 2π ∑_{k<K} kern t (pk k)`;
* `left_limit_K`, `tendsto_trivial_partial`: `K → ∞`.
This gives `primeSum t = Res t - ¼ e^{-t/2} (L t - 16)` (`primeSum_eq_res`). The unknown
constant `F'(0) - ∑' m/(ρ-½)²` is then removed by letting `t → 0⁺` (`primeSum t = 0` for
`t < log 2`), and `F 0 = (A - log π)/2` (`F_zero`) finishes the identification with `PsiArch`.
-/

open Complex Filter Topology MeasureTheory

namespace ScrewRH

/-- The residue sum on the right rectangle. -/
noncomputable def resSum (t : ℝ) : ℂ :=
  4 * Complex.exp (t / 2) + (deriv F 0 + t * F 0) -
    ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)

/-- The trivial-pole contribution `¼ e^{-t/2} (L t - 16)`. -/
noncomputable def trivSum (t : ℝ) : ℂ :=
  (((1 / 4 * Real.exp (-t / 2) * (V5_1.L t - 16)) : ℝ) : ℂ)

lemma sig_le_neg_one (K : ℕ) : sig K ≤ -1 := by
  unfold sig; linarith [(K.cast_nonneg : (0 : ℝ) ≤ K)]

/-- The truncated left-line integrals, rewritten through the left rectangle. -/
lemma left_truncated_eq (t : ℝ) (K : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ y in (-T)..T, fk t (-1 + y * I)) =
      (∫ y in (-T)..T, fkL t ((sig K : ℂ) + y * I)) -
        2 * Real.pi * ∑ k ∈ Finset.range K, kern t (pk k) +
        I * ((∫ x : ℝ in (sig K)..(-1), fkL t ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (sig K)..(-1), fkL t ((x : ℂ) + T * I))) := by
  have h := left_rect_identity t K hT
  unfold GlobalTheory.ResRect.bdInt at h
  have e : (∫ y in (-T)..T, fkL t (((-1 : ℝ) : ℂ) + y * I)) =
      ∫ y in (-T)..T, fk t (-1 + y * I) := by
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [fk, fk_eq_fkL_of_re_eq t (by simp)]
    push_cast; rfl
  rw [e] at h
  set f := ∫ y in (-T)..T, fk t (-1 + y * I)
  set V := ∫ y in (-T)..T, fkL t ((sig K : ℂ) + y * I)
  set S := ∑ k ∈ Finset.range K, kern t (pk k)
  linear_combination (-I) * h + (f - V + 2 * Real.pi * S) * Complex.I_sq

/-- **Contour identity** for `t > 0`: `∫right - 2π Res = -2π · trivSum`. -/
lemma right_sub_res (t : ℝ) (ht : 0 < t) :
    (∫ y : ℝ, fk t (1 + y * I)) - 2 * Real.pi * resSum t = -(2 * Real.pi * trivSum t) := by
  obtain ⟨T, hT, hTpos, hlim⟩ := shift_limit' t
  have hK : ∀ K : ℕ, (∫ y : ℝ, fk t (1 + y * I)) - 2 * Real.pi * resSum t =
      (∫ y : ℝ, fkL t ((sig K : ℂ) + y * I)) -
        2 * Real.pi * ∑ k ∈ Finset.range K, kern t (pk k) := by
    intro K
    have h1 : Tendsto (fun j => ∫ y in (-T j)..(T j), fk t (-1 + y * I)) atTop
        (𝓝 ((∫ y : ℝ, fkL t ((sig K : ℂ) + y * I)) -
          2 * Real.pi * ∑ k ∈ Finset.range K, kern t (pk k) + I * (0 - 0))) := by
      simp_rw [fun j => left_truncated_eq t K (hTpos j)]
      refine ((intervalIntegral_tendsto_integral (integrable_fkL_vertical t K)
        (tendsto_neg_atTop_atBot.comp hT) hT).sub tendsto_const_nhds).add
        ((((tendsto_left_horizontal_bot ht.le (sig K) (sig_le_neg_one K)).comp hT).sub
          ((tendsto_left_horizontal_top ht.le (sig K) (sig_le_neg_one K)).comp hT)).const_mul _)
    have h2 := tendsto_nhds_unique hlim h1
    rw [resSum, h2]; ring
  have hlimK : Tendsto (fun K : ℕ => (∫ y : ℝ, fkL t ((sig K : ℂ) + y * I)) -
      2 * Real.pi * ∑ k ∈ Finset.range K, kern t (pk k)) atTop
      (𝓝 (0 - 2 * Real.pi * trivSum t)) :=
    (left_limit_K ht).sub ((tendsto_trivial_partial t ht.le).const_mul _)
  have hconst : Tendsto (fun _ : ℕ => (∫ y : ℝ, fk t (1 + y * I)) - 2 * Real.pi * resSum t)
      atTop (𝓝 (0 - 2 * Real.pi * trivSum t)) := by
    exact hlimK.congr (fun K => (hK K).symm)
  rw [tendsto_nhds_unique tendsto_const_nhds hconst]; ring

/-- For `t > 0`: `primeSum t = Res t - ¼ e^{-t/2} (L t - 16)`. -/
theorem primeSum_eq_res (t : ℝ) (ht : 0 < t) :
    ((V5_1.primeSum t : ℝ) : ℂ) = resSum t - trivSum t := by
  have hP := perron_primeSum t
  have hR := right_sub_res t ht
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [← hP]
  unfold fk at hR
  field_simp
  linear_combination hR

/-- The constant `∑' m(ρ)/(ρ-½)²`. -/
noncomputable def zeroConst : ℂ := ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) / ((ρ : ℂ) - 1 / 2) ^ 2

lemma summable_zeroConst :
    Summable (fun ρ : Z => (mult (ρ : ℂ) : ℂ) / ((ρ : ℂ) - 1 / 2) ^ 2) := by
  refine (summable_zero_kern 0).congr (fun ρ => ?_)
  simp [kern, div_eq_mul_inv]

lemma tsum_zero_kern_eq (t : ℝ) :
    ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2) =
      (∑' ρ : Z, zeroTerm t ρ) + zeroConst := by
  rw [zeroConst, ← (summable_zero_term t).tsum_add summable_zeroConst]
  refine tsum_congr (fun ρ => ?_)
  simp only [kern, zeroTerm]
  ring

/-- The elementary part of the identity. -/
noncomputable def elem (t : ℝ) : ℂ :=
  4 * Complex.exp (t / 2) + t * F 0 - (∑' ρ : Z, zeroTerm t ρ) - trivSum t

lemma primeSum_eq_elem (t : ℝ) (ht : 0 < t) :
    ((V5_1.primeSum t : ℝ) : ℂ) = elem t + (deriv F 0 - zeroConst) := by
  rw [primeSum_eq_res t ht, resSum, tsum_zero_kern_eq, elem]
  ring

lemma continuousOn_L : ContinuousOn V5_1.L (Set.Ici 0) := by
  unfold V5_1.L
  refine continuousOn_tsum (u := fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2)
    (fun n => by fun_prop) V5_1.summable_C (fun n t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr ?_)
  have : (0 : ℝ) ≤ t := ht
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

lemma continuousOn_elem : ContinuousOn elem (Set.Ici 0) := by
  unfold elem trivSum
  have hL : ContinuousOn (fun t : ℝ => (((1 / 4 * Real.exp (-t / 2) * (V5_1.L t - 16)) : ℝ) : ℂ))
      (Set.Ici 0) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (continuousOn_const.mul (by fun_prop)).mul (continuousOn_L.sub continuousOn_const)
  refine ContinuousOn.sub (ContinuousOn.sub (Continuous.continuousOn (by fun_prop))
    continuous_tsum_zero_term.continuousOn) hL

lemma tsum_zeroTerm_zero : ∑' ρ : Z, zeroTerm 0 ρ = 0 := by
  simp [zeroTerm]

lemma elem_zero : elem 0 = ((8 - V5_1.C / 4 : ℝ) : ℂ) := by
  rw [elem, tsum_zeroTerm_zero, trivSum, V5_1.L_zero]
  push_cast
  simp
  ring

/-- **Elimination of `F'(0)`**: `F'(0) - ∑' m/(ρ-½)² = C/4 - 8`. -/
theorem deriv_F_zero_sub : deriv F 0 - zeroConst = ((V5_1.C / 4 - 8 : ℝ) : ℂ) := by
  have hcont : Tendsto elem (𝓝[>] 0) (𝓝 (elem 0)) :=
    ((continuousOn_elem 0 (Set.mem_Ici.2 le_rfl)).mono Set.Ioi_subset_Ici_self).tendsto
  have hev : elem =ᶠ[𝓝[>] 0] fun _ => -(deriv F 0 - zeroConst) := by
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    filter_upwards [Ioo_mem_nhdsGT hlog] with t ht
    have h := primeSum_eq_elem t ht.1
    rw [V5_1.primeSum_eq_zero t ht.1.le ht.2] at h
    push_cast at h
    linear_combination -h
  have h := tendsto_nhds_unique hcont (tendsto_const_nhds.congr' hev.symm)
  rw [elem_zero] at h
  push_cast at h ⊢
  linear_combination h

/-- **Blueprint lemma 10 (explicit formula for the screw function).** No RH is assumed. For
every `t ≥ 0`, `Psi t = ∑' ρ, m(ρ) (e^{(ρ-½)t} - 1)/(ρ-½)²`, the sum running over the
nontrivial zeros of `ζ` without repetition, weighted by multiplicity. -/
theorem Psi_eq_tsum_zeros (t : ℝ) (ht : 0 ≤ t) :
    ((V5_1.Psi t : ℝ) : ℂ) = ∑' ρ : Z, zeroTerm t ρ := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; rw [V5_1.Psi_zero, tsum_zeroTerm_zero]; simp
  have h := primeSum_eq_elem t hpos
  rw [deriv_F_zero_sub, elem, trivSum, F_zero] at h
  have hPsi : V5_1.Psi t = V5_1.PsiArch t - V5_1.primeSum t := by
    rw [V5_1.Psi, V5_1.PsiNonneg, abs_of_nonneg ht]
  rw [hPsi, V5_1.PsiArch]
  push_cast at h ⊢
  have e : Complex.exp (-(t : ℂ) / 2) = Complex.exp (-((t : ℂ) / 2)) := by ring_nf
  rw [e] at h ⊢
  linear_combination -h

end ScrewRH
