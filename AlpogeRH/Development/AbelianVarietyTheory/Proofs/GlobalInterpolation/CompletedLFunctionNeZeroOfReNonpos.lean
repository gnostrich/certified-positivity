-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem inv_Gammaℝ_eq_mul_inv_add_two (s : ℂ) :
    (Gammaℝ s)⁻¹ = s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gammaℝ_def]
  · have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Gammaℝ_add_two hs]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    generalize (Gammaℝ s)⁻¹ = g
    field_simp

private lemma deriv_inv_Gammaℝ_eq_shift (x : ℂ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) x =
      1 / (2 * Real.pi) * (Gammaℝ (x + 2))⁻¹ +
        x / (2 * Real.pi) * deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2) := by
  have hF : (fun s : ℂ => (Gammaℝ s)⁻¹) = fun s => s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ :=
    funext inv_Gammaℝ_eq_mul_inv_add_two
  have h1 : HasDerivAt (fun s : ℂ => s / (2 * (Real.pi : ℂ))) (1 / (2 * Real.pi)) x :=
    (hasDerivAt_id' x).div_const _
  have h2 : HasDerivAt (fun s : ℂ => (Gammaℝ (s + 2))⁻¹)
      (deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (x + 2)) x :=
    HasDerivAt.comp_add_const x 2 (differentiable_Gammaℝ_inv (x + 2)).hasDerivAt
  conv_lhs => rw [hF]
  exact (h1.mul h2).deriv

theorem deriv_inv_Gammaℝ_ne_zero (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-(2 * n)) ≠ 0 := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  induction n with
  | zero =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have h2 : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
    simp [h2, Real.pi_ne_zero]
  | succ n ih =>
    rw [deriv_inv_Gammaℝ_eq_shift]
    have e : (-(2 * ((n + 1 : ℕ) : ℂ))) + 2 = -(2 * (n : ℂ)) := by push_cast; ring
    rw [e, inv_eq_zero.mpr (Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩), mul_zero, zero_add]
    refine mul_ne_zero (div_ne_zero ?_ hπ) ih
    have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero this)

theorem rootNumber_ne_zero_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : rootNumber χ ≠ 0 := by
  have hG : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h
    have h1 : ZMod.dft (χ : ZMod q → ℂ) = 0 := by
      funext k
      rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, h, mul_zero]
      rfl
    have h2 := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
    rw [h1, _root_.map_zero] at h2
    simp only [Pi.zero_apply, neg_neg, map_one, smul_eq_mul, mul_one] at h2
    exact NeZero.ne q (by exact_mod_cast h2.symm)
  unfold rootNumber
  refine div_ne_zero (div_ne_zero hG (pow_ne_zero _ I_ne_zero)) ?_
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)

theorem completedLFunction_ne_zero_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) (h0 : s ≠ 0 ∨ χ ≠ 1) :
    completedLFunction χ s ≠ 0 := by
  have hFE := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  have hw : 1 ≤ (1 - s).re := by rw [sub_re, one_re]; linarith
  refine mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero_of_isPrimitive hχ)) ?_
  · rw [Ne, cpow_eq_zero_iff]
    exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)
  · intro hC
    have hne : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 := by
      rcases h0 with h | h
      · exact Or.inr (by intro h'; apply h; linear_combination -h')
      · exact Or.inl (inv_ne_one.mpr h)
    apply LFunction_ne_zero_of_one_le_re χ⁻¹ hne hw
    have h1s : 1 - s ≠ 0 := by
      intro h'; rw [h'] at hw; norm_num at hw
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s), hC, zero_div]

theorem LFunction_zero_of_re_nonpos : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ, s.re ≤ 0 → LFunction χ s = 0 → (∃ n : ℕ, s = -n) ∧ analyticOrderNatAt (LFunction χ) s = 1 ∧ (s = 0 → χ.Even ∧ χ ≠ 1) ∧ (s = -1 → χ.Odd) := by
  intro q _ χ hχ s hs hL
  have h0 : s ≠ 0 ∨ χ ≠ 1 := by
    by_contra! h
    obtain ⟨rfl, rfl⟩ := h
    have hq : q = 1 := by rw [IsPrimitive, conductor_one] at hχ; exact hχ.symm
    subst hq
    rw [LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have h0' : s ≠ 0 ∨ q ≠ 1 := h0.imp id (fun h hq => h (level_one' χ hq))
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hC : completedLFunction χ s ≠ 0 := completedLFunction_ne_zero_of_re_nonpos hχ hs h0
  have hCd : DifferentiableAt ℂ (completedLFunction χ) s :=
    differentiableAt_completedLFunction χ s h0' (Or.inl hs1)
  obtain ⟨a, ha, hpar⟩ : ∃ a : ℕ, (∀ w, gammaFactor χ w = Gammaℝ (w + a)) ∧
      (a = 0 ∧ χ.Even ∨ a = 1 ∧ χ.Odd) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, fun w => by simp [h.gammaFactor_def], Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, fun w => by simp [h.gammaFactor_def], Or.inr ⟨rfl, h⟩⟩
  have hev : LFunction χ =ᶠ[nhds s] fun w => completedLFunction χ w * (Gammaℝ (w + a))⁻¹ := by
    have : ∀ᶠ w in nhds s, w ≠ 0 ∨ q ≠ 1 := by
      rcases h0' with h | h
      · exact (eventually_ne_nhds h).mono fun w hw => Or.inl hw
      · exact Filter.Eventually.of_forall fun _ => Or.inr h
    exact this.mono fun w hw => by
      rw [LFunction_eq_completed_div_gammaFactor χ w hw, div_eq_mul_inv, ha]
  have hG : Gammaℝ (s + a) = 0 := by
    have := hev.self_of_nhds
    rw [hL] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hC
    · exact inv_eq_zero.mp h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
  have hh : HasDerivAt (fun w : ℂ => (Gammaℝ (w + a))⁻¹)
      (deriv (fun w : ℂ => (Gammaℝ w)⁻¹) (s + a)) s :=
    HasDerivAt.comp_add_const s (a : ℂ) (differentiable_Gammaℝ_inv (s + a)).hasDerivAt
  have hder : deriv (LFunction χ) s ≠ 0 := by
    rw [hev.deriv_eq, (hCd.hasDerivAt.fun_mul hh).deriv, inv_eq_zero.mpr hG, mul_zero, zero_add]
    refine mul_ne_zero hC ?_
    rw [hn]
    exact deriv_inv_Gammaℝ_ne_zero n
  have hAn : AnalyticAt ℂ (LFunction χ) s :=
    analyticAt_iff_eventually_differentiableAt.mpr
      ((eventually_ne_nhds hs1).mono fun w hw => differentiableAt_LFunction χ w (Or.inl hw))
  have hord : analyticOrderAt (LFunction χ) s = 1 :=
    hAn.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hL hder
  have hs_eq : s = -((2 * n + a : ℕ) : ℂ) := by push_cast; linear_combination hn
  refine ⟨⟨2 * n + a, hs_eq⟩, by simp [analyticOrderNatAt, hord], fun h => ?_, fun h => ?_⟩
  · rw [h] at hs_eq
    have hk : ((2 * n + a : ℕ) : ℂ) = 0 := by linear_combination hs_eq
    have hk' : 2 * n + a = 0 := by exact_mod_cast hk
    refine ⟨?_, h0.resolve_left (not_not.mpr h)⟩
    rcases hpar with ⟨_, he⟩ | ⟨ha1, _⟩
    · exact he
    · omega
  · rw [h] at hs_eq
    have hk : ((2 * n + a : ℕ) : ℂ) = 1 := by linear_combination hs_eq
    have hk' : 2 * n + a = 1 := by exact_mod_cast hk
    rcases hpar with ⟨ha0, _⟩ | ⟨_, ho⟩
    · omega
    · exact ho

end GlobalTheory
