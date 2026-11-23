module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset

@[expose] public section

/-!
# Summability over the nontrivial zeros (blueprint lemma 9)

Interface (all in namespace `ScrewRH`):
* `zeta_zero_window C`: zero counting in unit windows, specialised to `riemannZeta`
  (from Alpöge's `GlobalTheory.ZeroWindow.count_zeros_window`).
* `Z_inter_finite T`: `(Z ∩ {ρ | |ρ.im| ≤ T}).Finite`.
* `Z_countable`: `Z.Countable`.
* `summable_zeros`: `Summable (fun ρ : Z => (mult ρ : ℝ) / ‖(ρ : ℂ) - 1/2‖ ^ 2)`.
* `zero_term_norm_le`: for `ρ ∈ Z` and real `t`,
  `‖mult ρ * (exp ((ρ-½) t) - 1) / (ρ-½)²‖ ≤ mult ρ * (exp (|t|/2) + 1) / ‖ρ-½‖²`.
* `summable_zero_term t`: summability over `Z` of `mult ρ * (exp ((ρ-½) t) - 1) / (ρ-½)²`.
* `continuous_tsum_zero_term`: `t ↦ ∑' ρ : Z, ...` is continuous on `ℝ` (Weierstrass M-test).

The ported Alpöge infrastructure is credited to Levent Alpöge (used with permission).
-/

open Complex Filter Topology

namespace ScrewRH

/-- The zero-counting window for `ζ`. -/
theorem zeta_zero_window : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0}.Finite ∧
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0},
      (mult ρ : ℝ) ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C, hC, fun t => ?_⟩
  have := h 1 (1 : DirichletCharacter ℂ 1) DirichletCharacter.isPrimitive_one_level_one t
  simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at this
  exact this

/-- The window around an integer `k`. -/
def win (k : ℤ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - (k : ℝ)| ≤ 1 ∧ riemannZeta ρ = 0}

theorem win_finite (k : ℤ) : (win k).Finite := by
  obtain ⟨_, -, h⟩ := zeta_zero_window
  exact (h k).1

theorem mem_win_round {ρ : ℂ} (hρ : ρ ∈ Z) : ρ ∈ win (round ρ.im) := by
  obtain ⟨h1, h2, h3⟩ := hρ
  refine ⟨h2, h3, ?_, h1⟩
  linarith [abs_sub_round ρ.im]

theorem Z_subset_iUnion : Z ⊆ ⋃ k : ℤ, win k := fun ρ hρ =>
  Set.mem_iUnion.2 ⟨round ρ.im, mem_win_round hρ⟩

theorem Z_countable : Z.Countable :=
  (Set.countable_iUnion fun k => (win_finite k).countable).mono Z_subset_iUnion

theorem Z_inter_finite (T : ℝ) : (Z ∩ {ρ : ℂ | |ρ.im| ≤ T}).Finite := by
  set N : ℕ := ⌈T⌉₊ + 1
  have hsub : Z ∩ {ρ : ℂ | |ρ.im| ≤ T} ⊆
      ⋃ k ∈ (Finset.Icc (-(N : ℤ)) N : Set ℤ), win k := by
    rintro ρ ⟨hρ, hT⟩
    refine Set.mem_biUnion (x := round ρ.im) ?_ (mem_win_round hρ)
    have h1 := abs_sub_round ρ.im
    have h2 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
    simp only [Set.mem_ofPred_eq] at hT
    have h3 : |((round ρ.im : ℤ) : ℝ)| ≤ (N : ℝ) := by
      have : |((round ρ.im : ℤ) : ℝ)| ≤ |ρ.im| + |ρ.im - (round ρ.im : ℝ)| := by
        have := abs_sub_abs_le_abs_sub ((round ρ.im : ℤ) : ℝ) ρ.im
        rw [abs_sub_comm] at this
        linarith
      simp only [N]; push_cast; linarith
    have h4 : |round ρ.im| ≤ (N : ℤ) := by exact_mod_cast h3
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact abs_le.1 h4
  exact ((Finset.Icc (-(N : ℤ)) N).finite_toSet.biUnion fun k _ => win_finite k).subset hsub

/-- The summand. -/
noncomputable def zw (ρ : Z) : ℝ := (mult (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2

theorem zw_nonneg (ρ : Z) : 0 ≤ zw ρ := by unfold zw; positivity

/-- Fibre of `round ∘ im` on `Z`. -/
abbrev Fib (k : ℤ) := {ρ : Z // round (ρ : ℂ).im = k}

instance (k : ℤ) : Finite (Fib k) := by
  have : Finite (win k) := (win_finite k).to_subtype
  refine Finite.of_injective (fun x : Fib k => (⟨(x.1 : ℂ), by
    have := mem_win_round x.1.2; rwa [x.2] at this⟩ : win k)) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  simpa using congrArg Subtype.val hxy

theorem fib_sum_mult_le {C : ℝ}
    (hC : ∀ t : ℝ, ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ riemannZeta ρ = 0},
      (mult ρ : ℝ) ≤ C * Real.log (|t| + 2)) (k : ℤ) :
    ∑' x : Fib k, (mult ((x.1 : ℂ)) : ℝ) ≤ C * Real.log (|(k : ℝ)| + 2) := by
  classical
  let _ := Fintype.ofFinite (Fib k)
  rw [tsum_fintype]
  refine le_trans ?_ (hC k)
  have hw : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - (k : ℝ)| ≤ 1 ∧ riemannZeta ρ = 0}.Finite :=
    win_finite k
  rw [finsum_mem_eq_finite_toFinset_sum _ hw]
  let e : Fib k ↪ ℂ := ⟨fun x => (x.1 : ℂ), fun x y h => by
    apply Subtype.ext; apply Subtype.ext; exact h⟩
  have : ∑ x : Fib k, (mult ((x.1 : ℂ)) : ℝ) =
      ∑ ρ ∈ Finset.univ.map e, (mult ρ : ℝ) := by
    rw [Finset.sum_map]; rfl
  rw [this]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro ρ hρ
  simp only [Finset.mem_map, Finset.mem_univ, true_and] at hρ
  obtain ⟨x, rfl⟩ := hρ
  rw [Set.Finite.mem_toFinset]
  have := mem_win_round x.1.2
  rw [x.2] at this
  exact this

theorem zw_le_of_fib {k : ℤ} (hk : k ≠ 0) (x : Fib k) :
    zw x.1 ≤ (mult ((x.1 : ℂ)) : ℝ) * (4 / (k : ℝ) ^ 2) := by
  unfold zw
  set ρ : ℂ := ((x.1 : Z) : ℂ)
  have hr := abs_sub_round ρ.im
  rw [x.2] at hr
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have him : |(k : ℝ)| / 2 ≤ |ρ.im| := by
    have := abs_sub_abs_le_abs_sub (k : ℝ) ρ.im
    rw [abs_sub_comm (k : ℝ)] at this
    linarith
  have hnorm : (k : ℝ) ^ 2 / 4 ≤ ‖ρ - 1 / 2‖ ^ 2 := by
    have h1 : |ρ.im| ≤ ‖ρ - 1 / 2‖ := by
      have := Complex.abs_im_le_norm (ρ - 1 / 2)
      simpa using this
    have h2 : (k : ℝ) ^ 2 / 4 = (|(k : ℝ)| / 2) ^ 2 := by rw [div_pow, sq_abs]; norm_num
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) (him.trans h1) 2
  have hkpos : 0 < (k : ℝ) ^ 2 / 4 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  rw [div_eq_mul_inv]
  gcongr
  · rw [inv_le_comm₀ (hkpos.trans_le hnorm) (by positivity)]
    calc (4 / (k : ℝ) ^ 2)⁻¹ = (k : ℝ) ^ 2 / 4 := by rw [inv_div]
      _ ≤ _ := hnorm

theorem log_div_sq_le {k : ℤ} (hk : k ≠ 0) :
    Real.log (|(k : ℝ)| + 2) / (k : ℝ) ^ 2 ≤ 4 * |(k : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  set a := |(k : ℝ)| with ha
  have ha0 : 0 < a := by linarith
  have hsq : (k : ℝ) ^ 2 = a ^ (2 : ℝ) := by
    rw [Real.rpow_two, ha, sq_abs]
  have hlog : Real.log (a + 2) ≤ (a + 2) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h3 : (a + 2) ^ (1 / 2 : ℝ) ≤ (4 * a) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h4 : (4 * a) ^ (1 / 2 : ℝ) = 2 * a ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) ha0.le]
    congr 1
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h5 : a ^ (1 / 2 : ℝ) / a ^ (2 : ℝ) = a ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_sub ha0]; norm_num
  rw [hsq, div_le_iff₀ (by positivity)]
  calc Real.log (a + 2) ≤ 4 * a ^ (1 / 2 : ℝ) := by linarith
    _ = 4 * a ^ (-(3 / 2 : ℝ)) * a ^ (2 : ℝ) := by
      rw [mul_assoc, ← h5, div_mul_cancel₀ _ (by positivity)]

/-- **Blueprint lemma 9.** -/
theorem summable_zeros :
    Summable (fun ρ : Z => (mult (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := zeta_zero_window
  have hC' : ∀ t : ℝ, ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧
      riemannZeta ρ = 0}, (mult ρ : ℝ) ≤ C * Real.log (|t| + 2) := fun t => (hC t).2
  change Summable zw
  let e := Equiv.sigmaFiberEquiv (fun ρ : Z => round (ρ : ℂ).im)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (f := fun x => zw (e x)) (fun _ => zw_nonneg _)).2
    ⟨fun k => Summable.of_finite, ?_⟩
  refine Summable.of_norm_bounded_eventually
    (g := fun k : ℤ => 16 * C * |(k : ℝ)| ^ (-(3 / 2 : ℝ)))
    ((Real.summable_abs_int_rpow (by norm_num)).mul_left _) ?_
  have : ∀ᶠ k : ℤ in cofinite, k ≠ 0 := eventually_cofinite_ne 0
  filter_upwards [this] with k hk
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => zw_nonneg _)]
  have hsum : Summable fun y : Fib k => (mult ((y.1 : ℂ)) : ℝ) := Summable.of_finite
  calc ∑' y : Fib k, zw (e ⟨k, y⟩)
      ≤ ∑' y : Fib k, (mult ((y.1 : ℂ)) : ℝ) * (4 / (k : ℝ) ^ 2) :=
        Summable.tsum_le_tsum (fun y => zw_le_of_fib hk y) Summable.of_finite
          Summable.of_finite
    _ = (∑' y : Fib k, (mult ((y.1 : ℂ)) : ℝ)) * (4 / (k : ℝ) ^ 2) := tsum_mul_right
    _ ≤ (C * Real.log (|(k : ℝ)| + 2)) * (4 / (k : ℝ) ^ 2) := by
        gcongr; exact fib_sum_mult_le hC' k
    _ = 4 * C * (Real.log (|(k : ℝ)| + 2) / (k : ℝ) ^ 2) := by ring
    _ ≤ 4 * C * (4 * |(k : ℝ)| ^ (-(3 / 2 : ℝ))) := by
        gcongr; exact log_div_sq_le hk
    _ = 16 * C * |(k : ℝ)| ^ (-(3 / 2 : ℝ)) := by ring

/-- The summand of the zero sum. -/
noncomputable def zeroTerm (t : ℝ) (ρ : ℂ) : ℂ :=
  (mult ρ : ℂ) * (Complex.exp ((ρ - 1 / 2) * t) - 1) / (ρ - 1 / 2) ^ 2

/-- M-test bound for the zero sum. -/
theorem zero_term_norm_le {ρ : ℂ} (hρ : ρ ∈ Z) (t : ℝ) :
    ‖zeroTerm t ρ‖ ≤ (mult ρ : ℝ) * (Real.exp (|t| / 2) + 1) / ‖ρ - 1 / 2‖ ^ 2 := by
  obtain ⟨-, h0, h1⟩ := hρ
  unfold zeroTerm
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  calc ‖Complex.exp ((ρ - 1 / 2) * t) - 1‖ ≤ ‖Complex.exp ((ρ - 1 / 2) * t)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ Real.exp (|t| / 2) + 1 := by
        rw [Complex.norm_exp, norm_one]
        gcongr
        have : ((ρ - 1 / 2) * (t : ℂ)).re = (ρ.re - 1 / 2) * t := by simp
        rw [this]
        have hb : |ρ.re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
        calc (ρ.re - 1 / 2) * t ≤ |(ρ.re - 1 / 2) * t| := le_abs_self _
          _ = |ρ.re - 1 / 2| * |t| := abs_mul _ _
          _ ≤ 1 / 2 * |t| := by gcongr
          _ = |t| / 2 := by ring

theorem summable_zero_term (t : ℝ) : Summable (fun ρ : Z => zeroTerm t ρ) := by
  refine Summable.of_norm_bounded (g := fun ρ : Z =>
    (mult (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 * (Real.exp (|t| / 2) + 1))
    (summable_zeros.mul_right _) (fun ρ => ?_)
  refine (zero_term_norm_le ρ.2 t).trans (le_of_eq ?_)
  ring

theorem continuousOn_tsum_zero_term (R : ℝ) :
    ContinuousOn (fun t : ℝ => ∑' ρ : Z, zeroTerm t ρ) (Set.Icc (-R) R) := by
  refine continuousOn_tsum (u := fun ρ : Z =>
    (mult (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 * (Real.exp (|R| / 2) + 1))
    (fun ρ => ?_) (summable_zeros.mul_right _) (fun ρ t ht => ?_)
  · unfold zeroTerm
    fun_prop
  · refine (zero_term_norm_le ρ.2 t).trans ?_
    rw [div_mul_eq_mul_div]
    have : |t| ≤ |R| := by
      rw [abs_le]; obtain ⟨h1, h2⟩ := ht
      constructor <;> cases abs_cases R <;> linarith
    gcongr

theorem continuous_tsum_zero_term : Continuous (fun t : ℝ => ∑' ρ : Z, zeroTerm t ρ) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h := continuousOn_tsum_zero_term (|t| + 1)
  refine h.continuousAt (Icc_mem_nhds ?_ ?_) <;> cases abs_cases t <;> linarith

end ScrewRH
