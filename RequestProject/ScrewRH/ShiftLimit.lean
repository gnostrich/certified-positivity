module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import RequestProject.ScrewRH.LocalExpansions
public import RequestProject.ScrewRH.RectIdentity
public import RequestProject.ScrewRH.SummableZeros
public import RequestProject.ScrewRH.ZetaHalf
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBoundRight

@[expose] public section

/-!
# ScrewRH.ShiftLimit: letting `T → ∞` in the right rectangle (blueprint lemma 7)

Interface (namespace `ScrewRH`; `fk t z = F z * kern t z`, `t : ℝ` arbitrary):
* `norm_F_le_of_re_eq_one`: `∃ M ≥ 0, ∀ z, re z = 1 → ‖F z‖ ≤ M`.
* `continuous_fk_right t`, `integrable_fk_right t`: `y ↦ fk t (1 + y I)` is continuous and
  integrable on `ℝ`.
* `norm_kern_le_horizontal`, `norm_integral_horizontal_le`: on a horizontal segment
  `[-1, 1] + c I`, `‖kern t‖ ≤ e^{|t|}/c²`, so the edge integral is `≤ 2 B e^{|t|}/c²`.
* `summable_zero_kern t`: `Summable (fun ρ : Z => mult ρ * kern t (ρ - 1/2))`.
* `tendsto_finsum_zerosBelow t hT`: if `T j → ∞`, then the truncated sums
  `∑ᶠ ρ ∈ zerosBelow (T j), mult ρ * kern t (ρ - 1/2)` tend to `∑' ρ : Z, ...`.
* `tendsto_left_of_heights`: the abstract shift. Assume `T j → ∞`, `T j > 0`, no zeros of
  `ζ(1/2 + z)` on the horizontal edges, `‖F‖ ≤ B j` there, and `B j / T j² → 0`. Then
  `∫_{-T j}^{T j} fk t (-1 + y I) dy → ∫ fk t (1 + y I) dy - 2π · Res`, where
  `Res = 4 e^{t/2} + (F'(0) + t F(0)) - ∑' ρ : Z, mult ρ * kern t (ρ - 1/2)`.
* `shift_limit hhalf t`: the same, along good heights produced by
  `GlobalTheory.GoodHeight.exists_height`. It needs no hypothesis on the left line.
* `shift_line_integral hhalf t hleft`: if moreover `y ↦ fk t (-1 + y I)` is integrable, then
  `∫ fk t (1 + y I) dy = ∫ fk t (-1 + y I) dy + 2π · Res`. In `dz = I dy` form this reads
  `∫_{Re z = 1} = ∫_{Re z = -1} + 2πi · Res`.

The main statements take `hhalf : riemannZeta (1/2) ≠ 0` as a hypothesis. The primed versions
`shift_limit'` and `shift_line_integral'` discharge it with `riemannZeta_half_ne_zero` from
`ScrewRH/ZetaHalf.lean`.
-/

open Complex Filter Topology MeasureTheory ArithmeticFunction

namespace ScrewRH

/-- `F` is bounded on the line `re z = 1` (that is, `re s = 3/2`). -/
lemma norm_F_le_of_re_eq_one : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, z.re = 1 → ‖F z‖ ≤ M := by
  refine ⟨∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) (3 / 2) n‖,
    tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro z hz
  have hs : (1 / 2 + z).re = 3 / 2 := by simp [hz]; norm_num
  have hs1 : 1 < (1 / 2 + z).re := by rw [hs]; norm_num
  have hsum : Summable (fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) (3 / 2) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  unfold F
  rw [← neg_div, ← key]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun n => ?_) ?_ hsum)
  · exact summable_norm_iff.mpr (LSeriesSummable_vonMangoldt hs1)
  · exact LSeries.norm_term_le_of_re_le_re _ (by rw [hs]; norm_num) n
  · exact summable_norm_iff.mpr (LSeriesSummable_vonMangoldt hs1)

lemma continuous_fk_right (t : ℝ) : Continuous (fun y : ℝ => fk t (1 + y * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hz0 : (1 + y * I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : 1 / 2 + (1 + y * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  have hζ : riemannZeta (1 / 2 + (1 + y * I)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  exact ContinuousAt.comp (g := fk t) (f := fun y : ℝ => 1 + (y : ℂ) * I)
    (differentiableAt_fk t hz0 h1 hζ).continuousAt (by fun_prop)

lemma norm_kern_right (t y : ℝ) : ‖kern t (1 + y * I)‖ = Real.exp t / (1 + y ^ 2) := by
  rw [kern, norm_div, norm_pow, Complex.norm_exp, Complex.sq_norm]
  have h1 : ((1 + y * I) * (t : ℂ)).re = t := by simp
  have h2 : normSq (1 + y * I) = 1 + y ^ 2 := by
    have := normSq_add_mul_I 1 y
    push_cast at this
    rw [this]; ring
  rw [h1, h2]

lemma integrable_fk_right (t : ℝ) : Integrable (fun y : ℝ => fk t (1 + y * I)) := by
  obtain ⟨M, hM0, hM⟩ := norm_F_le_of_re_eq_one
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (M * Real.exp t))
    (continuous_fk_right t).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hF := hM (1 + y * I) (by simp)
  rw [fk, norm_mul, norm_kern_right]
  calc ‖F (1 + y * I)‖ * (Real.exp t / (1 + y ^ 2))
      ≤ M * (Real.exp t / (1 + y ^ 2)) := by gcongr
    _ = M * Real.exp t * (1 + y ^ 2)⁻¹ := by ring

lemma norm_kern_le_horizontal (t x c : ℝ) (hx : |x| ≤ 1) (hc : c ≠ 0) :
    ‖kern t (x + c * I)‖ ≤ Real.exp |t| / c ^ 2 := by
  rw [kern, norm_div, norm_pow, Complex.norm_exp, Complex.sq_norm, normSq_add_mul_I]
  have h1 : ((x + c * I) * (t : ℂ)).re = x * t := by simp
  rw [h1]
  have hxt : x * t ≤ |t| := by
    calc x * t ≤ |x * t| := le_abs_self _
      _ = |x| * |t| := abs_mul _ _
      _ ≤ 1 * |t| := by gcongr
      _ = |t| := one_mul _
  have hc2 : 0 < c ^ 2 := by positivity
  calc Real.exp (x * t) / (x ^ 2 + c ^ 2) ≤ Real.exp |t| / (x ^ 2 + c ^ 2) := by
        gcongr
    _ ≤ Real.exp |t| / c ^ 2 := by
        gcongr
        nlinarith [sq_nonneg x]

lemma norm_integral_horizontal_le (t : ℝ) {c B : ℝ} (hc : c ≠ 0)
    (hB : ∀ x : ℝ, |x| ≤ 1 → ‖F (x + c * I)‖ ≤ B) :
    ‖∫ x in (-1 : ℝ)..1, fk t (x + c * I)‖ ≤ 2 * Real.exp |t| * (B / c ^ 2) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 1)
    (C := B * (Real.exp |t| / c ^ 2)) (f := fun x : ℝ => fk t (x + c * I)) (fun x hx => by
      have hx' : x ∈ Set.uIcc (-1 : ℝ) 1 := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by norm_num)] at hx'
      have hxa : |x| ≤ 1 := abs_le.mpr hx'
      rw [fk, norm_mul]
      exact mul_le_mul (hB x hxa) (norm_kern_le_horizontal t x c hxa hc) (norm_nonneg _) hB0)
  refine this.trans (le_of_eq ?_)
  norm_num
  ring

lemma norm_kern_shift_le {ρ : ℂ} (hρ : ρ ∈ Z) (t : ℝ) :
    ‖kern t (ρ - 1 / 2)‖ ≤ Real.exp (|t| / 2) / ‖ρ - 1 / 2‖ ^ 2 := by
  obtain ⟨-, h0, h1⟩ := hρ
  rw [kern, norm_div, norm_pow, Complex.norm_exp]
  gcongr
  have : ((ρ - 1 / 2) * (t : ℂ)).re = (ρ.re - 1 / 2) * t := by simp
  rw [this]
  have hb : |ρ.re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  calc (ρ.re - 1 / 2) * t ≤ |(ρ.re - 1 / 2) * t| := le_abs_self _
    _ = |ρ.re - 1 / 2| * |t| := abs_mul _ _
    _ ≤ 1 / 2 * |t| := by gcongr
    _ = |t| / 2 := by ring

theorem summable_zero_kern (t : ℝ) :
    Summable (fun ρ : Z => (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)) := by
  refine Summable.of_norm_bounded (g := fun ρ : Z =>
    (mult (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 * Real.exp (|t| / 2))
    (summable_zeros.mul_right _) (fun ρ => ?_)
  rw [norm_mul, Complex.norm_natCast]
  calc (mult (ρ : ℂ) : ℝ) * ‖kern t ((ρ : ℂ) - 1 / 2)‖
      ≤ (mult (ρ : ℂ) : ℝ) * (Real.exp (|t| / 2) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2) := by
        gcongr; exact norm_kern_shift_le ρ.2 t
    _ = _ := by ring

/-- The truncated zero sums converge to the full sum along any `T j → ∞`. -/
theorem tendsto_finsum_zerosBelow (t : ℝ) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun j => ∑ᶠ ρ ∈ zerosBelow (T j), (mult ρ : ℂ) * kern t (ρ - 1 / 2)) atTop
      (𝓝 (∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2))) := by
  classical
  set g : ℂ → ℂ := fun ρ => (mult ρ : ℂ) * kern t (ρ - 1 / 2) with hg
  have hS := (summable_zero_kern t).hasSum
  let s : ℕ → Finset Z := fun j => (zerosBelow_finite (T j)).toFinset.subtype (· ∈ Z)
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro A
    have hev : ∀ᶠ j in atTop, ∑ ρ ∈ A, |(ρ : ℂ).im| + 1 ≤ T j := hT.eventually_ge_atTop _
    filter_upwards [hev] with j hj
    intro ρ hρ
    have hle : |(ρ : ℂ).im| ≤ ∑ ρ ∈ A, |(ρ : ℂ).im| :=
      Finset.single_le_sum (f := fun ρ : Z => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
    simp only [s, Finset.mem_subtype, Set.Finite.mem_toFinset]
    exact ⟨ρ.2, by linarith⟩
  have hc := hS.comp hs
  refine hc.congr fun j => ?_
  simp only [Function.comp, s]
  rw [Finset.sum_subtype_of_mem (f := g) (fun x hx => ((Set.Finite.mem_toFinset _).1 hx).1),
    finsum_mem_eq_finite_toFinset_sum _ (zerosBelow_finite (T j))]

/-- **Blueprint lemma 7 (abstract form).** -/
theorem tendsto_left_of_heights (hhalf : riemannZeta (1 / 2) ≠ 0) (t : ℝ) (T B : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) (hTpos : ∀ j, 0 < T j)
    (hside : ∀ j (z : ℂ), -1 ≤ z.re → z.re ≤ 1 → |z.im| = T j →
      riemannZeta (1 / 2 + z) ≠ 0 ∧ ‖F z‖ ≤ B j)
    (hB : Tendsto (fun j => B j / T j ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y in (-T j)..(T j), fk t (-1 + y * I)) atTop
      (𝓝 ((∫ y : ℝ, fk t (1 + y * I)) - 2 * Real.pi * (4 * Complex.exp (t / 2) +
        (deriv F 0 + t * F 0) - ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)))) := by
  set A : ℂ := 4 * Complex.exp (t / 2) + (deriv F 0 + t * F 0) with hA
  set Res : ℕ → ℂ := fun j => ∑ᶠ ρ ∈ zerosBelow (T j), (mult ρ : ℂ) * kern t (ρ - 1 / 2)
    with hRes
  set H1 : ℕ → ℂ := fun j => ∫ x in (-1 : ℝ)..1, fk t (x + ((-T j : ℝ) : ℂ) * I) with hH1
  set H2 : ℕ → ℂ := fun j => ∫ x in (-1 : ℝ)..1, fk t (x + (T j : ℂ) * I) with hH2
  set R : ℕ → ℂ := fun j => ∫ y in (-T j)..(T j), fk t (1 + y * I) with hR
  set L : ℕ → ℂ := fun j => ∫ y in (-T j)..(T j), fk t (-1 + y * I) with hL
  have hid : ∀ j, L j = R j - I * (H1 j - H2 j) - 2 * Real.pi * (A - Res j) := by
    intro j
    have e := rect_identity hhalf t (hTpos j) (fun z h1 h2 h3 => (hside j z h1 h2 h3).1)
    simp only [GlobalTheory.ResRect.bdInt, Complex.ofReal_one, Complex.ofReal_neg] at e
    have e' : H1 j - H2 j + I * R j - I * L j = 2 * Real.pi * I * (A - Res j) := by
      simp only [hH1, hH2, hR, hL, hA, hRes, Complex.ofReal_neg]
      exact e
    linear_combination I * e' + (L j - R j + 2 * Real.pi * (A - Res j)) * Complex.I_sq
  -- horizontal edges
  have hHor : ∀ (c : ℕ → ℝ), (∀ j, |c j| = T j) →
      Tendsto (fun j => ∫ x in (-1 : ℝ)..1, fk t (x + (c j : ℂ) * I)) atTop (𝓝 0) := by
    intro c hc
    refine squeeze_zero_norm (a := fun j => 2 * Real.exp |t| * (B j / T j ^ 2)) (fun j => ?_) ?_
    · have hc0 : c j ≠ 0 := by
        intro h; have := hc j; rw [h, abs_zero] at this; linarith [hTpos j]
      have := norm_integral_horizontal_le t (B := B j) hc0 (fun x hx => by
        refine (hside j (x + c j * I) (by simp; linarith [(abs_le.mp hx).1])
          (by simp; linarith [(abs_le.mp hx).2]) (by simpa using hc j)).2)
      have hsq : c j ^ 2 = T j ^ 2 := by rw [← sq_abs, hc j]
      rwa [hsq] at this
    · simpa using hB.const_mul (2 * Real.exp |t|)
  have h1 : Tendsto H1 atTop (𝓝 0) :=
    hHor (fun j => -T j) (fun j => by rw [abs_neg, abs_of_pos (hTpos j)])
  have h2 : Tendsto H2 atTop (𝓝 0) :=
    hHor T (fun j => abs_of_pos (hTpos j))
  have hRt : Tendsto R atTop (𝓝 (∫ y : ℝ, fk t (1 + y * I))) :=
    intervalIntegral_tendsto_integral (integrable_fk_right t) (tendsto_neg_atTop_atBot.comp hT) hT
  have hRest := tendsto_finsum_zerosBelow t hT
  have hlim := (hRt.sub ((h1.sub h2).const_mul I)).sub ((hRest.const_sub A).const_mul
    (2 * Real.pi : ℂ))
  simp only [sub_zero, mul_zero] at hlim
  refine hlim.congr fun j => ?_
  rw [hid j]

/-- Good heights for `ζ`, from Alpöge's `exists_height`: an unbounded sequence `T j > 0` with no
zeros of `ζ(1/2 + z)` on the horizontal edges and `‖F‖ ≤ B j` there, `B j / T j² → 0`. -/
theorem exists_good_heights : ∃ T B : ℕ → ℝ, Tendsto T atTop atTop ∧ (∀ j, 0 < T j) ∧
    (∀ j (z : ℂ), -1 ≤ z.re → z.re ≤ 1 → |z.im| = T j →
      riemannZeta (1 / 2 + z) ≠ 0 ∧ ‖F z‖ ≤ B j) ∧
    Tendsto (fun j => B j / T j ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hgood⟩ := GlobalTheory.GoodHeight.exists_height
  have h := fun j : ℕ => hgood 1 (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one ((j : ℝ) + 2) (by linarith [j.cast_nonneg (α := ℝ)])
  choose T hT1 hT2 hT3 using h
  refine ⟨T, fun j => C * Real.log ((j : ℝ) + 2) ^ 2, ?_, fun j => ?_, fun j z h1 h2 h3 => ?_, ?_⟩
  · exact tendsto_atTop_mono hT1
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  · linarith [hT1 j, j.cast_nonneg (α := ℝ)]
  · have := hT3 j (1 / 2 + z) (by simp; linarith) (by simp; linarith) (by simpa using h3)
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at this
    refine ⟨this.1, ?_⟩
    rw [F, norm_neg]
    exact this.2
  · have hlim : Tendsto (fun j : ℕ => C * (Real.log ((j : ℝ) + 2) ^ 2 / (1 * ((j : ℝ) + 2) + 0)))
        atTop (𝓝 0) := by
      have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa using this.const_mul C
    refine squeeze_zero (fun j => by positivity) (fun j => ?_) hlim
    have hj : (2 : ℝ) ≤ (j : ℝ) + 2 := by linarith [j.cast_nonneg (α := ℝ)]
    have hTj : (j : ℝ) + 2 ≤ T j := hT1 j
    have hsq : (j : ℝ) + 2 ≤ T j ^ 2 := by nlinarith
    rw [one_mul, add_zero, mul_div_assoc]
    gcongr

/-- **Blueprint lemma 7.** Along good heights, the truncated left-line integrals converge to
`∫ fk t (1 + y I) dy - 2π · Res`. -/
theorem shift_limit (hhalf : riemannZeta (1 / 2) ≠ 0) (t : ℝ) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ (∀ j, 0 < T j) ∧
      Tendsto (fun j => ∫ y in (-T j)..(T j), fk t (-1 + y * I)) atTop
        (𝓝 ((∫ y : ℝ, fk t (1 + y * I)) - 2 * Real.pi * (4 * Complex.exp (t / 2) +
          (deriv F 0 + t * F 0) - ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)))) := by
  obtain ⟨T, B, hT, hTpos, hside, hB⟩ := exists_good_heights
  exact ⟨T, hT, hTpos, tendsto_left_of_heights hhalf t T B hT hTpos hside hB⟩

/-- **Blueprint lemma 7, line form.** If `fk t` is integrable on `re z = -1`, then
`∫ fk t (1 + y I) dy = ∫ fk t (-1 + y I) dy + 2π · Res`. -/
theorem shift_line_integral (hhalf : riemannZeta (1 / 2) ≠ 0) (t : ℝ)
    (hleft : Integrable (fun y : ℝ => fk t (-1 + y * I))) :
    (∫ y : ℝ, fk t (1 + y * I)) = (∫ y : ℝ, fk t (-1 + y * I)) +
      2 * Real.pi * (4 * Complex.exp (t / 2) + (deriv F 0 + t * F 0) -
        ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)) := by
  obtain ⟨T, hT, -, hlim⟩ := shift_limit hhalf t
  have h2 := intervalIntegral_tendsto_integral hleft (tendsto_neg_atTop_atBot.comp hT) hT
  have := tendsto_nhds_unique h2 hlim
  rw [this]
  ring

/-- `shift_limit` with `ζ(1/2) ≠ 0` discharged. -/
theorem shift_limit' (t : ℝ) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ (∀ j, 0 < T j) ∧
      Tendsto (fun j => ∫ y in (-T j)..(T j), fk t (-1 + y * I)) atTop
        (𝓝 ((∫ y : ℝ, fk t (1 + y * I)) - 2 * Real.pi * (4 * Complex.exp (t / 2) +
          (deriv F 0 + t * F 0) - ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)))) :=
  shift_limit riemannZeta_half_ne_zero t

/-- `shift_line_integral` with `ζ(1/2) ≠ 0` discharged. -/
theorem shift_line_integral' (t : ℝ) (hleft : Integrable (fun y : ℝ => fk t (-1 + y * I))) :
    (∫ y : ℝ, fk t (1 + y * I)) = (∫ y : ℝ, fk t (-1 + y * I)) +
      2 * Real.pi * (4 * Complex.exp (t / 2) + (deriv F 0 + t * F 0) -
        ∑' ρ : Z, (mult (ρ : ℂ) : ℂ) * kern t ((ρ : ℂ) - 1 / 2)) :=
  shift_line_integral riemannZeta_half_ne_zero t hleft

end ScrewRH
