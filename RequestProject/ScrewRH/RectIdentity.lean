module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import RequestProject.ScrewRH.LocalExpansions
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompletedLFunctionNeZeroOfReNonpos

@[expose] public section

/-!
# ScrewRH.RectIdentity: the residue theorem on `[-1, 1] × [-T, T]` (blueprint lemma 6, right part)

Interface.
* `zerosBelow T = {ρ ∈ Z | |ρ.im| < T}`; `zerosBelow_finite T` says it is finite.
* `mem_Z_of_zeta_half_add`: for `-1 ≤ re z`, `ζ(1/2 + z) = 0` forces `1/2 + z ∈ Z`;
  `riemannZeta_ne_zero_of_strip`: no zeros with `-1/2 ≤ re s ≤ 0`.
  Real parts `≥ 1` use Mathlib; real parts `≤ 0` use the ported `LFunction_zero_of_re_nonpos`.
* `rect_identity hhalf t hT hside`: let `T > 0` be such that `ζ(1/2 + z) ≠ 0` on both horizontal
  edges `|im z| = T`, `-1 ≤ re z ≤ 1`. Then
  `bdInt (-1) 1 (-T) T (fk t) = 2πi (4 e^{t/2} + (F'(0) + t F(0)) - ∑ᶠ ρ ∈ zerosBelow T, m(ρ) kern t (ρ - 1/2))`.
  Here `bdInt a b c d f = ∫_a^b f(x+ci) - ∫_a^b f(x+di) + i∫_c^d f(b+iy) - i∫_c^d f(a+iy)`
  (`GlobalTheory.ResRect.bdInt`). The hypothesis `hhalf : riemannZeta (1/2) ≠ 0` is used for
  the residue at `0`, and to show that `0` is not the shift of a zero.
-/

open Complex Filter Topology MeasureTheory

namespace ScrewRH

/-- The nontrivial zeros with `|Im ρ| < T`. -/
def zerosBelow (T : ℝ) : Set ℂ := {ρ | ρ ∈ Z ∧ |ρ.im| < T}

lemma zerosBelow_finite (T : ℝ) : (zerosBelow T).Finite := by
  refine (GlobalTheory.ExplicitRect.finite_zeros (1 : DirichletCharacter ℂ 1) T).subset ?_
  rintro ρ ⟨⟨h0, h1, h2⟩, hT⟩
  refine ⟨h1, h2, hT, ?_⟩
  rw [← riemannZeta_eq_LFunction_one]
  exact h0

/-- `ζ` has no zeros with `-1/2 ≤ re s ≤ 0`. -/
lemma riemannZeta_ne_zero_of_strip {s : ℂ} (h1 : -(1 / 2 : ℝ) ≤ s.re) (h2 : s.re ≤ 0) :
    riemannZeta s ≠ 0 := by
  intro hs
  rw [riemannZeta_eq_LFunction_one] at hs
  obtain ⟨⟨n, hn⟩, -, h0, -⟩ := GlobalTheory.LFunction_zero_of_re_nonpos 1 1
    (DirichletCharacter.isPrimitive_one_level_one) s h2 hs
  have hre : s.re = -(n : ℝ) := by rw [hn]; simp
  have hn0 : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    linarith
  exact (h0 (by rw [hn, hn0]; simp)).2 rfl

/-- Zeros of `ζ(1/2 + z)` with `-1 ≤ re z` are nontrivial zeros. -/
lemma mem_Z_of_zeta_half_add {z : ℂ} (h1 : -1 ≤ z.re)
    (hz : riemannZeta (1 / 2 + z) = 0) : 1 / 2 + z ∈ Z := by
  have hre : (1 / 2 + z).re = 1 / 2 + z.re := by simp
  refine ⟨hz, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_strip (by rw [hre]; linarith) h hz
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hz

/-- **Blueprint lemma 6 (right rectangle).** -/
theorem rect_identity (hhalf : riemannZeta (1 / 2) ≠ 0) (t : ℝ) {T : ℝ} (hT : 0 < T)
    (hside : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 1 → |z.im| = T → riemannZeta (1 / 2 + z) ≠ 0) :
    GlobalTheory.ResRect.bdInt (-1) 1 (-T) T (fk t) =
      2 * Real.pi * I * (4 * Complex.exp (t / 2) + (deriv F 0 + t * F 0) -
        ∑ᶠ ρ ∈ zerosBelow T, (mult ρ : ℂ) * kern t (ρ - 1 / 2)) := by
  classical
  have hfin := zerosBelow_finite T
  set Zs : Finset ℂ := hfin.toFinset with hZs
  have hmemZs : ∀ ρ, ρ ∈ Zs ↔ ρ ∈ Z ∧ |ρ.im| < T := fun ρ => by
    rw [hZs, Set.Finite.mem_toFinset]; rfl
  set Im : Finset ℂ := Zs.image (fun ρ => ρ - 1 / 2) with hIm
  have hinj : Set.InjOn (fun ρ : ℂ => ρ - 1 / 2) Zs := fun a _ b _ h => by
    simpa using h
  have h0Im : (0 : ℂ) ∉ Im := by
    intro h
    obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
    have : ρ = 1 / 2 := by linear_combination e
    exact hhalf (this ▸ ((hmemZs ρ).1 hρ).1.1)
  have hhIm : (1 / 2 : ℂ) ∉ insert 0 Im := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · norm_num at h
    obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
    have : ρ = 1 := by linear_combination e
    have := ((hmemZs ρ).1 hρ).1.2.2
    simp_all
  set S : Finset ℂ := insert (1 / 2) (insert 0 Im) with hS
  let r : ℂ → ℂ := fun p => if p = 1 / 2 then 4 * Complex.exp (t / 2)
    else if p = 0 then deriv F 0 + t * F 0
    else -(mult (p + 1 / 2) : ℂ) * kern t p
  have hins : ∀ p ∈ S, (⟨-1, -T⟩ : ℂ).re < p.re ∧ p.re < (⟨1, T⟩ : ℂ).re ∧
      (⟨-1, -T⟩ : ℂ).im < p.im ∧ p.im < (⟨1, T⟩ : ℂ).im := by
    intro p hp
    show -1 < p.re ∧ p.re < 1 ∧ -T < p.im ∧ p.im < T
    rcases Finset.mem_insert.1 hp with rfl | hp
    · norm_num; exact hT
    rcases Finset.mem_insert.1 hp with rfl | hp
    · simp; exact hT
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨⟨-, h0, h1⟩, hT'⟩ := (hmemZs ρ).1 hρ
    rw [abs_lt] at hT'
    simp only [sub_re, sub_im]
    norm_num
    refine ⟨by linarith, by linarith, hT'.1, hT'.2⟩
  have hdiff : DifferentiableOn ℂ (fk t) ((Set.Icc (⟨-1, -T⟩ : ℂ).re (⟨1, T⟩ : ℂ).re ×ℂ
      Set.Icc (⟨-1, -T⟩ : ℂ).im (⟨1, T⟩ : ℂ).im) \ ↑S) := by
    intro z hz
    obtain ⟨hzR, hzS⟩ := hz
    rw [Complex.mem_reProdIm] at hzR
    obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩⟩ := hzR
    change -1 ≤ z.re at hre1
    change z.re ≤ 1 at hre2
    change -T ≤ z.im at him1
    change z.im ≤ T at him2
    have hzh : z ≠ 1 / 2 := fun h => hzS (by simp [S, h])
    have hz0 : z ≠ 0 := fun h => hzS (by simp [S, h])
    have h1 : 1 / 2 + z ≠ 1 := fun h => hzh (by linear_combination h)
    have hζ : riemannZeta (1 / 2 + z) ≠ 0 := by
      intro hζ
      by_cases hI : |z.im| = T
      · exact hside z hre1 hre2 hI hζ
      have hI' : |z.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨him1, him2⟩) hI
      apply hzS
      have hmem : 1 / 2 + z ∈ Zs := (hmemZs _).2
        ⟨mem_Z_of_zeta_half_add hre1 hζ, by simpa using hI'⟩
      have : z ∈ Im := Finset.mem_image.2 ⟨1 / 2 + z, hmem, by ring⟩
      simp [S, this]
    exact (differentiableAt_fk t hz0 h1 hζ).differentiableWithinAt
  have hexp : ∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧
      ∀ᶠ s in nhdsWithin p {p}ᶜ, fk t s = a / (s - p) ^ 2 + r p / (s - p) + g s := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · have hr : r (1 / 2) = 4 * Complex.exp (t / 2) := by simp [r]
      rw [hr]; exact fk_expansion_half t
    rcases Finset.mem_insert.1 hp with rfl | hp
    · have hr : r 0 = deriv F 0 + t * F 0 := by simp [r]
      rw [hr]; exact fk_expansion_zero hhalf t
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hp
    have hρZ := ((hmemZs ρ).1 hρ).1
    have hρ1 : ρ ≠ 1 := by rintro rfl; simp [Z] at hρZ
    have hρh : ρ ≠ 1 / 2 := by rintro rfl; exact hhalf hρZ.1
    have hp0 : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρh
    have hph : ρ - 1 / 2 ≠ 1 / 2 := fun h => hρ1 (by linear_combination h)
    have hr : r (ρ - 1 / 2) = -(mult ρ : ℂ) * kern t (ρ - 1 / 2) := by
      simp only [r, hph, hp0, ↓reduceIte, sub_add_cancel]
    rw [hr]; exact fk_expansion_zero_shift hρ1 hρh t
  have key := GlobalTheory.ResRect.residue_rectangle (fk t) ⟨-1, -T⟩ ⟨1, T⟩ S r
    (show (-1 : ℝ) < 1 by norm_num) (show -T < T by linarith) hins hdiff hexp
  have e : GlobalTheory.ResRect.bdInt (-1) 1 (-T) T (fk t) = 2 * Real.pi * I * ∑ p ∈ S, r p := key
  rw [e]
  have hr1 : r (1 / 2) = 4 * Complex.exp (t / 2) := by simp [r]
  have hr0 : r 0 = deriv F 0 + t * F 0 := by simp [r]
  have hrZ : ∑ p ∈ Im, r p = -∑ ρ ∈ Zs, (mult ρ : ℂ) * kern t (ρ - 1 / 2) := by
    rw [hIm, Finset.sum_image hinj, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρZ := ((hmemZs ρ).1 hρ).1
    have hρ1 : ρ ≠ 1 := by rintro rfl; simp [Z] at hρZ
    have hρh : ρ ≠ 1 / 2 := by rintro rfl; exact hhalf hρZ.1
    have hp0 : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρh
    have hph : ρ - 1 / 2 ≠ 1 / 2 := fun h => hρ1 (by linear_combination h)
    simp only [r, hph, hp0, ↓reduceIte, sub_add_cancel]
    ring
  rw [hS, Finset.sum_insert hhIm, Finset.sum_insert h0Im, hr1, hr0, hrZ,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  ring

end ScrewRH
