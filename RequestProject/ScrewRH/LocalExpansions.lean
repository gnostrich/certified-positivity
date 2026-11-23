module

public import Mathlib
public import RequestProject.ScrewRH.Defs
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AnalyticAtDslope

@[expose] public section

/-!
# ScrewRH.LocalExpansions: residues of `F · kern t` (blueprint lemma 5)

Interface. Write `fk t z = F z * kern t z`. Each lemma below gives a local expansion
`fk t z = a / (z - p) ^ 2 + r / (z - p) + G z` on a punctured neighbourhood of `p`, with `G`
analytic at `p`. This is the hypothesis shape of `GlobalTheory.ResRect.residue_rectangle`.

* `fk_expansion_half t`: at `p = 1/2`, `r = 4 * exp (t / 2)` (the pole of `ζ` at `1`).
* `fk_expansion_zero hhalf t`: at `p = 0`, `r = deriv F 0 + t * F 0`. This needs
  `hhalf : riemannZeta (1/2) ≠ 0`.
* `fk_expansion_zero_shift hρ1 hρ t`: at `p = ρ - 1/2` for `ρ ≠ 1`, `ρ ≠ 1/2`,
  `r = -(mult ρ) * kern t (ρ - 1/2)`. No zero hypothesis is needed: if `ζ ρ ≠ 0`, then
  `mult ρ = 0` and the statement still holds.
* `differentiableAt_fk`: `fk t` is complex differentiable at every `z ≠ 0` with `1/2 + z ≠ 1`
  and `ζ (1/2 + z) ≠ 0`.
-/

open Complex Filter Topology

namespace ScrewRH

/-- The integrand `F z * e^{zt} / z²`. -/
noncomputable def fk (t : ℝ) (z : ℂ) : ℂ := F z * kern t z

lemma riemannZeta_eq_LFunction_one :
    riemannZeta = DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) :=
  DirichletCharacter.LFunction_modOne_eq.symm

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  rw [riemannZeta_eq_LFunction_one]
  exact GlobalTheory.ExplicitRect.analyticOff _ s hs

lemma analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  rw [riemannZeta_eq_LFunction_one]
  exact GlobalTheory.ExplicitRect.order_ne_top _ hs

lemma analyticAt_kern (t : ℝ) {p : ℂ} (hp : p ≠ 0) : AnalyticAt ℂ (kern t) p := by
  unfold kern
  exact ((analyticAt_id.mul analyticAt_const).cexp).div (analyticAt_id.pow 2) (pow_ne_zero 2 hp)

lemma analyticAt_F {z : ℂ} (h1 : 1 / 2 + z ≠ 1) (h0 : riemannZeta (1 / 2 + z) ≠ 0) :
    AnalyticAt ℂ F z := by
  have hz : AnalyticAt ℂ riemannZeta (1 / 2 + z) := analyticAt_riemannZeta h1
  have hc : AnalyticAt ℂ (fun w : ℂ => 1 / 2 + w) z := analyticAt_const.add analyticAt_id
  unfold F
  exact ((hz.deriv.comp hc).div (hz.comp hc) h0).neg

lemma differentiableAt_fk (t : ℝ) {z : ℂ} (hz : z ≠ 0) (h1 : 1 / 2 + z ≠ 1)
    (h0 : riemannZeta (1 / 2 + z) ≠ 0) : DifferentiableAt ℂ (fk t) z :=
  ((analyticAt_F h1 h0).mul (analyticAt_kern t hz)).differentiableAt

/-- The shift `z ↦ 1/2 + z` maps punctured neighbourhoods to punctured neighbourhoods. -/
lemma tendsto_half_add (p : ℂ) :
    Tendsto (fun z : ℂ => 1 / 2 + z) (𝓝[≠] p) (𝓝[≠] (1 / 2 + p)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact (Continuous.tendsto (by fun_prop : Continuous fun z : ℂ => 1 / 2 + z) p).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

/-- Multiplying a function with a simple pole by an analytic function. -/
lemma expand_mul_simple {φ K g : ℂ → ℂ} {p k : ℂ} (hK : AnalyticAt ℂ K p)
    (hg : AnalyticAt ℂ g p) (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G p ∧ ∀ᶠ s in 𝓝[≠] p,
      φ s * K s = a / (s - p) ^ 2 + (k * K p) / (s - p) + G s := by
  refine ⟨0, fun s => k * dslope K p s + g s * K s,
    (analyticAt_const.mul (GlobalTheory.ExplicitRect.analyticAt_dslope hK)).add (hg.mul hK), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hexp := GlobalTheory.ExplicitRect.eq_add_dslope K p s
  rw [hs, hexp]
  field_simp
  ring

/-- An analytic function divided by `s²`. -/
lemma expand_div_sq {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      H s / s ^ 2 = a / (s - 0) ^ 2 + deriv H 0 / (s - 0) + G s := by
  have hD1 := GlobalTheory.ExplicitRect.analyticAt_dslope hH
  have hD2 := GlobalTheory.ExplicitRect.analyticAt_dslope hD1
  refine ⟨H 0, dslope (dslope H 0) 0, hD2, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs0
  have hs0' : s ≠ 0 := hs0
  have e1 := GlobalTheory.ExplicitRect.eq_add_dslope H 0 s
  have e2 := GlobalTheory.ExplicitRect.eq_add_dslope (dslope H 0) 0 s
  rw [dslope_same] at e2
  simp only [sub_zero] at e1 e2 ⊢
  rw [e1, e2]
  field_simp
  ring

/-- `F` has a simple pole with residue `1` at `1/2`. -/
lemma F_expansion_half : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (1 / 2) ∧
    ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), F z = 1 / (z - 1 / 2) + g z := by
  obtain ⟨g, hg, hφ⟩ := GlobalTheory.ExplicitRect.logDeriv_one
    (DirichletCharacter.isPrimitive_one_level_one (R := ℂ))
  rw [← riemannZeta_eq_LFunction_one] at hφ
  simp only [ite_true] at hφ
  have hc : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  refine ⟨fun z => -g (1 / 2 + z), ?_, ?_⟩
  · have : AnalyticAt ℂ g (1 / 2 + 1 / 2) := by rw [hc]; exact hg
    exact (this.comp (analyticAt_const.add analyticAt_id)).neg
  · have ht := tendsto_half_add (1 / 2 : ℂ)
    rw [hc] at ht
    filter_upwards [ht.eventually hφ] with z hz
    unfold F
    rw [hz]
    have : (1 / 2 + z - 1 : ℂ) = z - 1 / 2 := by ring
    rw [this]
    ring

/-- At `ρ - 1/2` (`ρ ≠ 1`), `F` has a simple pole with residue `-mult ρ`. -/
lemma F_expansion_shift {ρ : ℂ} (hρ1 : ρ ≠ 1) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (ρ - 1 / 2) ∧
    ∀ᶠ z in 𝓝[≠] (ρ - 1 / 2), F z = (-(mult ρ : ℂ)) / (z - (ρ - 1 / 2)) + g z := by
  obtain ⟨g, hg, hφ⟩ := GlobalTheory.ExplicitRect.logDeriv_pole (analyticAt_riemannZeta hρ1)
    (analyticOrderAt_riemannZeta_ne_top hρ1)
  have hc : (1 / 2 + (ρ - 1 / 2) : ℂ) = ρ := by ring
  refine ⟨fun z => -g (1 / 2 + z), ?_, ?_⟩
  · have : AnalyticAt ℂ g (1 / 2 + (ρ - 1 / 2)) := by rw [hc]; exact hg
    exact (this.comp (analyticAt_const.add analyticAt_id)).neg
  · have ht := tendsto_half_add (ρ - 1 / 2)
    rw [hc] at ht
    filter_upwards [ht.eventually hφ] with z hz
    unfold F
    rw [hz]
    have : (1 / 2 + z - ρ : ℂ) = z - (ρ - 1 / 2) := by ring
    rw [this, mult]
    ring

lemma kern_half (t : ℝ) : kern t (1 / 2) = 4 * Complex.exp (t / 2) := by
  unfold kern
  have : (1 / 2 : ℂ) * t = t / 2 := by ring
  rw [this]
  norm_num
  ring

/-- **Residue at `1/2`.** -/
theorem fk_expansion_half (t : ℝ) : ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G (1 / 2) ∧
    ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ),
      fk t z = a / (z - 1 / 2) ^ 2 + (4 * Complex.exp (t / 2)) / (z - 1 / 2) + G z := by
  obtain ⟨g, hg, hF⟩ := F_expansion_half
  obtain ⟨a, G, hG, h⟩ := expand_mul_simple (analyticAt_kern t (by norm_num)) hg hF
  refine ⟨a, G, hG, ?_⟩
  filter_upwards [h] with z hz
  rw [fk, hz, kern_half, one_mul]

/-- **Residue at `ρ - 1/2`.** -/
theorem fk_expansion_zero_shift {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : ρ ≠ 1 / 2) (t : ℝ) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G (ρ - 1 / 2) ∧
    ∀ᶠ z in 𝓝[≠] (ρ - 1 / 2), fk t z = a / (z - (ρ - 1 / 2)) ^ 2 +
      (-(mult ρ : ℂ) * kern t (ρ - 1 / 2)) / (z - (ρ - 1 / 2)) + G z := by
  obtain ⟨g, hg, hF⟩ := F_expansion_shift hρ1
  have hp : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
  exact expand_mul_simple (analyticAt_kern t hp) hg hF

/-- **Residue at `0`** (double pole of the kernel). -/
theorem fk_expansion_zero (hhalf : riemannZeta (1 / 2) ≠ 0) (t : ℝ) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G 0 ∧
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), fk t z = a / (z - 0) ^ 2 + (deriv F 0 + t * F 0) / (z - 0) + G z := by
  have hFa : AnalyticAt ℂ F 0 :=
    analyticAt_F (by norm_num) (by simpa using hhalf)
  have hE : AnalyticAt ℂ (fun z : ℂ => Complex.exp (z * t)) 0 :=
    (analyticAt_id.mul analyticAt_const).cexp
  obtain ⟨a, G, hG, h⟩ := expand_div_sq (H := fun z => F z * Complex.exp (z * t)) (hFa.mul hE)
  have hd : deriv (fun z => F z * Complex.exp (z * t)) 0 = deriv F 0 + t * F 0 := by
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (z * t)) (Complex.exp (0 * t) * (1 * t)) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const (t : ℂ)).cexp
    rw [(hFa.differentiableAt.hasDerivAt.fun_mul h1).deriv]
    simp
    ring
  refine ⟨a, G, hG, ?_⟩
  filter_upwards [h] with z hz
  rw [← hd, ← hz, fk, kern]
  ring

end ScrewRH
