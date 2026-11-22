-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
public import AlpogeRH.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompletedLFunctionNeZeroOfReNonpos

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ExplicitRect

theorem analyticAt_dslope {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  obtain ⟨q, hq⟩ := hf
  exact ⟨_, hq.has_fpower_series_dslope_fslope⟩

theorem eq_add_dslope (f : ℂ → ℂ) (p s : ℂ) : f s = f p + (s - p) * dslope f p s := by
  have h := sub_smul_dslope f p s
  rw [smul_eq_mul] at h
  linear_combination -h

theorem logDeriv_pole {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hn : analyticOrderAt f p ≠ ⊤) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p,
      deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  obtain ⟨g0, hg0, hg0p, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := analyticOrderNatAt f p)).mp (Nat.cast_analyticOrderNatAt hn).symm
  generalize analyticOrderNatAt f p = n at hfg ⊢
  refine ⟨fun s => deriv g0 s / g0 s, hg0.deriv.div hg0 hg0p, ?_⟩
  have hne : ∀ᶠ s in 𝓝 p, g0 s ≠ 0 := hg0.continuousAt.eventually_ne hg0p
  have hdiff : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ g0 s :=
    hg0.eventually_analyticAt.mono fun s hs => hs.differentiableAt
  filter_upwards [nhdsWithin_le_nhds hne, nhdsWithin_le_nhds hfg.eventually_nhds,
    nhdsWithin_le_nhds hdiff, nhdsWithin_le_nhds hfg, self_mem_nhdsWithin] with s h1 h2 h3 h4 h5
  have hsp : s - p ≠ 0 := sub_ne_zero.mpr h5
  have hd : HasDerivAt (fun z => (z - p) ^ n • g0 z)
      ((n : ℂ) * (s - p) ^ (n - 1) * 1 * g0 s + (s - p) ^ n * deriv g0 s) s := by
    have := (((hasDerivAt_id' s).sub_const p).pow n).mul h3.hasDerivAt
    convert this using 1
    all_goals rfl
  have h2' : f =ᶠ[𝓝 s] fun z => (z - p) ^ n • g0 z := h2
  rw [h2'.deriv_eq, h4, hd.deriv, smul_eq_mul]
  rcases n with _ | k
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp

theorem analyticAt_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p := analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.2 hu)

theorem expand_simple {φ g : ℂ → ℂ} {p k : ℂ} {u : ℝ} (hu : 0 < u) (hp : p ≠ 0)
    (hg : AnalyticAt ℂ g p) (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(φ s) * (u : ℂ) ^ s / s = a / (s - p) ^ 2 + (-(k * ((u : ℂ) ^ p / p))) / (s - p) + G s := by
  have hW : AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s / s) p :=
    (analyticAt_cpow hu p).div analyticAt_id hp
  refine ⟨0, fun s => -(k * dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s) - g s * ((u : ℂ) ^ s / s),
    ((analyticAt_const.mul (analyticAt_dslope hW)).neg).sub (hg.mul hW), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hexp : (u : ℂ) ^ s / s = (u : ℂ) ^ p / p + (s - p) * dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s :=
    eq_add_dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s
  rw [hs, mul_div_assoc, hexp]
  field_simp
  ring

theorem expand_zero {φ h : ℂ → ℂ} {m : ℂ} {u : ℝ} (hu : 0 < u)
    (hh : AnalyticAt ℂ h 0) (hφ : ∀ᶠ s in 𝓝[≠] (0 : ℂ), φ s = m / s + h s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(φ s) * (u : ℂ) ^ s / s =
        a / (s - 0) ^ 2 + (-(m * (Real.log u : ℂ) + h 0)) / (s - 0) + G s := by
  have hE : AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) 0 := analyticAt_cpow hu 0
  have hD1 := analyticAt_dslope hE
  have hD2 := analyticAt_dslope hD1
  have hDh := analyticAt_dslope hh
  have hD10 : dslope (fun s : ℂ => (u : ℂ) ^ s) 0 0 = (Real.log u : ℂ) := by
    rw [dslope_same]
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    rw [(hasStrictDerivAt_const_cpow (x := (u : ℂ)) (y := 0) (.inl hu0)).hasDerivAt.deriv,
      Complex.cpow_zero, one_mul, Complex.ofReal_log hu.le]
  refine ⟨-m, fun s => -(m * dslope (dslope (fun s : ℂ => (u : ℂ) ^ s) 0) 0 s + dslope h 0 s +
      h s * (Real.log u : ℂ) + h s * s * dslope (dslope (fun s : ℂ => (u : ℂ) ^ s) 0) 0 s),
    ((((analyticAt_const.mul hD2).add hDh).add (hh.mul analyticAt_const)).add
      ((hh.mul analyticAt_id).mul hD2)).neg, ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hs0
  have hs0' : s ≠ 0 := hs0
  have e1 := eq_add_dslope (fun s : ℂ => (u : ℂ) ^ s) 0 s
  have e2 := eq_add_dslope (dslope (fun s : ℂ => (u : ℂ) ^ s) 0) 0 s
  have eh := eq_add_dslope h 0 s
  simp only [Complex.cpow_zero, sub_zero] at e1 e2 eh
  rw [hD10] at e2
  rw [hs, e1, e2]
  simp only [sub_zero]
  rw [eh]
  field_simp
  ring

theorem analyticOff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := DifferentiableOn.analyticOnNhd
    (fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt)
    isOpen_compl_singleton

theorem exists_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 1 ≠ 0 ∧ ∀ s, s ≠ 1 → LFunction χ s = 0 → F s = 0 := by
  by_cases h1 : χ = 1
  · subst h1
    refine ⟨DirichletCharacter.LFunctionTrivChar₁ q, DirichletCharacter.differentiable_LFunctionTrivChar₁ q,
      DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs hL => ?_⟩
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]
    show (s - 1) * LFunction 1 s = 0
    rw [hL, mul_zero]
  · exact ⟨LFunction χ, DirichletCharacter.differentiable_LFunction h1,
      DirichletCharacter.LFunction_apply_one_ne_zero h1, fun s _ h => h⟩

theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite := by
  obtain ⟨F, hF, hF1, hFz⟩ := exists_entire χ
  have hZc : IsCompact ({ρ : ℂ | F ρ = 0} ∩ Metric.closedBall 0 (1 + T)) :=
    (isCompact_closedBall 0 (1 + T)).inter_left (isClosed_eq hF.continuous continuous_const)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  rcases hFa.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact absurd (h (Set.mem_univ 1)) hF1
  have hd : IsDiscrete ({ρ : ℂ | F ρ = 0} ∩ Metric.closedBall 0 (1 + T)) := by
    rw [isDiscrete_iff_nhdsNE]
    intro x _
    rw [Filter.eventually_iff, mem_codiscreteWithin] at h
    have hx := h x (Set.mem_univ _)
    rw [disjoint_iff] at hx
    have hsub : {ρ : ℂ | F ρ = 0} ∩ Metric.closedBall 0 (1 + T) ⊆ Set.univ \ {x | F x ≠ 0} :=
      fun y hy => ⟨Set.mem_univ _, fun h' => h' hy.1⟩
    exact le_bot_iff.mp ((inf_le_inf_left _ (Filter.principal_mono.mpr hsub)).trans hx.le)
  refine (hZc.finite hd).subset fun ρ hρ => ?_
  obtain ⟨h0, h1, hT, hL⟩ := hρ
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp at h1
  refine ⟨hFz ρ hρ1 hL, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
  rw [abs_of_pos h0]
  linarith

theorem order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  have h2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    intro htop
    have hne : LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num)
    exact hne (analyticOrderAt_eq_top.mp htop).self_of_nhds
  exact (analyticOff χ).analyticOrderAt_ne_top_of_isPreconnected hU
    (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) hρ h2

theorem logDeriv_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      deriv (LFunction χ) s / LFunction χ s = (if N = 1 then -1 else 0) / (s - 1) + g s := by
  by_cases hN : N = 1
  · subst hN
    obtain rfl : χ = 1 := DirichletCharacter.level_one χ
    have hZd := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    have hZa : AnalyticAt ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) 1 := hZd.analyticAt 1
    have hZ1 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
    refine ⟨fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s /
      DirichletCharacter.LFunctionTrivChar₁ 1 s, hZa.deriv.div hZa hZ1, ?_⟩
    have hne : ∀ᶠ s in 𝓝 (1 : ℂ), DirichletCharacter.LFunctionTrivChar₁ 1 s ≠ 0 :=
      hZa.continuousAt.eventually_ne hZ1
    filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with s hZs hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hLeq : LFunction (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 s]
        fun z => DirichletCharacter.LFunctionTrivChar₁ 1 z / (z - 1) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz]
      field_simp
    have hd : HasDerivAt (fun z => DirichletCharacter.LFunctionTrivChar₁ 1 z / (z - 1))
        ((deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s * (s - 1) -
          DirichletCharacter.LFunctionTrivChar₁ 1 s * 1) / (s - 1) ^ 2) s :=
      (hZd s).hasDerivAt.div ((hasDerivAt_id' s).sub_const 1) hs1'
    rw [hLeq.deriv_eq, hLeq.eq_of_nhds, hd.deriv, if_pos rfl]
    field_simp
    ring
  · have hχ1 : χ ≠ 1 := by
      rintro rfl
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hχ
      exact hN hχ.symm
    have hLa : AnalyticAt ℂ (LFunction χ) 1 := (DirichletCharacter.differentiable_LFunction hχ1).analyticAt 1
    have hL1 := DirichletCharacter.LFunction_apply_one_ne_zero hχ1
    refine ⟨fun s => deriv (LFunction χ) s / LFunction χ s, hLa.deriv.div hLa hL1,
      Filter.Eventually.of_forall fun s => ?_⟩
    simp only [hN, if_false, zero_div, zero_add]

theorem residue_identity : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ (u c T : ℝ) (m : ℕ) (h : ℂ → ℂ), 1 < u → 1 < c → 0 < T → AnalyticAt ℂ h 0 → (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (LFunction χ) s / LFunction χ s = (m : ℂ) / s + h s) → (∀ s : ℂ, -(1/2 : ℝ) ≤ s.re → s.re ≤ c → |s.im| = T → LFunction χ s ≠ 0) → (∀ s : ℂ, s.re = -(1/2 : ℝ) → LFunction χ s ≠ 0) → (∫ x : ℝ in (-(1/2 : ℝ))..c, (-(deriv (LFunction χ) ((x : ℂ) - T * I) / LFunction χ ((x : ℂ) - T * I)) * (u : ℂ) ^ ((x : ℂ) - T * I) / ((x : ℂ) - T * I))) - (∫ x : ℝ in (-(1/2 : ℝ))..c, (-(deriv (LFunction χ) ((x : ℂ) + T * I) / LFunction χ ((x : ℂ) + T * I)) * (u : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I))) + I * (∫ t : ℝ in (-T)..T, (-(deriv (LFunction χ) ((c : ℂ) + t * I) / LFunction χ ((c : ℂ) + t * I)) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) - I * (∫ t : ℝ in (-T)..T, (-(deriv (LFunction χ) (((-(1/2) : ℝ) : ℂ) + t * I) / LFunction χ (((-(1/2) : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + t * I) / (((-(1/2) : ℝ) : ℂ) + t * I))) = 2 * Real.pi * I * ((if N = 1 then (u : ℂ) else 0) - (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)) - (m * (Real.log u : ℂ) + h 0)) := by
  intro N _ χ hχ u c T m h hu hc hT hh hφ0 hside hleft
  have hu0 : (0 : ℝ) < u := by linarith
  let f : ℂ → ℂ := fun s => -(deriv (LFunction χ) s / LFunction χ s) * (u : ℂ) ^ s / s
  have hZfin := finite_zeros χ T
  have h0Z : (0 : ℂ) ∉ hZfin.toFinset := by simp
  have h1Z : (1 : ℂ) ∉ hZfin.toFinset := by simp
  have h1S : (1 : ℂ) ∉ insert (0 : ℂ) hZfin.toFinset := by
    simp only [Finset.mem_insert, one_ne_zero, false_or]; exact h1Z
  let S : Finset ℂ := insert 1 (insert 0 hZfin.toFinset)
  let r : ℂ → ℂ := fun p => if p = 1 then -((if N = 1 then (-1 : ℂ) else 0) * ((u : ℂ) ^ p / p))
    else if p = 0 then -(m * (Real.log u : ℂ) + h 0)
    else -((analyticOrderNatAt (LFunction χ) p : ℕ) * ((u : ℂ) ^ p / p))
  have hins : ∀ p ∈ S, (⟨-(1/2), -T⟩ : ℂ).re < p.re ∧ p.re < (⟨c, T⟩ : ℂ).re ∧
      (⟨-(1/2), -T⟩ : ℂ).im < p.im ∧ p.im < (⟨c, T⟩ : ℂ).im := by
    intro p hp
    show -(1/2 : ℝ) < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | ⟨h0, h1, hT', -⟩
    · exact ⟨by simp only [Complex.one_re]; linarith, by simp only [Complex.one_re]; linarith,
        by simp only [Complex.one_im]; linarith, by simp only [Complex.one_im]; linarith⟩
    · exact ⟨by simp only [Complex.zero_re]; linarith, by simp only [Complex.zero_re]; linarith,
        by simp only [Complex.zero_im]; linarith, by simp only [Complex.zero_im]; linarith⟩
    · rw [abs_lt] at hT'
      exact ⟨by linarith, by linarith, hT'.1, hT'.2⟩
  have hdiff : DifferentiableOn ℂ f ((Set.Icc (⟨-(1/2), -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ
      Set.Icc (⟨-(1/2), -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im) \ ↑S) := by
    intro s hs
    obtain ⟨hsR, hsS⟩ := hs
    rw [Complex.mem_reProdIm] at hsR
    obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩⟩ := hsR
    change -(1/2 : ℝ) ≤ s.re at hre1
    change s.re ≤ c at hre2
    change -T ≤ s.im at him1
    change s.im ≤ T at him2
    have hs1 : s ≠ 1 := fun h' => hsS (by simp [S, h'])
    have hs0 : s ≠ 0 := fun h' => hsS (by simp [S, h'])
    have hLs : LFunction χ s ≠ 0 := by
      intro hL
      by_cases hI : |s.im| = T
      · exact hside s hre1 hre2 hI hL
      by_cases hRe : s.re = -(1/2 : ℝ)
      · exact hleft s hRe hL
      by_cases h1 : 1 ≤ s.re
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr hs1) h1 hL
      by_cases h0 : s.re ≤ 0
      · obtain ⟨⟨n, hn⟩, -⟩ := GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ s h0 hL
        have hre : s.re = -(n : ℝ) := by rw [hn]; simp
        have hn0 : n = 0 := by
          by_contra hne
          have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
        exact hs0 (by rw [hn, hn0]; simp)
      · have hI' : |s.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨him1, him2⟩) hI
        apply hsS
        simp only [S, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Set.Finite.mem_toFinset,
          Set.mem_ofPred_eq]
        exact Or.inr (Or.inr ⟨by linarith, by linarith, hI', hL⟩)
    have hLa : AnalyticAt ℂ (LFunction χ) s := analyticOff χ s hs1
    have hd1 : DifferentiableAt ℂ (deriv (LFunction χ)) s := hLa.deriv.differentiableAt
    have hd2 : DifferentiableAt ℂ (fun s : ℂ => (u : ℂ) ^ s) s := (analyticAt_cpow hu0 s).differentiableAt
    exact (((hd1.div hLa.differentiableAt hLs).neg.mul hd2).div differentiableAt_id hs0).differentiableWithinAt
  have hexp : ∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧
      ∀ᶠ s in nhdsWithin p {p}ᶜ, f s = a / (s - p) ^ 2 + r p / (s - p) + g s := by
    intro p hp
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | hpZ
    · obtain ⟨g1, hg1, hφ1⟩ := logDeriv_one hχ
      obtain ⟨a, G, hG, hfe⟩ := expand_simple
        (φ := fun s => deriv (LFunction χ) s / LFunction χ s) hu0 one_ne_zero hg1 hφ1
      have hr : r 1 = -((if N = 1 then (-1 : ℂ) else 0) * ((u : ℂ) ^ (1 : ℂ) / 1)) := by simp [r]
      exact ⟨a, G, hG, by rw [hr]; exact hfe⟩
    · obtain ⟨a, G, hG, hfe⟩ := expand_zero
        (φ := fun s => deriv (LFunction χ) s / LFunction χ s) hu0 hh hφ0
      have hr : r 0 = -(m * (Real.log u : ℂ) + h 0) := by simp [r]
      exact ⟨a, G, hG, by rw [hr]; exact hfe⟩
    · have hp1 : p ≠ 1 := by rintro rfl; simp at hpZ
      have hp0 : p ≠ 0 := by rintro rfl; simp at hpZ
      obtain ⟨g, hg, hφp⟩ := logDeriv_pole (analyticOff χ p hp1) (order_ne_top χ hp1)
      obtain ⟨a, G, hG, hfe⟩ := expand_simple
        (φ := fun s => deriv (LFunction χ) s / LFunction χ s) hu0 hp0 hg hφp
      have hr : r p = -((analyticOrderNatAt (LFunction χ) p : ℕ) * ((u : ℂ) ^ p / p)) := by
        simp [r, hp1, hp0]
      exact ⟨a, G, hG, by rw [hr]; exact hfe⟩
  have key : (∫ x : ℝ in (-(1/2) : ℝ)..c, f (x + ((-T : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (-(1/2) : ℝ)..c, f (x + (T : ℂ) * I)) +
      I * (∫ y : ℝ in (-T)..T, f ((c : ℂ) + y * I)) -
      I * (∫ y : ℝ in (-T)..T, f (((-(1/2) : ℝ) : ℂ) + y * I)) = 2 * Real.pi * I * ∑ p ∈ S, r p :=
    GlobalTheory.ResRect.residue_rectangle f ⟨-(1/2), -T⟩ ⟨c, T⟩ S r
      (show (-(1/2) : ℝ) < c by linarith) (show -T < T by linarith) hins hdiff hexp
  have e : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * I = (x : ℂ) + ((-T : ℝ) : ℂ) * I := by
    intro x; push_cast; ring
  simp only [e]
  refine key.trans ?_
  have hr1 : r 1 = if N = 1 then (u : ℂ) else 0 := by
    simp only [r, if_pos]
    split_ifs <;> simp
  have hr0 : r 0 = -(m * (Real.log u : ℂ) + h 0) := by simp [r]
  have hrZ : ∑ p ∈ hZfin.toFinset, r p =
      -∑ p ∈ hZfin.toFinset, ((analyticOrderNatAt (LFunction χ) p : ℕ) : ℂ) * ((u : ℂ) ^ p / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := fun h' => h0Z (h' ▸ hp)
    have hp1 : p ≠ 1 := fun h' => h1Z (h' ▸ hp)
    simp [r, hp1, hp0]
  rw [Finset.sum_insert h1S, Finset.sum_insert h0Z, hr1, hr0, hrZ,
    finsum_mem_eq_finite_toFinset_sum _ hZfin]
  ring

end GlobalTheory.ExplicitRect
