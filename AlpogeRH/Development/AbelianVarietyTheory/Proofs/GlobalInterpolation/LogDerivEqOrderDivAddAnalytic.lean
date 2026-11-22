-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem logDeriv_eq_order_div_add_analytic :
    ∀ (f : ℂ → ℂ) (p : ℂ), AnalyticAt ℂ f p → (¬ ∀ᶠ s in 𝓝 p, f s = 0) →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, f s ≠ 0 ∧
        deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  intro f p hf hne
  have htop : analyticOrderAt f p ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact hne
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderNatAt_eq_iff htop (n := analyticOrderNatAt f p)).mp rfl
  set m := analyticOrderNatAt f p with hm
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have h1 : ∀ᶠ s in 𝓝 p, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have h2 : ∀ᶠ s in 𝓝 p, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have h3 := hfg.eventually_nhds
  have h4 : ∀ᶠ s in 𝓝[≠] p, s ≠ p := self_mem_nhdsWithin
  filter_upwards [h4, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3]
    with s hsp hs1 hs2 hs3
  have hsub : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hev : f =ᶠ[𝓝 s] fun z => (z - p) ^ m * g z := by
    filter_upwards [hs3] with z hz
    rw [hz, smul_eq_mul]
  have hfs : f s = (s - p) ^ m * g s := hev.eq_of_nhds
  have hd : HasDerivAt (fun z => (z - p) ^ m * g z)
      ((m : ℂ) * (s - p) ^ (m - 1) * 1 * g s + (s - p) ^ m * deriv g s) s :=
    (((hasDerivAt_id s).sub_const p).pow m).mul hs2.differentiableAt.hasDerivAt
  have hdf : deriv f s = (m : ℂ) * (s - p) ^ (m - 1) * 1 * g s + (s - p) ^ m * deriv g s := by
    rw [hev.deriv_eq, hd.deriv]
  refine ⟨by rw [hfs]; exact mul_ne_zero (pow_ne_zero _ hsub) hs1, ?_⟩
  rw [hdf, hfs]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    field_simp
    ring

end GlobalTheory
