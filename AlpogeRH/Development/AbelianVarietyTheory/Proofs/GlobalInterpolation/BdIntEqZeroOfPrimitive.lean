-- Ported from Levent Alpöge's Lean development of the Riemann Hypothesis (alpo.ge, 2026-11-20; mirror CocoSgt/riemann-hypothesis-lean @7cbf7a0), used with the author's permission. Modified for Lean v4.35.0 and the Lean module system.

module

public import Mathlib

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ResRect

noncomputable def bdInt (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I))
    + I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

def SidesIn (a b c d : ℝ) (B : Set ℂ) : Prop :=
  (∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) ∧ (∀ x ∈ Set.uIcc a b, (x : ℂ) + d * I ∈ B) ∧
  (∀ y ∈ Set.uIcc c d, (b : ℂ) + y * I ∈ B) ∧ (∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B)

theorem int_hor {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b :=
  (hf.comp (by fun_prop) h).intervalIntegrable

theorem int_ver {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d :=
  (hf.comp (by fun_prop) h).intervalIntegrable

theorem bdInt_add {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hf : ContinuousOn f B) (hg : ContinuousOn g B) :
    bdInt a b c d (fun s => f s + g s) = bdInt a b c d f + bdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [intervalIntegral.integral_add (int_hor hf h1) (int_hor hg h1),
    intervalIntegral.integral_add (int_hor hf h2) (int_hor hg h2),
    intervalIntegral.integral_add (int_ver hf h3) (int_ver hg h3),
    intervalIntegral.integral_add (int_ver hf h4) (int_ver hg h4)]
  ring

theorem bdInt_sum {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {ι : Type*} (S : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, ContinuousOn (f i) B) :
    bdInt a b c d (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, bdInt a b c d (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bdInt]
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [bdInt_add h (hf i (Finset.mem_insert_self _ _))
      (continuousOn_finset_sum _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem bdInt_congr {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hfg : ∀ s ∈ B, f s = g s) : bdInt a b c d f = bdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => g (x + c * I)) fun x hx => hfg _ (h1 x hx),
    intervalIntegral.integral_congr (f := fun x : ℝ => f (x + d * I))
      (g := fun x : ℝ => g (x + d * I)) fun x hx => hfg _ (h2 x hx),
    intervalIntegral.integral_congr (f := fun y : ℝ => f (b + y * I))
      (g := fun y : ℝ => g (b + y * I)) fun x hx => hfg _ (h3 x hx),
    intervalIntegral.integral_congr (f := fun y : ℝ => f (a + y * I))
      (g := fun y : ℝ => g (a + y * I)) fun x hx => hfg _ (h4 x hx)]

theorem ftc_hor {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    ∫ x : ℝ in a..b, f (x + c * I) = F (b + c * I) - F (a + c * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + c * I))
    (fun x hx => ?_) (int_hor hf h)
  have h1 : HasDerivAt (fun t : ℂ => F (t + c * I)) (f (x + c * I)) (x : ℂ) :=
    HasDerivAt.comp_add_const (x : ℂ) (c * I) (hF _ (h x hx))
  exact h1.comp_ofReal

theorem ftc_ver {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    I * ∫ y : ℝ in c..d, f (a + y * I) = F (a + d * I) - F (a + c * I) := by
  rw [mul_comm, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F (a + y * I))
    (fun y hy => ?_) ((int_ver hf h).mul_const I)
  have h0 : HasDerivAt (fun t : ℂ => (a : ℂ) + t * I) I (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ)
  have h1 : HasDerivAt (fun t : ℂ => F (a + t * I)) (f (a + y * I) * I) (y : ℂ) :=
    HasDerivAt.comp (y : ℂ) (hF _ (h y hy)) h0
  exact h1.comp_ofReal

theorem bdInt_eq_zero_of_primitive {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B)
    {F f : ℂ → ℂ} (hf : ContinuousOn f B) (hF : ∀ s ∈ B, HasDerivAt F (f s) s) :
    bdInt a b c d f = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [ftc_hor hf hF h1, ftc_hor hf hF h2, ftc_ver hf hF h3, ftc_ver hf hF h4]
  ring

theorem sidesIn_compl {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) : SidesIn a b c d {p}ᶜ := by
  refine ⟨fun x _ hx => ?_, fun x _ hx => ?_, fun x _ hx => ?_, fun x _ hx => ?_⟩
  · have := congrArg Complex.im (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.im (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.re (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.re (Set.mem_singleton_iff.1 hx); simp at this; linarith

theorem bdInt_sq {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) (k : ℂ) : bdInt a b c d (fun s => k / (s - p) ^ 2) = 0 := by
  refine bdInt_eq_zero_of_primitive (sidesIn_compl h1 h2 h3 h4) (F := fun s => -k * (s - p)⁻¹)
    ?_ fun s hs => ?_
  · exact ContinuousOn.div (by fun_prop) (by fun_prop)
      fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs)
  · have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    have := (((hasDerivAt_id s).sub_const p).inv hs').const_mul (-k)
    refine this.congr_deriv ?_
    simp only [id]
    ring

theorem bdInt_inv {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) (k : ℂ) : bdInt a b c d (fun s => k / (s - p)) = 2 * Real.pi * I * k := by
  have hc : ∀ B : Set ℂ, (∀ s ∈ B, s - p ≠ 0) → ContinuousOn (fun s => k / (s - p)) B :=
    fun B hB => ContinuousOn.div (by fun_prop) (by fun_prop) hB
  have hc1 := hc {s | s - p ∈ slitPlane} fun s hs => slitPlane_ne_zero hs
  have hc2 := hc {s | -(s - p) ∈ slitPlane} fun s hs => neg_ne_zero.1 (slitPlane_ne_zero hs)
  have hd1 : ∀ s ∈ {s | s - p ∈ slitPlane},
      HasDerivAt (fun s => k * log (s - p)) (k / (s - p)) s := fun s hs => by
    have := (((hasDerivAt_id s).sub_const p).clog hs).const_mul k
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have hd2 : ∀ s ∈ {s | -(s - p) ∈ slitPlane},
      HasDerivAt (fun s => k * log (-(s - p))) (k / (s - p)) s := fun s hs => by
    have := (((hasDerivAt_id s).sub_const p).neg.clog hs).const_mul k
    refine this.congr_deriv ?_
    simp only [id, Pi.neg_apply, neg_div_neg_eq]
    ring
  simp only [bdInt]
  rw [ftc_hor hc1 hd1 (c := c) fun x _ => Or.inr (by simp; linarith),
    ftc_hor hc1 hd1 (c := d) fun x _ => Or.inr (by simp; linarith),
    ftc_ver hc1 hd1 (a := b) fun x _ => Or.inl (by simp; linarith),
    ftc_ver hc2 hd2 (a := a) fun x _ => Or.inl (by simp; linarith)]
  have e1 : log (-((a : ℂ) + d * I - p)) = log ((a : ℂ) + d * I - p) - Real.pi * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos (by simp; linarith)]
    push_cast; ring
  have e2 : log (-((a : ℂ) + c * I - p)) = log ((a : ℂ) + c * I - p) + Real.pi * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg (by simp; linarith)]
    push_cast; ring
  rw [e1, e2]
  ring

theorem residue_rectangle :
    ∀ (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ) (r : ℂ → ℂ), z.re < w.re → z.im < w.im → (∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) → DifferentiableOn ℂ f ((Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im) \ S) → (∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧ ∀ᶠ s in nhdsWithin p {p}ᶜ, f s = a / (s - p) ^ 2 + r p / (s - p) + g s) → (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 2 * Real.pi * I * ∑ p ∈ S, r p := by
  classical
  intro f z w S r hre him hS hf hp
  choose! a g hg hfg using hp
  set R : Set ℂ := Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im with hR
  let P : ℂ → ℂ → ℂ := fun p s => a p / (s - p) ^ 2 + r p / (s - p)
  have hP : ∀ p s, s ≠ p → DifferentiableAt ℂ (P p) s := fun p s hs => by
    have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    have hs2 : (s - p) ^ 2 ≠ 0 := pow_ne_zero _ hs'
    simp only [P]
    fun_prop (disch := assumption)
  let h : ℂ → ℂ := fun s =>
    if s ∈ S then g s s - ∑ q ∈ S.erase s, P q s else f s - ∑ q ∈ S, P q s
  have hopen : ∀ T : Finset ℂ, ∀ s ∉ T, ∀ᶠ t in nhds s, t ∉ T := fun T s hs =>
    T.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
  have hh : DifferentiableOn ℂ h R := by
    intro s hs
    by_cases hsS : s ∈ S
    · have hd : DifferentiableAt ℂ (fun t => g s t - ∑ q ∈ S.erase s, P q t) s :=
        (hg s hsS).differentiableAt.sub
          (DifferentiableAt.fun_sum fun q hq => hP q s (Finset.ne_of_mem_erase hq).symm)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      have e1 := eventually_nhdsWithin_iff.1 (hfg s hsS)
      filter_upwards [e1, hopen (S.erase s) s (Finset.notMem_erase s S)] with t ht1 ht2
      by_cases hts : t = s
      · subst hts
        simp only [h, if_pos hsS]
      · have htS : t ∉ S := fun ht => ht2 (Finset.mem_erase.2 ⟨hts, ht⟩)
        simp only [h, if_neg htS]
        rw [ht1 hts, ← Finset.add_sum_erase S _ hsS]
        simp only [P]
        ring
    · have hd : DifferentiableWithinAt ℂ (fun t => f t - ∑ q ∈ S, P q t) R s := by
        refine DifferentiableWithinAt.sub ?_
          (DifferentiableAt.fun_sum fun q hq => hP q s fun e => hsS (e ▸ hq)).differentiableWithinAt
        refine (hf s ⟨hs, hsS⟩).mono_of_mem_nhdsWithin ?_
        exact inter_mem_nhdsWithin R (hopen S s hsS)
      refine hd.congr_of_eventuallyEq ?_ (by simp only [h, if_neg hsS])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen S s hsS)] with t ht
      have ht' : t ∉ S := ht
      simp only [h, if_neg ht']
  have hB : SidesIn z.re w.re z.im w.im (R \ S) := by
    rw [SidesIn, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
    refine ⟨fun x hx => ⟨?_, fun hm => ?_⟩, fun x hx => ⟨?_, fun hm => ?_⟩,
      fun x hx => ⟨?_, fun hm => ?_⟩, fun x hx => ⟨?_, fun hm => ?_⟩⟩
    · simp [hR, mem_reProdIm, hx.1, hx.2, him.le]
    · simpa using (hS _ hm).2.2.1
    · simp [hR, mem_reProdIm, hx.1, hx.2, him.le]
    · simpa using (hS _ hm).2.2.2
    · simp [hR, mem_reProdIm, hx.1, hx.2, hre.le]
    · simpa using (hS _ hm).2.1
    · simp [hR, mem_reProdIm, hx.1, hx.2, hre.le]
    · simpa using (hS _ hm).1
  have hPc : ∀ p ∈ S, ContinuousOn (P p) (R \ S) := fun p hp s hs =>
    (hP p s fun e => hs.2 (e ▸ hp)).continuousAt.continuousWithinAt
  have h0 : bdInt z.re w.re z.im w.im h = 0 := by
    have := integral_boundary_rect_eq_zero_of_differentiableOn h z w
      (by rwa [Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le])
    simpa only [smul_eq_mul, bdInt] using this
  change bdInt z.re w.re z.im w.im f = _
  rw [bdInt_congr hB (g := fun s => h s + ∑ q ∈ S, P q s) (fun s hs => by
      have ht' : s ∉ S := hs.2
      simp only [h, if_neg ht']; ring),
    bdInt_add hB (hh.continuousOn.mono Set.diff_subset) (continuousOn_finset_sum _ hPc), h0,
    zero_add, bdInt_sum hB S hPc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hS p hp
  simp only [P]
  rw [bdInt_add (sidesIn_compl h1 h2 h3 h4) (f := fun s => a p / (s - p) ^ 2)
    (g := fun s => r p / (s - p))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => sub_ne_zero.2 hs),
    bdInt_sq h1 h2 h3 h4, bdInt_inv h1 h2 h3 h4, zero_add]

end GlobalTheory.ResRect
