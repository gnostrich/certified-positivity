module

public import Mathlib
public import RequestProject.Horizon
public import RequestProject.V5_1

@[expose] public section

/-!
# ScrewRH.PSD: positive semidefiniteness from a cosine series (blueprint lemma 11)

If `Ψ t = ∑ w i (1 - cos (γ i t))` with nonnegative weights, then the Krein kernel
`Ψ (t i) + Ψ (t j) - Ψ (t i - t j)` is positive semidefinite on every finite grid. The
pointwise identity is
`1 - cos a - cos b + cos (a - b) = (1 - cos a) (1 - cos b) + sin a sin b`.
-/

open scoped BigOperators

namespace ScrewRH

/-- Pointwise identity behind the positivity. -/
lemma cos_kernel_identity (a b : ℝ) :
    (1 - Real.cos a) + (1 - Real.cos b) - (1 - Real.cos (a - b)) =
      (1 - Real.cos a) * (1 - Real.cos b) + Real.sin a * Real.sin b := by
  rw [Real.cos_sub]; ring

/-- Summability of `w i * (1 - cos (γ i t))` follows from summability of `w`. -/
lemma summable_mul_one_sub_cos {ι : Type*} (w : ι → ℝ) (γ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (t : ℝ) :
    Summable (fun i => w i * (1 - Real.cos (γ i * t))) := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) ?_) (fun i => ?_) (hs.mul_left 2)
  · linarith [Real.cos_le_one (γ i * t)]
  · have h1 : 1 - Real.cos (γ i * t) ≤ 2 := by linarith [Real.neg_one_le_cos (γ i * t)]
    nlinarith [hw i]

/-- **Blueprint lemma 11 (abstract form).** A nonnegative cosine series gives a positive
semidefinite Krein kernel on every finite grid. -/
theorem quadForm_nonneg_of_cos_series {ι : Type*} (w : ι → ℝ) (γ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (Ψ : ℝ → ℝ)
    (hΨ : ∀ t, HasSum (fun i => w i * (1 - Real.cos (γ i * t))) (Ψ t)) :
    ∀ (N : ℕ) (t x : Fin N → ℝ),
      0 ≤ ∑ i, ∑ j, x i * (Ψ (t i) + Ψ (t j) - Ψ (t i - t j)) * x j := by
  -- `hs` is not needed: the hypotheses `hΨ` already provide the sums.
  have _ : Summable w := hs
  intro N t x
  have key : ∀ i j, HasSum (fun k => x i * (w k * ((1 - Real.cos (γ k * t i)) *
      (1 - Real.cos (γ k * t j)) + Real.sin (γ k * t i) * Real.sin (γ k * t j))) * x j)
      (x i * (Ψ (t i) + Ψ (t j) - Ψ (t i - t j)) * x j) := by
    intro i j
    have h := (((hΨ (t i)).add (hΨ (t j))).sub (hΨ (t i - t j))).mul_left (x i)
    have h2 := h.mul_right (x j)
    convert h2 using 2 with k
    rw [mul_sub (γ k), ← cos_kernel_identity]
    ring
  have htot := hasSum_sum (fun i (_ : i ∈ Finset.univ) =>
    hasSum_sum (fun j (_ : j ∈ Finset.univ) => key i j))
  refine htot.nonneg (fun k => ?_)
  have hid : (∑ i, ∑ j, x i * (w k * ((1 - Real.cos (γ k * t i)) *
      (1 - Real.cos (γ k * t j)) + Real.sin (γ k * t i) * Real.sin (γ k * t j))) * x j) =
      w k * ((∑ i, x i * (1 - Real.cos (γ k * t i))) ^ 2 +
        (∑ i, x i * Real.sin (γ k * t i)) ^ 2) := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [hid]
  exact mul_nonneg (hw k) (by positivity)

/-- The same statement in the vocabulary of `Horizon.IsPSDq`. -/
theorem isPSDq_of_cos_series {ι : Type*} (w : ι → ℝ) (γ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (Ψ : ℝ → ℝ)
    (hΨ : ∀ t, HasSum (fun i => w i * (1 - Real.cos (γ i * t))) (Ψ t))
    {N : ℕ} (t : Fin N → ℝ) :
    Horizon.IsPSDq (Matrix.of fun i j : Fin N => Ψ (t i) + Ψ (t j) - Ψ (t i - t j)) := by
  intro x
  simpa [Horizon.quadForm] using quadForm_nonneg_of_cos_series w γ hw hs Ψ hΨ N t x

/-- Specialisation to Suzuki's screw function: if `V5_1.Psi` is a nonnegative cosine series,
then Krein's Gram kernel `V5_1.G` is positive semidefinite on every finite grid. -/
theorem isPSDq_G_of_cos_series {ι : Type*} (w : ι → ℝ) (γ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w)
    (hΨ : ∀ t, HasSum (fun i => w i * (1 - Real.cos (γ i * t))) (V5_1.Psi t))
    {N : ℕ} (t : Fin N → ℝ) :
    Horizon.IsPSDq (Matrix.of fun i j : Fin N => V5_1.G (t i) (t j)) :=
  isPSDq_of_cos_series w γ hw hs V5_1.Psi hΨ t

end ScrewRH
