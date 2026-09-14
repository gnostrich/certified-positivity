import Mathlib

open scoped BigOperators Matrix ComplexOrder
open Complex

/-!
# D4Aux. Supporting material for the Carathéodory–Fejér theorem (D4)

This file collects the general-purpose ingredients used by `D4.D4_caratheodory`:

* `rank_principal_submatrix_le`: a principal submatrix has rank at most the rank of the matrix;
* `rank_le_card_of_atoms`: if `c` is a sum of `|S|` unimodular atoms on `|m| ≤ N`, then the
  associated Toeplitz matrix has rank at most `|S|` (Vandermonde factorization);
* `window_null`: a null vector of a leading Toeplitz block, placed in any window of a larger
  positive semidefinite Toeplitz matrix, is again a null vector — this propagates the linear
  recurrence to all available indices;
* `rec_up` / `rec_down`: two sequences satisfying the same linear recurrence and agreeing on a
  window of length `q` agree on the whole range;
* `vandermonde_solve`: interpolation at `q` distinct nodes.
-/

namespace D4Aux

/-- The Hermitian Toeplitz matrix `T j k = c (j - k)` of size `N + 1`. -/
def T {N : ℕ} (c : ℤ → ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- A principal submatrix has rank at most the rank of the ambient matrix. -/
lemma rank_principal_submatrix_le {N k : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (f : Fin k → Fin N) :
    (M.submatrix f f).rank ≤ M.rank := by
  have h1 : M.submatrix f f = (M.submatrix id f).submatrix f (Equiv.refl (Fin k)) := rfl
  have h2 : (M.submatrix id f).rank ≤ M.rank := by
    have ht : (M.submatrix id f)ᵀ = Mᵀ.submatrix f (Equiv.refl (Fin N)) := rfl
    calc (M.submatrix id f).rank = ((M.submatrix id f)ᵀ).rank := (Matrix.rank_transpose _).symm
      _ = (Mᵀ.submatrix f (Equiv.refl (Fin N))).rank := by rw [ht]
      _ ≤ Mᵀ.rank := Matrix.rank_submatrix_le _ _ _
      _ = M.rank := Matrix.rank_transpose _
  calc (M.submatrix f f).rank
      = ((M.submatrix id f).submatrix f (Equiv.refl (Fin k))).rank := by rw [← h1]
    _ ≤ (M.submatrix id f).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ M.rank := h2

/-- If `c` is, on the window `|m| ≤ N`, a combination of `|S|` unimodular exponentials, then the
Toeplitz matrix of `c` has rank at most `|S|`. -/
lemma rank_le_card_of_atoms {N q : ℕ} (c : ℤ → ℂ) (θ : Fin q → ℝ) (a : Fin q → ℂ)
    (S : Finset (Fin q))
    (hrep : ∀ m : ℤ, |m| ≤ (N : ℤ) →
      c m = ∑ s ∈ S, a s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I)) :
    (T (N := N) c).rank ≤ S.card := by
  classical
  set A : Matrix (Fin (N + 1)) S ℂ :=
    Matrix.of fun j (s : S) => a (s : Fin q) * Complex.exp ((j : ℂ) * ((θ s : ℝ) : ℂ) * Complex.I)
    with hA
  set B : Matrix S (Fin (N + 1)) ℂ :=
    Matrix.of fun (s : S) k => Complex.exp (-(k : ℂ) * ((θ s : ℝ) : ℂ) * Complex.I) with hB
  have hT : T (N := N) c = A * B := by
    ext j k
    have hjk : |((j : ℤ) - (k : ℤ))| ≤ (N : ℤ) := by
      have hj := j.isLt
      have hk := k.isLt
      rw [abs_le]
      omega
    show c ((j : ℤ) - (k : ℤ)) = _
    rw [hrep _ hjk, Matrix.mul_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hA, hB, Matrix.of_apply]
    have hexp : Complex.exp ((j : ℂ) * ((θ (s : Fin q) : ℝ) : ℂ) * Complex.I)
        * Complex.exp (-(k : ℂ) * ((θ (s : Fin q) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * ((θ (s : Fin q) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hexp]
    ring
  rw [hT]
  calc (A * B).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card S := Matrix.rank_le_card_width _
    _ = S.card := Fintype.card_coe S

/-- Propagation of the null relation: if `u` annihilates the leading `(q+1) × (q+1)` block of a
positive semidefinite Toeplitz matrix of size `N + 1`, then the same relation holds in every
window. -/
lemma window_null {N q : ℕ} (c : ℤ → ℂ) (hPSD : (T (N := N) c).PosSemidef) (u : Fin (q + 1) → ℂ)
    (hnull : ∀ i : Fin (q + 1), ∑ k : Fin (q + 1), c ((i : ℤ) - (k : ℤ)) * u k = 0)
    (j : ℕ) (hj : j + q ≤ N) (i : Fin (N + 1)) :
    ∑ k : Fin (q + 1), c ((i : ℤ) - (j : ℤ) - (k : ℤ)) * u k = 0 := by
  classical
  set ι : Fin (q + 1) → Fin (N + 1) := fun k => ⟨j + (k : ℕ), by have := k.isLt; omega⟩ with hι
  set y : Fin (N + 1) → ℂ := fun t => ∑ k : Fin (q + 1), if ι k = t then u k else 0 with hy
  have hspread : ∀ g : Fin (N + 1) → ℂ,
      ∑ t : Fin (N + 1), g t * y t = ∑ k : Fin (q + 1), g (ι k) * u k := by
    intro g
    simp only [hy, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_ite]
  have hspread' : ∀ g : Fin (N + 1) → ℂ,
      ∑ t : Fin (N + 1), starRingEnd ℂ (y t) * g t
        = ∑ k : Fin (q + 1), starRingEnd ℂ (u k) * g (ι k) := by
    intro g
    have hc : ∀ t, starRingEnd ℂ (y t) = ∑ k : Fin (q + 1), if ι k = t then starRingEnd ℂ (u k)
        else 0 := by
      intro t
      simp [hy, map_sum, apply_ite]
    simp only [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ite_mul]
  have hivals : ∀ k : Fin (q + 1), ((ι k : Fin (N + 1)) : ℤ) = (j : ℤ) + (k : ℤ) := by
    intro k; simp [hι]
  have key : ∀ t : Fin (N + 1), ((T (N := N) c).mulVec y) t
      = ∑ k : Fin (q + 1), c ((t : ℤ) - (j : ℤ) - (k : ℤ)) * u k := by
    intro t
    show ∑ s : Fin (N + 1), T (N := N) c t s * y s = _
    rw [hspread (fun s => T (N := N) c t s)]
    refine Finset.sum_congr rfl fun k _ => ?_
    show c ((t : ℤ) - ((ι k : Fin (N + 1)) : ℤ)) * u k = _
    rw [hivals k]
    ring_nf
  have hform : star y ⬝ᵥ (T (N := N) c).mulVec y = 0 := by
    show ∑ t : Fin (N + 1), star (y t) * ((T (N := N) c).mulVec y) t = 0
    have hst : ∀ t : Fin (N + 1), star (y t) * ((T (N := N) c).mulVec y) t
        = starRingEnd ℂ (y t) * (∑ k : Fin (q + 1), c ((t : ℤ) - (j : ℤ) - (k : ℤ)) * u k) := by
      intro t; rw [key t]; rfl
    simp only [hst]
    rw [hspread' (fun t => ∑ k : Fin (q + 1), c ((t : ℤ) - (j : ℤ) - (k : ℤ)) * u k)]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hzero : (∑ k : Fin (q + 1), c (((ι l : Fin (N + 1)) : ℤ) - (j : ℤ) - (k : ℤ)) * u k) = 0 := by
      rw [hivals l]
      have := hnull l
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [hzero, mul_zero]
  have hker := (hPSD.dotProduct_mulVec_zero_iff y).mp hform
  have := congr_fun hker i
  rw [key i] at this
  exact this

/-- Upward propagation of a linear recurrence whose lowest coefficient `u 0` is nonzero. -/
lemma rec_up (q : ℕ) (u : Fin (q + 1) → ℂ) (hu0 : u 0 ≠ 0) (f g : ℤ → ℂ) (lo hi : ℤ)
    (hf : ∀ m : ℤ, lo ≤ m → m ≤ hi → ∑ k : Fin (q + 1), f (m - (k : ℕ)) * u k = 0)
    (hg : ∀ m : ℤ, lo ≤ m → m ≤ hi → ∑ k : Fin (q + 1), g (m - (k : ℕ)) * u k = 0)
    (hbase : ∀ m : ℤ, lo - q ≤ m → m < lo → f m = g m) :
    ∀ m : ℤ, lo - q ≤ m → m ≤ hi → f m = g m := by
  have key : ∀ t : ℕ, ∀ m : ℤ, m = lo - q + t → m ≤ hi → f m = g m := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro m hm hmhi
      rcases lt_or_ge m lo with hlt | hge
      · exact hbase m (by omega) hlt
      · have hsub : ∑ k : Fin (q + 1), (f (m - (k : ℕ)) - g (m - (k : ℕ))) * u k = 0 := by
          have h1 := hf m hge hmhi
          have h2 := hg m hge hmhi
          simp only [sub_mul]
          rw [Finset.sum_sub_distrib, h1, h2, sub_zero]
        have htail : ∀ k : Fin q,
            (f (m - ((k.succ : Fin (q + 1)) : ℕ)) - g (m - ((k.succ : Fin (q + 1)) : ℕ)))
              * u k.succ = 0 := by
          intro k
          have hk : ((k.succ : Fin (q + 1)) : ℕ) = (k : ℕ) + 1 := rfl
          have hlt2 : t - ((k : ℕ) + 1) < t := by
            have : (q : ℤ) ≤ t := by omega
            have := k.isLt
            omega
          have heq : m - (((k : ℕ) + 1 : ℕ) : ℤ) = lo - q + (t - ((k : ℕ) + 1) : ℕ) := by
            have : (q : ℤ) ≤ t := by omega
            have hkk := k.isLt
            have : ((t - ((k : ℕ) + 1) : ℕ) : ℤ) = (t : ℤ) - ((k : ℕ) + 1) := by
              omega
            omega
          have := ih (t - ((k : ℕ) + 1)) hlt2 (m - (((k : ℕ) + 1 : ℕ) : ℤ)) heq (by omega)
          rw [hk]
          rw [this]
          ring
        rw [Fin.sum_univ_succ] at hsub
        have : ∑ k : Fin q,
            (f (m - ((k.succ : Fin (q + 1)) : ℕ)) - g (m - ((k.succ : Fin (q + 1)) : ℕ)))
              * u k.succ = 0 := Finset.sum_eq_zero fun k _ => htail k
        rw [this, add_zero] at hsub
        have h0 : ((0 : Fin (q + 1)) : ℕ) = 0 := rfl
        rw [h0] at hsub
        simp only [Nat.cast_zero, sub_zero] at hsub
        rcases mul_eq_zero.mp hsub with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hu0
  intro m hm hmhi
  exact key (m - (lo - q)).toNat m (by omega) hmhi

/-- Downward propagation of a linear recurrence whose top coefficient `u q` is nonzero. -/
lemma rec_down (q : ℕ) (u : Fin (q + 1) → ℂ) (huq : u (Fin.last q) ≠ 0) (f g : ℤ → ℂ) (lo hi : ℤ)
    (hf : ∀ m : ℤ, lo ≤ m → m ≤ hi → ∑ k : Fin (q + 1), f (m - (k : ℕ)) * u k = 0)
    (hg : ∀ m : ℤ, lo ≤ m → m ≤ hi → ∑ k : Fin (q + 1), g (m - (k : ℕ)) * u k = 0)
    (hbase : ∀ m : ℤ, hi - q < m → m ≤ hi → f m = g m) :
    ∀ m : ℤ, lo - q ≤ m → m ≤ hi → f m = g m := by
  have key : ∀ t : ℕ, ∀ m : ℤ, m = hi - t → lo - q ≤ m → f m = g m := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro m hm hmlo
      rcases lt_or_ge (hi - q) m with hgt | hle
      · exact hbase m hgt (by omega)
      · -- use the recurrence at `m + q`
        have hsub : ∑ k : Fin (q + 1),
            (f (m + q - (k : ℕ)) - g (m + q - (k : ℕ))) * u k = 0 := by
          have h1 := hf (m + q) (by omega) (by omega)
          have h2 := hg (m + q) (by omega) (by omega)
          simp only [sub_mul]
          rw [Finset.sum_sub_distrib, h1, h2, sub_zero]
        have hhead : ∀ k : Fin q,
            (f (m + q - ((k.castSucc : Fin (q + 1)) : ℕ)) - g (m + q - ((k.castSucc : Fin (q + 1)) : ℕ)))
              * u k.castSucc = 0 := by
          intro k
          have hk : ((k.castSucc : Fin (q + 1)) : ℕ) = (k : ℕ) := rfl
          have hkk := k.isLt
          have hlt2 : (hi - (m + q - (k : ℕ))).toNat < t := by omega
          have heq : m + q - ((k : ℕ) : ℤ) = hi - ((hi - (m + q - (k : ℕ))).toNat : ℤ) := by
            omega
          have := ih ((hi - (m + q - (k : ℕ))).toNat) hlt2 (m + q - ((k : ℕ) : ℤ)) heq (by omega)
          rw [hk, this]
          ring
        rw [Fin.sum_univ_castSucc] at hsub
        have hz : ∑ k : Fin q,
            (f (m + q - ((k.castSucc : Fin (q + 1)) : ℕ)) - g (m + q - ((k.castSucc : Fin (q + 1)) : ℕ)))
              * u k.castSucc = 0 := Finset.sum_eq_zero fun k _ => hhead k
        rw [hz, zero_add] at hsub
        have hlast : ((Fin.last q : Fin (q + 1)) : ℕ) = q := rfl
        rw [hlast] at hsub
        have hmm : m + (q : ℤ) - (q : ℤ) = m := by ring
        rw [hmm] at hsub
        rcases mul_eq_zero.mp hsub with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h huq
  intro m hm hmhi
  exact key (hi - m).toNat m (by omega) hm

/-- Interpolation at `q` distinct nodes. -/
lemma vandermonde_solve {q : ℕ} (w : Fin q → ℂ) (hw : Function.Injective w) (b : Fin q → ℂ) :
    ∃ a : Fin q → ℂ, ∀ m : Fin q, ∑ s, a s * (w s) ^ (m : ℕ) = b m := by
  classical
  set V : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun m s => (w s) ^ (m : ℕ) with hV
  have hVt : V = (Matrix.vandermonde w)ᵀ := by
    ext m s; simp [hV, Matrix.vandermonde]
  have hdet : IsUnit V.det := by
    rw [hVt, Matrix.det_transpose, Matrix.det_vandermonde]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne fun h => ?_
    exact absurd (hw h) (Finset.mem_Ioi.mp hj).ne'
  refine ⟨V⁻¹ *ᵥ b, fun m => ?_⟩
  have hmul : V *ᵥ (V⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hcomp := congr_fun hmul m
  rw [← hcomp]
  simp only [Matrix.mulVec, dotProduct, hV, Matrix.of_apply]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end D4Aux
