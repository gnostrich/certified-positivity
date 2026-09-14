import Mathlib
import RequestProject.D4Aux
import RequestProject.F2
import RequestProject.F3R

open scoped BigOperators Matrix ComplexOrder
open Complex

namespace D4

/-!
# D4. Carathéodory–Toeplitz: positive Toeplitz = atomic (the trigonometric Kronecker)

Let `c : ℤ → ℂ` satisfy `c (-m) = conj (c m)`, and let `T` be the `(n+1) × (n+1)` Hermitian
Toeplitz matrix `T j k = c (j - k)`.  If `T` is positive semidefinite with rank `r ≤ n`, then
there are `r` real frequencies `θ_s` and `r` strictly positive weights `ρ_s` with
`c m = ∑ s, ρ_s · exp(i · m · θ_s)` for all `|m| ≤ n`.

This is the Carathéodory–Fejér theorem, and it is proved here in full.  The proof runs as follows.

* Let `q` be least with the property that the leading `(q+1) × (q+1)` block of `T` fails to be
  positive definite (such a `q ≤ n` exists because `T` itself is singular).  Then the leading
  `q × q` block is positive definite and the `(q+1) × (q+1)` block is singular.
* `F3R.F3R_roots` (the hard rung) applies to that block: a nonzero null vector `u` of it has an
  annihilator polynomial `P(z) = ∑ u_k z^k` whose `q` roots are unimodular and pairwise distinct.
* `D4Aux.window_null` propagates the null relation `∑ u_k c(m-k) = 0` from the block to every
  window of `T`, so it holds for all `-(n-q) ≤ m ≤ n`.
* The reciprocals `w_s` of the roots are unimodular and distinct, and the sequence
  `x m = ∑ a_s w_s^m` obeys the same recurrence for any coefficients `a`.  Choosing `a` by
  Vandermonde interpolation on `0 ≤ m < q` (`D4Aux.vandermonde_solve`) and propagating the
  recurrence up and down (`D4Aux.rec_up`, `D4Aux.rec_down`) gives `c m = x m` for `|m| ≤ n`.
* Counting rank both ways (`D4Aux.rank_le_card_of_atoms` and `D4Aux.rank_principal_submatrix_le`)
  shows `q = r`, and that no coefficient `a_s` vanishes.
* Finally `F2.F2_b` and `F2.F2_c` show that the coefficients are real and strictly positive.
-/

variable {n : ℕ}

/-- The Hermitian Toeplitz matrix `T j k = c (j - k)`. -/
def toeplitz (c : ℤ → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- The `k × k` Toeplitz block `[c (i - j)]`. -/
def block (c : ℤ → ℂ) (k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => c ((i : ℤ) - (j : ℤ))

/-- Carathéodory–Fejér representation. -/
theorem D4_caratheodory (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (n := n) c).PosSemidef)
    (r : ℕ) (hr : (toeplitz (n := n) c).rank = r) (hrn : r ≤ n) :
    ∃ (θ : Fin r → ℝ) (ρ : Fin r → ℝ), (∀ s, 0 < ρ s) ∧
      ∀ m : ℤ, |m| ≤ (n : ℤ) →
        c m = ∑ s, (ρ s : ℂ) * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I) := by
  classical
  have hTT : toeplitz (n := n) c = D4Aux.T (N := n) c := rfl
  have hPSDn : (D4Aux.T (N := n) c).PosSemidef := hPSD
  -- Every leading block is positive semidefinite.
  have hblockPSD : ∀ k, k ≤ n + 1 → (block c k).PosSemidef := by
    intro k hk
    have hsub : block c k
        = (toeplitz (n := n) c).submatrix
            (fun i : Fin k => (⟨i, lt_of_lt_of_le i.isLt hk⟩ : Fin (n + 1)))
            (fun i : Fin k => (⟨i, lt_of_lt_of_le i.isLt hk⟩ : Fin (n + 1))) := rfl
    rw [hsub]
    exact hPSD.submatrix _
  -- `T` itself is not positive definite, since its rank is at most `n`.
  have hnotPD : ¬ (block c (n + 1)).PosDef := by
    intro h
    have hbt : block c (n + 1) = toeplitz (n := n) c := rfl
    have hunit : IsUnit (toeplitz (n := n) c) := by
      rw [← hbt]
      exact h.isUnit
    have hrk : (toeplitz (n := n) c).rank = n + 1 := by
      simpa using Matrix.rank_of_isUnit _ hunit
    omega
  -- The least `q` whose `(q+1)`-block fails to be positive definite.
  have hex : ∃ k : ℕ, ¬ (block c (k + 1)).PosDef := ⟨n, hnotPD⟩
  set q := Nat.find hex with hqdef
  have hqn : q ≤ n := Nat.find_le hnotPD
  have hqnotPD : ¬ (block c (q + 1)).PosDef := Nat.find_spec hex
  have hleadPD : (block c q).PosDef := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · rw [h0]
      exact ⟨by ext i; exact i.elim0, fun x hx => absurd (Finsupp.ext fun i => i.elim0) hx⟩
    · have hmin := Nat.find_min hex (m := q - 1) (by omega)
      rw [not_not] at hmin
      rwa [Nat.sub_add_cancel hpos] at hmin
  have hsing : (block c (q + 1)).det = 0 := by
    by_contra hdet
    refine hqnotPD (((hblockPSD (q + 1) (by omega)).posDef_iff_isUnit).mpr ?_)
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨u, hu, hnull⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hsing
  -- Apply the F3R machinery to the `(q+1)`-block.
  have hPSDq : (F3R.toeplitz (r := q) c).PosSemidef := hblockPSD (q + 1) (by omega)
  have hleadq : (F3R.leadingBlock (r := q) c).PosDef := hleadPD
  have hsingq : (F3R.toeplitz (r := q) c).det = 0 := hsing
  have hnullq : (F3R.toeplitz (r := q) c).mulVec u = 0 := hnull
  obtain ⟨hroots_unim, hroots_nodup⟩ := F3R.F3R_roots c hHerm hPSDq hleadq hsingq u hu hnullq
  have hlast : u (Fin.last q) ≠ 0 := F3R.F3R_uLast_ne c hleadq u hu hnullq
  -- The annihilator polynomial has degree exactly `q` and `q` distinct unimodular roots.
  set Pu : Polynomial ℂ := F3R.annihilator u with hPu
  have hPu0 : Pu ≠ 0 := by
    intro h
    refine hu (funext fun i => ?_)
    have hc := F3R.annihilator_coeff u i
    rw [← hPu, h] at hc
    simpa using hc.symm
  have hcoeff_last : Pu.coeff q = u (Fin.last q) := F3R.annihilator_coeff u (Fin.last q)
  have hdeg : Pu.natDegree = q := by
    refine le_antisymm (F3R.annihilator_natDegree_le u) (Polynomial.le_natDegree_of_ne_zero ?_)
    rw [hcoeff_last]
    exact hlast
  have hcard : Multiset.card Pu.roots = q := by
    rw [← hdeg]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits Pu)
  have hFcard : Pu.roots.toFinset.card = q := by
    rw [Multiset.toFinset_card_of_nodup hroots_nodup, hcard]
  set zz : Fin q → ℂ := fun s =>
    ((Pu.roots.toFinset.equivFin.symm (Fin.cast hFcard.symm s) : Pu.roots.toFinset) : ℂ) with hzz
  have hzz_inj : Function.Injective zz := by
    intro s t hst
    have h1 : Pu.roots.toFinset.equivFin.symm (Fin.cast hFcard.symm s)
        = Pu.roots.toFinset.equivFin.symm (Fin.cast hFcard.symm t) := Subtype.ext hst
    have h2 := Pu.roots.toFinset.equivFin.symm.injective h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  have hzz_mem : ∀ s, zz s ∈ Pu.roots := fun s =>
    Multiset.mem_toFinset.mp (Pu.roots.toFinset.equivFin.symm (Fin.cast hFcard.symm s)).2
  have hzz_norm : ∀ s, ‖zz s‖ = 1 := fun s => hroots_unim _ (hzz_mem s)
  have hzz_ne : ∀ s, zz s ≠ 0 := by
    intro s h
    have := hzz_norm s
    rw [h] at this
    simp at this
  have hzz_root : ∀ s, ∑ k : Fin (q + 1), u k * (zz s) ^ (k : ℕ) = 0 := by
    intro s
    have h := Polynomial.isRoot_of_mem_roots (hzz_mem s)
    simpa [hPu, F3R.annihilator, Polynomial.eval_finset_sum] using h
  -- The nodes are the reciprocals of the roots.
  set w : Fin q → ℂ := fun s => (zz s)⁻¹ with hw
  have hw_ne : ∀ s, w s ≠ 0 := fun s => inv_ne_zero (hzz_ne s)
  have hw_inv : ∀ s, (w s)⁻¹ = zz s := fun s => inv_inv _
  have hw_inj : Function.Injective w := by
    intro s t h
    exact hzz_inj (by rw [← hw_inv s, ← hw_inv t, h])
  have hw_norm : ∀ s, ‖w s‖ = 1 := by
    intro s
    rw [hw]
    simp [hzz_norm s]
  obtain ⟨θ, hθ⟩ : ∃ θ : Fin q → ℝ, ∀ s, Complex.exp ((θ s : ℂ) * Complex.I) = w s := by
    have h : ∀ s, ∃ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) = w s := fun s =>
      (Complex.norm_eq_one_iff _).mp (hw_norm s)
    choose θ hθ using h
    exact ⟨θ, hθ⟩
  have hθ_inj : Function.Injective (fun s => Complex.exp ((θ s : ℂ) * Complex.I)) := by
    intro s t h
    refine hw_inj ?_
    rw [← hθ s, ← hθ t]
    exact h
  -- Vandermonde interpolation of the first `q` values.
  obtain ⟨a, ha⟩ := D4Aux.vandermonde_solve w hw_inj (fun m : Fin q => c ((m : ℕ) : ℤ))
  set x : ℤ → ℂ := fun m => ∑ s, a s * (w s) ^ m with hx
  -- The null relation, and its propagation to all windows.
  have hnull_rows : ∀ i : Fin (q + 1), ∑ k : Fin (q + 1), c ((i : ℤ) - (k : ℤ)) * u k = 0 := by
    intro i
    have h := congr_fun hnullq i
    simpa [Matrix.mulVec, dotProduct, F3R.toeplitz] using h
  have hrec_c : ∀ m : ℤ, -((n : ℤ) - (q : ℤ)) ≤ m → m ≤ (n : ℤ) →
      ∑ k : Fin (q + 1), c (m - ((k : ℕ) : ℤ)) * u k = 0 := by
    intro m hlo hhi
    rcases le_or_gt 0 m with hm | hm
    · have hi : (m.toNat : ℕ) < n + 1 := by omega
      have h := D4Aux.window_null (N := n) c hPSDn u hnull_rows 0 (by omega) ⟨m.toNat, hi⟩
      refine Eq.trans ?_ h
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      push_cast
      omega
    · have hj : (-m).toNat + q ≤ n := by omega
      have h := D4Aux.window_null (N := n) c hPSDn u hnull_rows ((-m).toNat) hj
        ⟨0, by omega⟩
      refine Eq.trans ?_ h
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      push_cast
      omega
  have hrec_x : ∀ m : ℤ, ∑ k : Fin (q + 1), x (m - ((k : ℕ) : ℤ)) * u k = 0 := by
    intro m
    have hstep : ∀ k : Fin (q + 1), x (m - ((k : ℕ) : ℤ)) * u k
        = ∑ s, (a s * (w s) ^ m * (zz s) ^ (k : ℕ)) * u k := by
      intro k
      rw [hx, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [zpow_sub₀ (hw_ne s), zpow_natCast, ← hw_inv s]
      field_simp
      ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hroot := hzz_root s
    calc ∑ k : Fin (q + 1), (a s * (w s) ^ m * (zz s) ^ (k : ℕ)) * u k
        = (a s * (w s) ^ m) * ∑ k : Fin (q + 1), u k * (zz s) ^ (k : ℕ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [hroot, mul_zero]
  -- Base window and propagation.
  have hbase : ∀ m : ℤ, 0 ≤ m → m < (q : ℤ) → c m = x m := by
    intro m h0 hq'
    have hlt : m.toNat < q := by omega
    have h : ∑ s, a s * (w s) ^ (m.toNat) = c ((m.toNat : ℕ) : ℤ) := ha ⟨m.toNat, hlt⟩
    have hmc : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h0
    rw [hmc] at h
    have hxm : x m = ∑ s, a s * (w s) ^ m := by rw [hx]
    rw [hxm, ← h]
    exact Finset.sum_congr rfl fun s _ => by rw [← zpow_natCast (w s) m.toNat, hmc]
  have hu0 : u 0 ≠ 0 := by
    intro h
    have hco : Pu.coeff 0 = 0 := by
      rw [hPu, show (0 : ℕ) = ((0 : Fin (q + 1)) : ℕ) from rfl, F3R.annihilator_coeff]
      exact h
    have hroot : Pu.IsRoot 0 := by
      rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero]
      exact hco
    have hmem : (0 : ℂ) ∈ Pu.roots := Polynomial.mem_roots'.mpr ⟨hPu0, hroot⟩
    have := hroots_unim 0 hmem
    simp at this
  have hup : ∀ m : ℤ, 0 ≤ m → m ≤ (n : ℤ) → c m = x m := by
    have h := D4Aux.rec_up q u hu0 c x (q : ℤ) (n : ℤ)
      (fun m h1 h2 => hrec_c m (by omega) h2)
      (fun m _ _ => hrec_x m)
      (fun m h1 h2 => hbase m (by omega) h2)
    intro m h1 h2
    exact h m (by omega) h2
  have hdown : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ (n : ℤ) → c m = x m := by
    have h := D4Aux.rec_down q u hlast c x (-((n : ℤ) - (q : ℤ))) (n : ℤ)
      (fun m h1 h2 => hrec_c m (by omega) h2)
      (fun m _ _ => hrec_x m)
      (fun m h1 h2 => hup m (by omega) h2)
    intro m h1 h2
    exact h m (by omega) h2
  have hrep : ∀ m : ℤ, |m| ≤ (n : ℤ) →
      c m = ∑ s, a s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I) := by
    intro m hm
    rw [abs_le] at hm
    rw [hdown m hm.1 hm.2, hx]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [← hθ s, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  -- Rank count: `q = r`.
  have hrank_le : (toeplitz (n := n) c).rank ≤ q := by
    have h := D4Aux.rank_le_card_of_atoms (N := n) c θ a Finset.univ
      (fun m hm => hrep m hm)
    rw [hTT]
    simpa using h
  have hq_le : q ≤ (toeplitz (n := n) c).rank := by
    have hunit : IsUnit (block c q) := hleadPD.isUnit
    have h1 : (block c q).rank = q := by
      simpa using Matrix.rank_of_isUnit _ hunit
    have h2 : block c q = (toeplitz (n := n) c).submatrix
        (fun i : Fin q => (⟨i, by omega⟩ : Fin (n + 1)))
        (fun i : Fin q => (⟨i, by omega⟩ : Fin (n + 1))) := rfl
    rw [← h1, h2]
    exact D4Aux.rank_principal_submatrix_le _ _
  have hqr : r = q := by omega
  -- No coefficient vanishes.
  have hmin : ∀ s : Fin q, a s ≠ 0 := by
    intro t ht
    have hrep' : ∀ m : ℤ, |m| ≤ (n : ℤ) →
        c m = ∑ s ∈ Finset.univ.erase t, a s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I) := by
      intro m hm
      rw [hrep m hm, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), ht, zero_mul, zero_add]
    have h := D4Aux.rank_le_card_of_atoms (N := n) c θ a (Finset.univ.erase t) hrep'
    rw [Finset.card_erase_of_mem (Finset.mem_univ t)] at h
    rw [← hTT] at h
    have ht' := t.isLt
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  -- Reality and positivity of the coefficients.
  have hsecPSD : (F2.section' (r := q) c).PosSemidef := hblockPSD q (by omega)
  have ha_im : ∀ s, (a s).im = 0 := F2.F2_b (r := q) (n := n) hqn θ hθ_inj c a hHerm hrep
  have ha_re : ∀ s, 0 < (a s).re :=
    F2.F2_c (r := q) (n := n) hqn θ hθ_inj c a hHerm hrep hsecPSD hmin
  subst hqr
  refine ⟨θ, fun s => (a s).re, ha_re, fun m hm => ?_⟩
  rw [hrep m hm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hre : (((a s).re : ℝ) : ℂ) = a s := by
    apply Complex.ext <;> simp [ha_im s]
  rw [hre]

end D4
