import Mathlib

open scoped BigOperators Matrix ComplexOrder
open Complex

namespace F3R

/-!
# F3R. Annihilator roots are unimodular and simple (isometry route)

Let `T` be an `(r+1) × (r+1)` Hermitian PSD Toeplitz matrix `T j k = c (j−k)` whose leading
`r × r` block is positive definite but which is itself singular.  Let `u` be a nonzero null
vector and `P(z) = ∑ k, u k · z^k`.  Then all roots of `P` lie on the unit circle and are simple.

Route (Szegő/CMV isometry / shift identity): the leading-block Hermitian form
`Q(a) = ∑_{i,j} conj (a i)·c(i−j)·a j` is positive definite (that is `hlead`).  From the null
relation `T·u = 0` and a root `P(z) = 0` one derives the scalar identity
`(z·conj z − 1)·Q(v) = 0` with `v k := u (castSucc k)`; since `Q(v) > 0` this forces
`‖z‖² = 1`.

Status: both halves are now proved.  `F3R_unimodular` (all roots unimodular) follows the
shift-identity route (helper lemmas `F3R_uLast_ne`, `F3R_v_ne`, `Qform_eq`, `F3R_Qpos`,
`F3R_Hform_conj`, `F3R_Hform_u_zero`, `F3R_pad0_Q`, `F3R_shift_inv`, `F3R_coeff`, and
`F3R_identity`).  `F3R_simple` (simplicity) is obtained by pushing the very same shift identity
one level deeper: a double root `z` of `P` would give `P = (X − z)·G` with `G = (X − z)·K`, and
the null relation plus the bilinear shift invariance `F3R_shift_inv'` then force the
leading-block form of the coefficient vector `g` of `G` to vanish, contradicting positive
definiteness (`F3R_no_double`).  No unitary diagonalization is needed.
-/

variable {r : ℕ}

/-- The `(r+1) × (r+1)` Hermitian Toeplitz matrix `T j k = c (j − k)`. -/
def toeplitz (c : ℤ → ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- The leading `r × r` principal block. -/
def leadingBlock (c : ℤ → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- The annihilator polynomial `P(z) = ∑ k, u k · z^k`. -/
noncomputable def annihilator (u : Fin (r + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (r + 1), Polynomial.C (u k) * Polynomial.X ^ (k : ℕ)

/-- The leading-block Hermitian form value `Q(a) = ∑_{i,j} conj (a i)·c(i−j)·a j`. -/
noncomputable def Qform (c : ℤ → ℂ) (a : Fin r → ℂ) : ℂ :=
  ∑ i : Fin r, ∑ j : Fin r, (starRingEnd ℂ (a i)) * c ((i : ℤ) - (j : ℤ)) * a j

/-
`Qform` agrees with the leading-block quadratic form `star a ⬝ᵥ B.mulVec a`.
-/
theorem Qform_eq (c : ℤ → ℂ) (a : Fin r → ℂ) :
    Qform c a = star a ⬝ᵥ (leadingBlock (r := r) c).mulVec a := by
  unfold Qform leadingBlock;
  simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ]

/-
The leading-block Hermitian form is (real and) strictly positive on nonzero vectors.
-/
theorem F3R_Qpos (c : ℤ → ℂ) (hlead : (leadingBlock (r := r) c).PosDef)
    (a : Fin r → ℂ) (ha : a ≠ 0) : 0 < (Qform c a).re := by
  obtain ⟨ v, hv ⟩ := hlead;
  specialize @hv ( Finsupp.equivFunOnFinite.symm a ) ; simp_all +decide [ Finsupp.sum_fintype, Qform ];
  simp_all +decide [ Complex.lt_def, Finsupp.ext_iff, funext_iff ];
  exact hv.1

/-
The top coefficient of a null vector is nonzero (leading block is PD).
-/
theorem F3R_uLast_ne (c : ℤ → ℂ) (hlead : (leadingBlock (r := r) c).PosDef)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) : u (Fin.last r) ≠ 0 := by
  intro h_last_zero;
  -- Since `u (Fin.last r) = 0`, we have `((leadingBlock c).mulVec (fun k => u (Fin.castSucc k))) = 0`.
  have h_leading_block : (leadingBlock (r := r) c).mulVec (fun k => u (Fin.castSucc k)) = 0 := by
    ext i; replace hnull := congr_fun hnull ( Fin.castSucc i ) ; simp_all +decide [ Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc ] ;
    convert hnull using 1;
  exact hu <| funext fun i => Fin.lastCases h_last_zero ( fun i => by simpa [ h_last_zero ] using congr_fun ( Matrix.eq_zero_of_mulVec_eq_zero hlead.det_pos.ne' h_leading_block ) i ) i

/-
The restriction `v k = u (castSucc k)` of a null vector is nonzero (for `r ≥ 1`).
-/
theorem F3R_v_ne (c : ℤ → ℂ) (hr : 0 < r) (hlead : (leadingBlock (r := r) c).PosDef)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) :
    (fun k : Fin r => u (Fin.castSucc k)) ≠ 0 := by
  contrapose! hu with h;
  ext i; induction i using Fin.lastCases <;> simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ] ;
  -- By definition of $toeplitz$, we know that $toeplitz c (Fin.last r) (Fin.last r) = c 0$.
  have h_toeplitz_last : toeplitz c (Fin.last r) (Fin.last r) = c 0 := by
    unfold toeplitz; norm_num;
  -- Since $c 0$ is the top-left diagonal entry of the positive-definite matrix $leadingBlock c$, it must be positive.
  have h_c0_pos : 0 < (c 0).re := by
    convert F3R_Qpos c hlead ( Pi.single ⟨ 0, hr ⟩ 1 ) ( by intros h; simpa using congr_fun h ⟨ 0, hr ⟩ ) using 1 ; simp +decide [ Qform_eq ];
    unfold leadingBlock; aesop;
  specialize hnull ( Fin.last r ) ; simp_all +decide [ Fin.sum_univ_castSucc ] ;
  exact hnull.resolve_left ( by rintro h; norm_num [ h ] at h_c0_pos )

/-- The full `(r+1)`-dimensional Hermitian sesquilinear form of the Toeplitz data. -/
noncomputable def Hform (c : ℤ → ℂ) (a b : Fin (r + 1) → ℂ) : ℂ :=
  ∑ i : Fin (r + 1), ∑ j : Fin (r + 1), (starRingEnd ℂ (a i)) * c ((i : ℤ) - (j : ℤ)) * b j

/-- `pad0 g` places `g` in slots `0..r-1` and `0` in the top slot. -/
def pad0 (g : Fin r → ℂ) : Fin (r + 1) → ℂ :=
  fun i => if h : (i : ℕ) < r then g ⟨i, h⟩ else 0

/-- `shift1 g` places `g` up-shifted into slots `1..r` and `0` in slot `0`. -/
def shift1 (g : Fin r → ℂ) : Fin (r + 1) → ℂ :=
  fun i => if h : 1 ≤ (i : ℕ) ∧ (i : ℕ) - 1 < r then g ⟨(i : ℕ) - 1, h.2⟩ else 0

/-
The full form is conjugate-symmetric (uses `hHerm`).
-/
theorem F3R_Hform_conj (c : ℤ → ℂ) (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (a b : Fin (r + 1) → ℂ) : Hform c a b = starRingEnd ℂ (Hform c b a) := by
  unfold Hform; simp +decide [ *, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc ] ;
  rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; ring;
  grind

/-
The full form against a null vector vanishes (uses `hnull`).
-/
theorem F3R_Hform_u_zero (c : ℤ → ℂ) (u : Fin (r + 1) → ℂ)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) (a : Fin (r + 1) → ℂ) :
    Hform c a u = 0 := by
  convert congr_arg ( fun x => ∑ i : Fin ( r + 1 ), ( starRingEnd ℂ ( a i ) ) * x i ) hnull using 1;
  · simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by unfold toeplitz; ring;
  · norm_num

/-
The full form on `pad0 g` reduces to the leading-block form `Qform c g`.
-/
theorem F3R_pad0_Q (c : ℤ → ℂ) (g : Fin r → ℂ) :
    Hform c (pad0 g) (pad0 g) = Qform c g := by
  unfold Hform Qform pad0;
  cases r <;> simp +decide [ Fin.sum_univ_castSucc ]

/-
Shift invariance of the full form (Toeplitz shift identity).
-/
theorem F3R_shift_inv (c : ℤ → ℂ) (g : Fin r → ℂ) :
    Hform c (shift1 g) (shift1 g) = Hform c (pad0 g) (pad0 g) := by
  -- Show that both forms reduce to the same sum.
  have hL : Hform c (shift1 g) (shift1 g) = ∑ i : Fin r, ∑ j : Fin r, (starRingEnd ℂ (g i)) * c ((i : ℤ) - (j : ℤ)) * g j := by
    unfold Hform; simp +decide [ shift1 ] ;
    rcases r with ( _ | r ) <;> simp_all +decide [ Fin.sum_univ_succ ];
  rw [ hL, F3R_pad0_Q ];
  rfl

/-
Coefficient relation from the factorization `P = (X - z)·G`: there is a nonzero `g` with
`u i = shift1 g i - z · pad0 g i` for all `i`.
-/
theorem F3R_coeff (c : ℤ → ℂ) (hr : 0 < r) (hlead : (leadingBlock (r := r) c).PosDef)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0) (hnull : (toeplitz (r := r) c).mulVec u = 0)
    (z : ℂ) (hroot : ∑ k : Fin (r + 1), u k * z ^ (k : ℕ) = 0) :
    ∃ g : Fin r → ℂ, g ≠ 0 ∧ ∀ i : Fin (r + 1), u i = shift1 g i - z * pad0 g i := by
  obtain ⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ i : Fin (r + 1), u i = shift1 g i - z * pad0 g i := by
    -- Set `g : Fin r → ℂ := fun k => G.coeff (k : ℕ)`.
    obtain ⟨G, hG⟩ : ∃ G : Polynomial ℂ, G.natDegree ≤ r - 1 ∧ ∀ i : Fin (r + 1), u i = Polynomial.coeff ((Polynomial.X - Polynomial.C z) * G) i := by
      obtain ⟨G, hG⟩ : ∃ G : Polynomial ℂ, Polynomial.natDegree G ≤ r ∧ ∀ i : Fin (r + 1), u i = (G.coeff i) ∧ G.IsRoot z := by
        refine' ⟨ ∑ i : Fin ( r + 1 ), Polynomial.C ( u i ) * Polynomial.X ^ ( i : ℕ ), _, _ ⟩;
        · exact le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le fun i hi => Polynomial.natDegree_C_mul_X_pow_le _ _ |> le_trans <| Nat.le_of_lt_succ <| Fin.is_lt i );
        · simp_all +decide [ Polynomial.eval_finset_sum ];
          simp +decide [ Finset.sum_ite, Fin.val_inj ];
      obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℂ, G = (Polynomial.X - Polynomial.C z) * Q := by
        exact Polynomial.dvd_iff_isRoot.mpr ( hG.2 0 |>.2 );
      by_cases hQ_zero : Q = 0 <;> simp_all +decide [ Polynomial.natDegree_mul' ];
      · exact False.elim <| hu <| funext hG;
      · exact ⟨ Q, Nat.le_sub_one_of_lt ( by linarith ), fun i => rfl ⟩;
    use fun k => G.coeff k.val;
    intro i; rw [ hG.2 i ] ; simp +decide [ Polynomial.coeff_X, Polynomial.coeff_C, sub_mul, mul_assoc, Finset.sum_range_succ', shift1, pad0 ] ;
    rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ Polynomial.coeff_X, mul_assoc ];
    split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
    exact Or.inr ( Polynomial.coeff_eq_zero_of_natDegree_lt <| by omega );
  refine' ⟨ g, _, hg ⟩ ; contrapose! hu ; simp_all +decide [ funext_iff ] ;
  unfold shift1 pad0; aesop;

/-- The scalar shift identity: from `T·u = 0` and `P(z) = 0`, `(z·conj z − 1)·Q(v) = 0`. -/
theorem F3R_identity (c : ℤ → ℂ) (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hlead : (leadingBlock (r := r) c).PosDef)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0) (hnull : (toeplitz (r := r) c).mulVec u = 0)
    (z : ℂ) (hroot : ∑ k : Fin (r + 1), u k * z ^ (k : ℕ) = 0) :
    (z * starRingEnd ℂ z - 1) * Qform c (fun k : Fin r => u (Fin.castSucc k)) = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [Qform]
  -- Factorization data.
  obtain ⟨g, hg0, hgu⟩ := F3R_coeff c hr hlead u hu hnull z hroot
  -- `Hform` is ℂ-linear in its second argument along `u = shift1 g - z • pad0 g`.
  have hlin : ∀ a : Fin (r + 1) → ℂ,
      Hform c a u = Hform c a (shift1 g) - z * Hform c a (pad0 g) := by
    intro a
    unfold Hform
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [hgu j]; ring
  have h1 := F3R_Hform_u_zero c u hnull (pad0 g)
  have h2 := F3R_Hform_u_zero c u hnull (shift1 g)
  rw [hlin (pad0 g)] at h1
  rw [hlin (shift1 g)] at h2
  -- Abbreviate the (real, positive) block value.
  have hshift := F3R_shift_inv c g
  have hsym := F3R_Hform_conj c hHerm (shift1 g) (pad0 g)
  have hQreal := F3R_Hform_conj c hHerm (pad0 g) (pad0 g)
  have e1 : Hform c (pad0 g) (shift1 g) = z * Hform c (pad0 g) (pad0 g) := by
    linear_combination h1
  -- Combine everything into `(z·conj z − 1)·Hform(pad0 g)(pad0 g) = 0`.
  have key : (z * starRingEnd ℂ z - 1) * Hform c (pad0 g) (pad0 g) = 0 := by
    have h2' := h2
    rw [hshift, hsym, e1, map_mul] at h2'
    -- h2' : Hform(pad0)(pad0) - z * (conj z * conj (Hform(pad0)(pad0))) = 0
    have hQ : starRingEnd ℂ (Hform c (pad0 g) (pad0 g)) = Hform c (pad0 g) (pad0 g) :=
      hQreal.symm
    rw [hQ] at h2'
    linear_combination -h2'
  -- The block value is nonzero (positive real part), so `z·conj z = 1`.
  have hQne : Hform c (pad0 g) (pad0 g) ≠ 0 := by
    rw [F3R_pad0_Q]
    intro h
    have := F3R_Qpos c hlead g hg0
    rw [h] at this; simp at this
  have hzz : z * starRingEnd ℂ z - 1 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hQne
  rw [hzz, zero_mul]

/-- All roots of the annihilator lie on the unit circle. -/
theorem F3R_unimodular (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (r := r) c).PosSemidef)
    (hlead : (leadingBlock (r := r) c).PosDef)
    (hsing : (toeplitz (r := r) c).det = 0)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) :
    ∀ z ∈ (annihilator u).roots, ‖z‖ = 1 := by
  intro z hz
  -- The `r = 0` case is vacuous: the annihilator is a nonzero constant, so has no roots.
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hC : annihilator u = Polynomial.C (u 0) := by
      simp [annihilator]
    rw [hC, Polynomial.roots_C] at hz
    simp at hz
  -- Extract the root condition `∑ k, u k * z^k = 0`.
  have hroot : ∑ k : Fin (r + 1), u k * z ^ (k : ℕ) = 0 := by
    have h := Polynomial.isRoot_of_mem_roots hz
    simpa [annihilator, Polynomial.eval_finset_sum, Polynomial.IsRoot,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul] using h
  -- The scalar identity and positivity of the block form.
  have hid := F3R_identity c hHerm hlead u hu hnull z hroot
  have hv : (fun k : Fin r => u (Fin.castSucc k)) ≠ 0 := F3R_v_ne c hr hlead u hu hnull
  have hQpos : 0 < (Qform c (fun k : Fin r => u (Fin.castSucc k))).re := F3R_Qpos c hlead _ hv
  have hQne : Qform c (fun k : Fin r => u (Fin.castSucc k)) ≠ 0 := by
    intro h; rw [h] at hQpos; simp at hQpos
  -- Hence `z * conj z = 1`.
  have hzz : z * starRingEnd ℂ z = 1 := by
    have := mul_eq_zero.mp hid
    rcases this with h | h
    · linear_combination h
    · exact absurd h hQne
  -- `z * conj z = ↑(normSq z)`, so `normSq z = 1`, giving `‖z‖ = 1`.
  have hns : (Complex.normSq z : ℂ) = 1 := by
    rw [← Complex.mul_conj]; exact hzz
  have hns' : Complex.normSq z = 1 := by exact_mod_cast hns
  have h2 : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]; exact hns'
  nlinarith [norm_nonneg z, h2]

/-!
### Simplicity of the roots

The remaining statement `F3R_simple` is proved below by the same shift-identity mechanism that
gives unimodularity, applied one level deeper.  If `z` were a double root of `P`, then
`P = (X - z)·G` with `G = (X - z)·K`, and writing `A = pad0 (pad0 k)`, `B = shift1 (pad0 k)`
(where `k` collects the coefficients of `K`), the relations `H(·, u) = 0` together with the
Toeplitz shift invariance `H(shift1 x, shift1 y) = H(pad0 x, pad0 y)` force
`conj z · H(A,B) + z · conj (H(A,B)) = 2·H(A,A)`, whence the leading-block form of the
coefficient vector `g` of `G` vanishes: `Qform c g = 0`.  Since `g ≠ 0` and the leading block is
positive definite, this is a contradiction.
-/

/-- Sesquilinearity of `Hform` in its second (linear) argument. -/
theorem Hform_right_comb (c : ℤ → ℂ) (a x y : Fin (r + 1) → ℂ) (w : ℂ) :
    Hform c a (fun i => x i - w * y i) = Hform c a x - w * Hform c a y := by
  unfold Hform
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Sesquilinearity of `Hform` in its first (conjugate-linear) argument. -/
theorem Hform_left_comb (c : ℤ → ℂ) (x y b : Fin (r + 1) → ℂ) (w : ℂ) :
    Hform c (fun i => x i - w * y i) b = Hform c x b - starRingEnd ℂ w * Hform c y b := by
  unfold Hform
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_sub, map_mul]
  ring

/-- Bilinear form of the Toeplitz shift invariance. -/
theorem F3R_shift_inv' (c : ℤ → ℂ) (g h : Fin r → ℂ) :
    Hform c (shift1 g) (shift1 h) = Hform c (pad0 g) (pad0 h) := by
  have hL : Hform c (shift1 g) (shift1 h)
      = ∑ i : Fin r, ∑ j : Fin r, (starRingEnd ℂ (g i)) * c ((i : ℤ) - (j : ℤ)) * h j := by
    unfold Hform
    simp +decide [shift1]
    rcases r with _ | r <;> simp_all +decide [Fin.sum_univ_succ]
  have hR : Hform c (pad0 g) (pad0 h)
      = ∑ i : Fin r, ∑ j : Fin r, (starRingEnd ℂ (g i)) * c ((i : ℤ) - (j : ℤ)) * h j := by
    unfold Hform pad0
    cases r <;> simp +decide [Fin.sum_univ_castSucc]
  rw [hL, hR]

lemma pad0_sub_smul (x y : Fin r → ℂ) (w : ℂ) :
    pad0 (fun j => x j - w * y j) = fun i => pad0 x i - w * pad0 y i := by
  funext i; unfold pad0; split <;> simp

lemma shift1_sub_smul (x y : Fin r → ℂ) (w : ℂ) :
    shift1 (fun j => x j - w * y j) = fun i => shift1 x i - w * shift1 y i := by
  funext i; unfold shift1; split <;> simp

lemma pad0_shift1_comm {m : ℕ} (k : Fin (m + 1) → ℂ) :
    pad0 (shift1 k) = shift1 (pad0 (r := m + 1) k) := by
  funext i
  unfold pad0 shift1
  split_ifs with h1 h2 h3 h4 <;> simp_all <;> omega

lemma pad0_zero : pad0 (r := r) 0 = 0 := by
  funext i; unfold pad0; split <;> simp

lemma shift1_zero : shift1 (r := r) 0 = 0 := by
  funext i; unfold shift1; split <;> simp

/-- The coefficients of `(X - z)·Q`, read off as a vector of length `N + 2`, are
`shift1 q - z • pad0 q`, where `q` is the coefficient vector of `Q` of length `N + 1`. -/
lemma vec_X_sub_C_mul {N : ℕ} (Q : Polynomial ℂ) (hQ : Q.natDegree ≤ N) (z : ℂ)
    (i : Fin (N + 2)) :
    ((Polynomial.X - Polynomial.C z) * Q).coeff (i : ℕ)
      = shift1 (fun j : Fin (N + 1) => Q.coeff (j : ℕ)) i
        - z * pad0 (fun j : Fin (N + 1) => Q.coeff (j : ℕ)) i := by
  have hp : pad0 (fun j : Fin (N + 1) => Q.coeff (j : ℕ)) i = Q.coeff (i : ℕ) := by
    unfold pad0
    split_ifs with h
    · rfl
    · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
  · have hs : shift1 (fun j : Fin (N + 1) => Q.coeff (j : ℕ)) i = 0 := by
      unfold shift1; rw [dif_neg]; omega
    rw [hs, hp, h0]
    simp
  · have hs : shift1 (fun j : Fin (N + 1) => Q.coeff (j : ℕ)) i = Q.coeff ((i : ℕ) - 1) := by
      unfold shift1
      rw [dif_pos ⟨h0, by omega⟩]
    rw [hs, hp]
    obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = j + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [hj]
    simp [sub_mul, Polynomial.coeff_X_mul]

/-- The coefficients of the annihilator polynomial are the entries of `u`. -/
lemma annihilator_coeff (u : Fin (r + 1) → ℂ) (i : Fin (r + 1)) :
    (annihilator u).coeff (i : ℕ) = u i := by
  unfold annihilator
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_eq_val, Ne.symm hb]
  · simp

lemma annihilator_natDegree_le (u : Fin (r + 1) → ℂ) : (annihilator u).natDegree ≤ r := by
  refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le fun i _ => ?_)
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (Nat.le_of_lt_succ (Fin.is_lt i))

/-- The key step: a double root is impossible.  Here `k` collects the coefficients of the
quotient `K` in `P = (X - z)^2·K`, `g` those of `(X - z)·K`. -/
theorem F3R_no_double {m : ℕ} (c : ℤ → ℂ)
    (hHerm : ∀ t : ℤ, c (-t) = starRingEnd ℂ (c t))
    (hlead : (leadingBlock (r := m + 2) c).PosDef)
    (u : Fin (m + 2 + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := m + 2) c).mulVec u = 0)
    (z : ℂ) (hz : z * starRingEnd ℂ z = 1)
    (k : Fin (m + 1) → ℂ) (g : Fin (m + 2) → ℂ)
    (hg : ∀ i, g i = shift1 k i - z * pad0 k i)
    (hug : ∀ i, u i = shift1 g i - z * pad0 g i) : False := by
  have hgf : g = fun j => shift1 k j - z * pad0 k j := funext hg
  have huf : u = fun i => shift1 g i - z * pad0 g i := funext hug
  set A : Fin (m + 2 + 1) → ℂ := pad0 (pad0 k) with hA
  set B : Fin (m + 2 + 1) → ℂ := shift1 (pad0 k) with hB
  have hAg : pad0 g = fun i => B i - z * A i := by
    rw [hgf, pad0_sub_smul, pad0_shift1_comm]
  -- The null relation, expanded along `u = shift1 g - z • pad0 g`.
  have hzero : ∀ x : Fin (m + 2 + 1) → ℂ,
      Hform c x (shift1 g) - z * Hform c x (pad0 g) = 0 := by
    intro x
    have h := F3R_Hform_u_zero c u hnull x
    rw [huf, Hform_right_comb] at h
    exact h
  have hsi1 : Hform c B (shift1 g) = Hform c A (pad0 g) := F3R_shift_inv' c (pad0 k) g
  have hsi2 : Hform c B B = Hform c A A := F3R_shift_inv' c (pad0 k) (pad0 k)
  have hconj : Hform c B A = starRingEnd ℂ (Hform c A B) := F3R_Hform_conj c hHerm B A
  have hexpA : Hform c A (pad0 g) = Hform c A B - z * Hform c A A := by
    rw [hAg, Hform_right_comb]
  have hexpB : Hform c B (pad0 g) = Hform c B B - z * Hform c B A := by
    rw [hAg, Hform_right_comb]
  have hrel : Hform c A B - z * Hform c A A
      = z * (Hform c A A - z * starRingEnd ℂ (Hform c A B)) := by
    have h := hzero B
    rw [hsi1, hexpA, hexpB, hsi2, hconj] at h
    linear_combination h
  have hkey : starRingEnd ℂ z * Hform c A B + z * starRingEnd ℂ (Hform c A B)
      = 2 * Hform c A A := by
    linear_combination (starRingEnd ℂ z) * hrel
      - (z * starRingEnd ℂ (Hform c A B) - 2 * Hform c A A) * hz
  have hQ0 : Hform c (pad0 g) (pad0 g) = 0 := by
    rw [hAg, Hform_left_comb, Hform_right_comb, Hform_right_comb, hsi2, hconj]
    linear_combination -hkey + Hform c A A * hz
  rw [F3R_pad0_Q] at hQ0
  have hgne : g ≠ 0 := by
    intro h0
    apply hu
    rw [huf, h0]
    funext i
    simp [pad0_zero, shift1_zero]
  have hpos := F3R_Qpos c hlead g hgne
  rw [hQ0] at hpos
  simp at hpos

/-- The roots of the annihilator are simple. -/
theorem F3R_simple (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (r := r) c).PosSemidef)
    (hlead : (leadingBlock (r := r) c).PosDef)
    (hsing : (toeplitz (r := r) c).det = 0)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) :
    (annihilator u).roots.Nodup := by
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · -- Degree `≤ 1`: at most one root.
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    have h1 : Multiset.card (annihilator u).roots ≤ r :=
      le_trans (Polynomial.card_roots' _) (annihilator_natDegree_le u)
    have h2 := Multiset.count_le_card a (annihilator u).roots
    omega
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  by_contra hcount
  push_neg at hcount
  have hz_mem : z ∈ (annihilator u).roots := by
    rw [← Multiset.count_pos]; omega
  have hnorm : ‖z‖ = 1 := F3R_unimodular c hHerm hPSD hlead hsing u hu hnull z hz_mem
  have hzz : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hnorm]
    norm_num
  have hP0 : annihilator u ≠ 0 := by
    intro h
    apply hu
    funext i
    rw [← annihilator_coeff u i, h]
    simp
  have hdvd : (Polynomial.X - Polynomial.C z) ^ 2 ∣ annihilator u := by
    refine dvd_trans (pow_dvd_pow _ ?_) (Polynomial.pow_rootMultiplicity_dvd (annihilator u) z)
    rw [← Polynomial.count_roots]
    omega
  obtain ⟨K, hK⟩ := hdvd
  have hK0 : K ≠ 0 := by
    rintro rfl
    exact hP0 (by simp [hK])
  have hdegP : (annihilator u).natDegree ≤ m + 2 := annihilator_natDegree_le u
  have hdegK : K.natDegree ≤ m := by
    have hmul : ((Polynomial.X - Polynomial.C z) ^ 2 * K).natDegree = 2 + K.natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero z)) hK0,
        Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    rw [hK, hmul] at hdegP
    omega
  have hdegK1 : ((Polynomial.X - Polynomial.C z) * K).natDegree ≤ m + 1 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_X_sub_C]
    omega
  refine F3R_no_double c hHerm hlead u hu hnull z hzz
    (fun j : Fin (m + 1) => K.coeff (j : ℕ))
    (fun j : Fin (m + 2) => ((Polynomial.X - Polynomial.C z) * K).coeff (j : ℕ)) ?_ ?_
  · intro i
    exact vec_X_sub_C_mul K hdegK z i
  · intro i
    rw [← annihilator_coeff u i, hK,
      show (Polynomial.X - Polynomial.C z) ^ 2 * K
        = (Polynomial.X - Polynomial.C z) * ((Polynomial.X - Polynomial.C z) * K) by ring]
    exact vec_X_sub_C_mul ((Polynomial.X - Polynomial.C z) * K) hdegK1 z i

/-- Combined: all roots of the annihilator lie on the unit circle and are simple. -/
theorem F3R_roots (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (r := r) c).PosSemidef)
    (hlead : (leadingBlock (r := r) c).PosDef)
    (hsing : (toeplitz (r := r) c).det = 0)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) :
    (∀ z ∈ (annihilator u).roots, ‖z‖ = 1) ∧ (annihilator u).roots.Nodup :=
  ⟨F3R_unimodular c hHerm hPSD hlead hsing u hu hnull,
   F3R_simple c hHerm hPSD hlead hsing u hu hnull⟩

end F3R