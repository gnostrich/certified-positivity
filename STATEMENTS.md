# STATEMENTS.md — the exact formal claims

Prose is not the claim; these statements are. Every block below is verbatim
from the named source file (proof bodies omitted). To evaluate this repo,
read the definitions first — they fix what the theorems mean — then the
theorem statements. What is proved is exactly this, no more and no less.

## Core definitions (these fix the meaning of everything below)

### `V5_1.lean` — `primeSum`
```lean
noncomputable def primeSum (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
    (Λ n / Real.sqrt n) * (t - Real.log n)
```

### `V5_1.lean` — `PsiArch`
```lean
noncomputable def PsiArch (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    (t / 2) * (A - Real.log Real.pi) +
    (1 / 4) * (C - Real.exp (-t / 2) * L t)
```

### `V5_1.lean` — `Psi`
```lean
noncomputable def Psi (t : ℝ) : ℝ := PsiNonneg |t|
```

### `V5_1.lean` — `G`
```lean
noncomputable def G (t u : ℝ) : ℝ := Psi t + Psi u - Psi (t - u)
```

### `Horizon.lean` — `quadForm`
```lean
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j
```

### `Horizon.lean` — `IsPDq`
```lean
def IsPDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x
```

### `V5_5.lean` — `M3`
```lean
noncomputable def M3 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  let t : Fin 3 → ℝ := ![0.2, 0.4, 0.6]
  V5_1.G (t i) (t j)

/-
Certified enclosures sufficient for the prime-free certificate.
-/
```

### `V5_5.lean` — `true_kernel_grid_margin`
```lean
theorem true_kernel_grid_margin (x : Fin 3 → ℝ) :
    (0.005 : ℝ) * ∑ i, x i ^ 2 ≤ quadForm M3 x := by (proof omitted)
```

### `V5_5.lean` — `true_kernel_grid_posdef`
```lean
theorem true_kernel_grid_posdef : IsPDq M3 := by (proof omitted)
```

### `V5_6.lean` — `true_kernel_first_prime_posdef`
```lean
theorem true_kernel_first_prime_posdef : IsPDq M2 := by (proof omitted)
```

### `V5_7.lean` — `weil_triangle_prime_side`
```lean
theorem weil_triangle_prime_side (t : ℝ) (ht : 0 < t) (N : ℕ)
    (hN : Real.exp t ≤ N) :
    ∑ n ∈ Finset.Icc 2 N,
        (Λ n / Real.sqrt n) *
          (triangle t (Real.log n) + triangle t (-Real.log n)) = V5_1.primeSum t := by (proof omitted)
```

### `R_A1.lean` — `schur`
```lean
noncomputable def schur (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) : ℝ :=
  d - dotProduct b (A⁻¹ *ᵥ b)
```

### `R_A1.lean` — `border`
```lean
def border (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else b ⟨i.val, hi⟩
  else if hj : j.val < n then b ⟨j.val, hj⟩ else d
```

### `R_A1.lean` — `schur_pos_isPDq`
```lean
theorem schur_pos_isPDq (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (hPD : IsPDq A) (b : Fin n → ℝ) (d : ℝ) (hs : 0 < schur A b d) :
    IsPDq (border A b d) := by (proof omitted)
```

### `R_A2.lean` — `GramState`
```lean
structure GramState where
  dim : ℕ
  M : Matrix (Fin dim) (Fin dim) ℝ
  hsymm : Mᵀ = M
  hpd : IsPDq M
  nonempty : NeZero dim

namespace GramState
```

### `R_A2.lean` — `margin_le`
```lean
theorem margin_le (G : GramState) : G.margin ≤ lambdaMin G.M := by (proof omitted)
```

### `R_A3_A4.lean` — `expand_pd`
```lean
theorem expand_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) : IsPDq (G.expand b d hs).M :=
  (G.expand b d hs).hpd
```

### `R_A3_A4.lean` — `halt_not_pd`
```lean
theorem halt_not_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : schur G.M b d ≤ 0) : ¬ IsPDq (border G.M b d) := by (proof omitted)
```

### `R_A5.lean` — `isPDq_iff_nMinus_nZero_eq_zero`
```lean
theorem isPDq_iff_nMinus_nZero_eq_zero (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) :
    IsPDq M ↔ nMinus M hM 0 = 0 ∧ nZero M hM 0 = 0 := by (proof omitted)
```

### `R_A6.lean` — `trueKernelGridState_matrix`
```lean
theorem trueKernelGridState_matrix : trueKernelGridState.M = V5_5.M3 := by (proof omitted)
```

### `R_B1.lean` — `checkPDq_sound`
```lean
theorem checkPDq_sound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (h : checkPDq M = true) : IsPDq (M.map (Rat.cast : ℚ → ℝ)) := by (proof omitted)
```

### `R5.lean` — `PsiArch_not_convex`
```lean
theorem PsiArch_not_convex :
    ¬ ConvexOn ℝ (Set.Icc (0 : ℝ) (2 / 5)) V5_1.PsiArch := by (proof omitted)
```

### `R5.lean` — `coverage_prime_free`
```lean
theorem coverage_prime_free :
    ¬ ∃ δ μ : ℝ, CoveragePrimeFree δ μ := by (proof omitted)
```

### `R5Prime.lean` — `gershgorin_margin`
```lean
theorem gershgorin_margin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (μ : ℝ)
    (hrow : ∀ i, μ + ∑ j with j ≠ i, |M i j| ≤ M i i) :
    ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ quadForm M x := by (proof omitted)
```

### `R5Prime.lean` — `coverage_band`
```lean
theorem coverage_band :
    ∃ (δ μ : ℝ), 0 < δ ∧ 0 < μ ∧
      ∀ (t : Fin 2 → ℝ), StrictMono t →
        (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
        (∀ i j, i ≠ j → δ ≤ |t i - t j|) →
        IsPDq (fun i j => V5_1.G (t i) (t j)) ∧
          μ ≤ lambdaMin (fun i j => V5_1.G (t i) (t j)) := by (proof omitted)
```

### `R5Final.lean` — `three_grid_last_row_gershgorin_zero`
```lean
lemma three_grid_last_row_gershgorin_zero :
    let t : Fin 3 → ℝ := ![1 / 5, 2 / 5, 3 / 5]
    V5_1.G (t 2) (t 2) = V5_1.G (t 2) (t 0) + V5_1.G (t 2) (t 1) := by (proof omitted)
```

### `R5Final.lean` — `coverage_band_final`
```lean
theorem coverage_band_final :
    ∃ (δ μ : ℝ), 0 < δ ∧ 0 < μ ∧
      ∀ (t : Fin 3 → ℝ), StrictMono t →
        (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
        (∀ i j, i ≠ j → δ ≤ |t i - t j|) →
        IsPDq (fun i j => V5_1.G (t i) (t j)) ∧
          μ ≤ lambdaMin (fun i j => V5_1.G (t i) (t j)) :=
  coverage_band_k

/-
Final frontier corollary.  Under the same explicit coarse mesh, the
three-site true-kernel matrix is represented by the state constructed in
`R_A6` literally by `singleton` and two successful `expand` operations.
Thus all two Schur gates are discharged by the existing audited construction.
-/
```

### `R5Final.lean` — `frontier_covers_band_final`
```lean
theorem frontier_covers_band_final :
    ∀ (t : Fin 3 → ℝ), StrictMono t →
      (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
      (∀ i j, i ≠ j → (1 / 5 : ℝ) ≤ |t i - t j|) →
      ∃ G : TierR.GramState,
        G.dim = 3 ∧ HEq G.M (fun i j => V5_1.G (t i) (t j)) := by (proof omitted)
```

### `G3.lean` — `G3_cert_neg` (the newest-binds refutation certificate)
```lean
theorem G3_cert_neg :
    ¬ IsPDq (U 0.789 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) :=
  G3_b_neg _ _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2 G2.G2_atom5.1 G2.G2_atom5.2
```

### `G5.lean` — `G5_c_prime` (atom maximality)
```lean
theorem G5_c_prime (p : ℕ) (hp : p.Prime) (hp7 : p ≠ 7) :
    Real.log p / Real.sqrt p < Real.log 7 / Real.sqrt 7 := by (proof omitted)
```

## What we do NOT claim

- No statement here is about the Riemann Hypothesis, and none implies progress on it.
- All positivity results are about SPECIFIC finite grids at specific rationals;
  there is no infinite-grid or all-mesh statement anywhere in the corpus.
- `coverage_band_final` covers the single 3-point grid (1/5, 2/5, 3/5); the
  fine-grid regime is explicitly open (see TIER_R_FINAL.md).
- Three `sorry` sites exist (D4, F3, F3R), one shared cause (unitary
  diagonalizability, absent from Mathlib); nothing below depends on them.
- `G5`/`G6` inherit `native_decide` axioms via `G4`→`E2` (integer-power
  comparison + legacy log bounds); `G3_cert_neg` likewise sits downstream of
  `E2` via the `E3`/`G2` atoms it cites; the V5 and R tiers are
  native_decide-free.
- `Psi` uses the even-extension convention `Psi t = PsiNonneg |t|`; the prime
  sum is over `2 ≤ n ≤ ⌊exp t⌋` with von Mangoldt weights, as written above.
- Proof terms were produced by an automated prover and audited at STATEMENT
  level only (AI-assisted); the trust anchor is Lean's kernel plus the axiom
  audit, not human proof-reading.
