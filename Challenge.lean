import Mathlib

/-!
# Challenge.lean — Mathlib-only statements of the headline theorems

This file states, with `sorry` as every proof, the headline theorems of this
repository. It imports **only Mathlib** — no repository modules — and inlines
every custom definition the statements need, copied verbatim from the named
source files (see the `-- from <file>` markers). Its purpose is mechanical:
the statements here can be compared against the repository modules (e.g. with
a statement comparator) to check that the sorry-free proofs in `lean/` prove
exactly these claims and not something subtly different.

Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (as pinned by
`lean-toolchain` / `lakefile.toml` / `lake-manifest.json` at the repo root).
Checked: this file elaborates with no errors under that toolchain
(`lake env lean Challenge.lean`), emitting exactly the 18 expected
`declaration uses 'sorry'` warnings.

Because all definitions live here in the single namespace `Challenge`, the
namespace prefixes of the originals (`Horizon.`, `V5_1.`, `TierR.`,
`R5.`, …) are necessarily dropped; this is the one systematic transformation
applied to every inlined definition and statement. Individual deviations
beyond that are marked `-- deviates from repo statement:` at the theorem.

This file makes **no axiom claim**: every proof below is `sorry`, so
`#print axioms` on this file is meaningless by design. In the repository,
the proof of `G5_c_prime` inherits `native_decide` (`Lean.ofReduceBool`)
exposure via its imports `G4` → `E2`, as disclosed in the README and
STATEMENTS.md; the V5 and R tiers are `native_decide`-free. Axiom status of
the real proofs is a property of the repository modules, not of this file.
-/

open scoped BigOperators Matrix
open ArithmeticFunction

namespace Challenge

/-! ## Definitions — from `lean/Horizon.lean` (namespace `Horizon`) -/

variable {n : ℕ}

/-- The quadratic form `xᵀ M x`. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `M` is positive definite (quadratic-form definition). -/
def IsPDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x

/-- The set of Rayleigh values of `M` over the unit sphere. -/
def valueSet (M : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {r : ℝ | ∃ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) ∧ r = quadForm M x}

/-- The minimal eigenvalue, defined as the infimum of the Rayleigh quotient over unit vectors. -/
noncomputable def lambdaMin (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf (valueSet M)

/-! ## Definitions — from `lean/V5_1.lean` (namespace `V5_1`) -/

/-- The Hurwitz value `ζ(2,1/4)` in the normalization used by Suzuki. -/
noncomputable def C : ℝ := ∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2)

/-- The Hurwitz--Lerch series in the archimedean screw term. -/
noncomputable def L (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-2 * n * t) * (1 / ((n : ℝ) + 1 / 4) ^ 2)

/-- The constant `Γ'/Γ(1/4)`. -/
noncomputable def A : ℝ :=
  -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2

/-- Suzuki's archimedean screw component. -/
noncomputable def PsiArch (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    (t / 2) * (A - Real.log Real.pi) +
    (1 / 4) * (C - Real.exp (-t / 2) * L t)

/-- The finite prime-power contribution at nonnegative `t`. -/
noncomputable def primeSum (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
    (Λ n / Real.sqrt n) * (t - Real.log n)

/-- The nonnegative-half screw function. -/
noncomputable def PsiNonneg (t : ℝ) : ℝ := PsiArch t - primeSum t

/-- The full screw function, extended evenly. -/
noncomputable def Psi (t : ℝ) : ℝ := PsiNonneg |t|

/-- Krein's Gram kernel. -/
noncomputable def G (t u : ℝ) : ℝ := Psi t + Psi u - Psi (t - u)

/-! ## Definitions — from `lean/V5_5.lean` / `lean/V5_6.lean` / `lean/V5_7.lean`
(namespaces `V5_5`, `V5_6`, `V5_7`) -/

/-- The genuine screw Gram matrix on the grid `(0.2,0.4,0.6)`. -/
noncomputable def M3 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  let t : Fin 3 → ℝ := ![0.2, 0.4, 0.6]
  G (t i) (t j)

noncomputable def M2 : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  let t : Fin 2 → ℝ := ![0.4, 0.9]
  G (t i) (t j)

/-- The compactly supported triangular window. -/
noncomputable def triangle (t x : ℝ) : ℝ :=
  if |x| ≤ t then (t - |x|) / 2 else 0

/-! ## Definitions — from `lean/R_A1.lean` / `lean/R_A2.lean`
(namespace `TierR`) -/

/-- A symmetric one-site border of `A`, indexed so the old matrix is the top-left block. -/
def border (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else b ⟨i.val, hi⟩
  else if hj : j.val < n then b ⟨j.val, hj⟩ else d

/-- The scalar Schur complement of the border. -/
noncomputable def schur (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) : ℝ :=
  d - dotProduct b (A⁻¹ *ᵥ b)

/-- R-A2: a finite Gram matrix together with its symmetry and PD certificate.
The dimension is part of the state through the dependent matrix field. -/
structure GramState where
  dim : ℕ
  M : Matrix (Fin dim) (Fin dim) ℝ
  hsymm : Mᵀ = M
  hpd : IsPDq M
  nonempty : NeZero dim

/-! ## Definitions — from `lean/R_A5.lean` (namespace `TierR`) -/

/-- Number of eigenvalues strictly above a threshold. -/
noncomputable def nPlus (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => τ < (show M.IsHermitian from hM).eigenvalues i).card

/-- Number of eigenvalues equal to a threshold. -/
noncomputable def nZero (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (show M.IsHermitian from hM).eigenvalues i = τ).card

/-- Number of eigenvalues strictly below a threshold. -/
noncomputable def nMinus (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (show M.IsHermitian from hM).eigenvalues i < τ).card

/-! ## Definitions — from `lean/R_B1.lean` (namespace `TierR`) -/

/-- Rational leading principal submatrix, in the same indexing convention as D6. -/
def leadingSubRat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (k : Fin n) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  A.submatrix (fun i => Fin.castLE (by omega) i) (fun i => Fin.castLE (by omega) i)

/-- R-B1: exact executable Sylvester checker. Symmetry is checked as part of the Boolean,
since positivity of leading minors alone characterizes PD only for symmetric matrices. -/
def checkPDq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  decide (Mᵀ = M ∧ ∀ k : Fin n, 0 < (leadingSubRat M k).det)

/-! ## Definitions — from `lean/R5.lean` (namespace `R5`) -/

/-- The endpoint requested in R5, written exactly as the rational `0.69`. -/
noncomputable def b : ℝ := 69 / 100

/-- The exact hypotheses appearing in the proposed headline coverage theorem.
`adjacentGap` is vacuous for a singleton, as any ordinary minimum-gap condition
must be. -/
def adjacentGap {n : ℕ} (δ : ℝ) (t : Fin n → ℝ) : Prop :=
  ∀ i j, j.val = i.val + 1 → δ ≤ t j - t i

/-- Faithful formalization of the requested all-grid statement at `b = 0.69`.
It deliberately permits the left endpoint `0`, exactly as the prompt does. -/
def CoveragePrimeFree (δ μ : ℝ) : Prop :=
  0 < δ ∧ 0 < μ ∧
  ∀ (n : ℕ) [NeZero n] (t : Fin n → ℝ),
    StrictMono t →
    (∀ i, 0 ≤ t i) →
    (∀ i, t i ≤ b) →
    adjacentGap δ t →
    IsPDq (fun i j => G (t i) (t j)) ∧
      μ ≤ lambdaMin (fun i j => G (t i) (t j))

/-! ## Definitions — from `lean/G3.lean` (namespace `G3`) -/

/-- The third-window `4 × 4` form. -/
def U (κ u v w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![κ, u, v, w; u, κ, u, v; v, u, κ, u; w, v, u, κ]

/-! ## Headline theorems, stated with `sorry`
Sorry-free proofs live in the named repository modules. -/

/-- From `lean/V5_5.lean` (`V5_5.true_kernel_grid_margin`). -/
theorem true_kernel_grid_margin (x : Fin 3 → ℝ) :
    (0.005 : ℝ) * ∑ i, x i ^ 2 ≤ quadForm M3 x := by sorry

/-- From `lean/V5_5.lean` (`V5_5.true_kernel_grid_posdef`).
The true zeta screw kernel is positive definite on `(0.2,0.4,0.6)`. -/
theorem true_kernel_grid_posdef : IsPDq M3 := by sorry

/-- From `lean/V5_6.lean` (`V5_6.true_kernel_first_prime_posdef`). -/
theorem true_kernel_first_prime_posdef : IsPDq M2 := by sorry

/-- From `lean/V5_7.lean` (`V5_7.weil_triangle_prime_side`). -/
theorem weil_triangle_prime_side (t : ℝ) (ht : 0 < t) (N : ℕ)
    (hN : Real.exp t ≤ N) :
    ∑ n ∈ Finset.Icc 2 N,
        (Λ n / Real.sqrt n) *
          (triangle t (Real.log n) + triangle t (-Real.log n)) = primeSum t := by sorry

/-- From `lean/R_A1.lean` (`TierR.schur_pos_isPDq`).
R-A1(a,c): a positive Schur complement extends a positive-definite matrix. -/
theorem schur_pos_isPDq (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (hPD : IsPDq A) (b : Fin n → ℝ) (d : ℝ) (hs : 0 < schur A b d) :
    IsPDq (border A b d) := by sorry

/-- From `lean/R_A3_A4.lean` (`TierR.GramState.expand_pd`).
-- deviates from repo statement: the repo states `IsPDq (G.expand b d hs).M`,
where `expand` is a `GramState`-valued constructor whose `hsymm`/`hpd` fields
carry proofs and therefore cannot be inlined here without them. Since
`(G.expand b d hs).M` is definitionally `border G.M b d`, this matrix-level
form is the same claim with the constructor unfolded. -/
theorem expand_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) : IsPDq (border G.M b d) := by sorry

/-- From `lean/R_A3_A4.lean` (`TierR.GramState.halt_not_pd`).
Honest halt: failure of the strict scalar gate proves that the proposed border is not PD. -/
theorem halt_not_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : schur G.M b d ≤ 0) : ¬ IsPDq (border G.M b d) := by sorry

/-- From `lean/R_A5.lean` (`TierR.isPDq_iff_nMinus_nZero_eq_zero`).
R-A5(c): for a symmetric matrix, PD means that the zero-threshold meter has no
negative or zero eigenvalues. -/
theorem isPDq_iff_nMinus_nZero_eq_zero (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) :
    IsPDq M ↔ nMinus M hM 0 = 0 ∧ nZero M hM 0 = 0 := by sorry

/-- From `lean/R_B1.lean` (`TierR.checkPDq_sound`).
Soundness of the executable rational checker. -/
theorem checkPDq_sound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (h : checkPDq M = true) : IsPDq (M.map (Rat.cast : ℚ → ℝ)) := by sorry

/-- From `lean/R5.lean` (`R5.PsiArch_not_convex`).
The requested convexity input is false, already on `[0,0.4]`. -/
theorem PsiArch_not_convex :
    ¬ ConvexOn ℝ (Set.Icc (0 : ℝ) (2 / 5)) PsiArch := by sorry

/-- From `lean/R5.lean` (`R5.coverage_prime_free`).
R5-3, as requested, is inconsistent: no positive mesh and margin can cover
*every* grid satisfying `0 ≤ t`, because the admissible singleton grid `{0}`
has zero diagonal. -/
theorem coverage_prime_free :
    ¬ ∃ δ μ : ℝ, CoveragePrimeFree δ μ := by sorry

/-- From `lean/R5Prime.lean` (`R5.gershgorin_margin`).
The standard finite-dimensional Gershgorin/diagonal-dominance Rayleigh floor.
No sign assumption on `μ` is needed for this purely algebraic inequality. -/
theorem gershgorin_margin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (μ : ℝ)
    (hrow : ∀ i, μ + ∑ j with j ≠ i, |M i j| ≤ M i i) :
    ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ quadForm M x := by sorry

/-- From `lean/R5Prime.lean` (`R5.coverage_band`). Two-site coverage of the band. -/
theorem coverage_band :
    ∃ (δ μ : ℝ), 0 < δ ∧ 0 < μ ∧
      ∀ (t : Fin 2 → ℝ), StrictMono t →
        (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
        (∀ i j, i ≠ j → δ ≤ |t i - t j|) →
        IsPDq (fun i j => G (t i) (t j)) ∧
          μ ≤ lambdaMin (fun i j => G (t i) (t j)) := by sorry

/-- From `lean/R5Final.lean` (`R5.three_grid_last_row_gershgorin_zero`).
On the certified equally-spaced grid, the last Gershgorin row has
exactly zero diagonal-dominance margin. -/
lemma three_grid_last_row_gershgorin_zero :
    let t : Fin 3 → ℝ := ![1 / 5, 2 / 5, 3 / 5]
    G (t 2) (t 2) = G (t 2) (t 0) + G (t 2) (t 1) := by sorry

/-- From `lean/R5Final.lean` (`R5.coverage_band_final`, stated identically as
`R5.coverage_band_k`). The strongest final coverage rung obtained in Tier R:
the explicit three-site coarse-mesh theorem. -/
theorem coverage_band_final :
    ∃ (δ μ : ℝ), 0 < δ ∧ 0 < μ ∧
      ∀ (t : Fin 3 → ℝ), StrictMono t →
        (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
        (∀ i j, i ≠ j → δ ≤ |t i - t j|) →
        IsPDq (fun i j => G (t i) (t j)) ∧
          μ ≤ lambdaMin (fun i j => G (t i) (t j)) := by sorry

/-- From `lean/R5Final.lean` (`R5.frontier_covers_band_final`).
-- deviates from repo statement (notation only): the repo writes the kernel as
`V5_1.G`; here the existential binder `G : GramState` shadows the unqualified
kernel name, so the kernel is written `Challenge.G`. Same constant, same
statement. -/
theorem frontier_covers_band_final :
    ∀ (t : Fin 3 → ℝ), StrictMono t →
      (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
      (∀ i j, i ≠ j → (1 / 5 : ℝ) ≤ |t i - t j|) →
      ∃ G : GramState,
        G.dim = 3 ∧ HEq G.M (fun i j => Challenge.G (t i) (t j)) := by sorry

/-- From `lean/G3.lean` (`G3.G3_cert_neg`).
Positivity genuinely fails at `κ₁ = 0.789` for the true atoms. -/
theorem G3_cert_neg :
    ¬ IsPDq (U 0.789 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) := by sorry

/-- From `lean/G5.lean` (`G5.G5_c_prime`).
(c, prime form) For every prime `p ≠ 7`, `(log p)/√p < (log 7)/√7`. -/
theorem G5_c_prime (p : ℕ) (hp : p.Prime) (hp7 : p ≠ 7) :
    Real.log p / Real.sqrt p < Real.log 7 / Real.sqrt 7 := by sorry

end Challenge
