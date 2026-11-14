module

public import Mathlib

@[expose] public section

/-!
# Challenge.lean — Mathlib-only statements of the headline theorems

This file states, with `sorry` as every proof, the three headline theorems of
the Certified Positivity part of this repository: the explicit positivity
window for the genuine screw kernel (with its margin) and its persistence past
the first prime atom. It imports **only Mathlib** — no repository modules — and inlines
every custom definition the statements need, copied verbatim from the named
source files (see the `-- from <file>` markers). Its purpose is mechanical:
the statements here can be compared against the repository modules (e.g. with
a statement comparator) to check that the sorry-free proofs in `RequestProject/` prove
exactly these claims and not something subtly different.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (as pinned by
`lean-toolchain` / `lakefile.toml` / `lake-manifest.json` at the repo root).
Checked: this file elaborates with no errors under that toolchain
(`lake env lean Challenge.lean`), emitting exactly the 3 expected
`declaration uses 'sorry'` warnings.

Because all definitions live here in the single namespace `Challenge`, the
namespace prefixes of the originals (`Horizon.`, `V5_1.`, `V5_5.`, `V5_6.`)
are necessarily dropped; this is the one systematic transformation
applied to every inlined definition and statement. There are no other
deviations.

This file makes **no axiom claim**: every proof below is `sorry`, so
`#print axioms` on this file is meaningless by design. Axiom status of the
real proofs is a property of the repository modules, not of this file. All
three statements below are proved in the repository on `propext`,
`Classical.choice`, `Quot.sound` only, and the whole development is
`native_decide`-free.
-/

open scoped BigOperators Matrix
open ArithmeticFunction

namespace Challenge

/-! ## Definitions — from `RequestProject/Horizon.lean` (namespace `Horizon`) -/

variable {n : ℕ}

/-- The quadratic form `xᵀ M x`. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `M` is positive definite (quadratic-form definition). -/
def IsPDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x

/-! ## Definitions — from `RequestProject/V5_1.lean` (namespace `V5_1`) -/

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

/-! ## Definitions — from `RequestProject/V5_5.lean` / `RequestProject/V5_6.lean`
(namespaces `V5_5`, `V5_6`) -/

/-- The genuine screw Gram matrix on the grid `(0.2,0.4,0.6)`. -/
noncomputable def M3 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  let t : Fin 3 → ℝ := ![0.2, 0.4, 0.6]
  G (t i) (t j)

noncomputable def M2 : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  let t : Fin 2 → ℝ := ![0.4, 0.9]
  G (t i) (t j)

/-! ## Headline theorems, stated with `sorry`
Sorry-free proofs live in the named repository modules. -/

/-- From `RequestProject/V5_5.lean` (`V5_5.true_kernel_grid_margin`). -/
theorem true_kernel_grid_margin (x : Fin 3 → ℝ) :
    (0.005 : ℝ) * ∑ i, x i ^ 2 ≤ quadForm M3 x := by sorry

/-- From `RequestProject/V5_5.lean` (`V5_5.true_kernel_grid_posdef`).
The true zeta screw kernel is positive definite on `(0.2,0.4,0.6)`. -/
theorem true_kernel_grid_posdef : IsPDq M3 := by sorry

/-- From `RequestProject/V5_6.lean` (`V5_6.true_kernel_first_prime_posdef`). -/
theorem true_kernel_first_prime_posdef : IsPDq M2 := by sorry

end Challenge
