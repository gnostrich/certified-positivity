# Certified Positivity — Lean 4 development

Machine-checked positivity results for truncated Weil-type quadratic forms,
and a self-expanding positive-definiteness certificate ("certified frontier")
with a verified coverage theorem. Two preprints in `papers/`:

1. **Certified Positivity** — exact certified thresholds and positivity
   windows where the literature has floating-point numerics; includes what we
   believe is the first explicit machine-checked positivity window of the
   genuine zeta screw kernel (the literature's result is existential).
2. **Certified Frontiers** — a verified generator that grows a
   positive-definiteness certificate one site at a time: every step a theorem,
   honest halt (explicit counterexample), certifier = instrument.

## Exact claims

Prose is not the claim — [STATEMENTS.md](STATEMENTS.md) lists the verbatim
formal statements of every headline result, definitions first, plus an
explicit list of what is not claimed. Read that file to evaluate this
repository. [`Challenge.lean`](Challenge.lean) — the same claims as a single
Mathlib-only sorried file, for mechanical comparison against the repo.

## Provenance (read first)

The `.lean` files are per-batch deliverables of an automated theorem prover
(Aristotle, by Harmonic). The author set the problems and made the
decisions; the specifications were developed in collaboration with an AI
assistant (Claude, Anthropic), and the statement-level audit of prover
output against those specifications was likewise AI-assisted. No human has
reviewed the proof terms line by line; the trust model is Lean's kernel,
with per-theorem axiom status recorded here and in the papers.
Axiom status of headline theorems:
`propext`, `Classical.choice`, `Quot.sound`. `native_decide` appears in two
files, both in numeric bound lemmas: `E2.lean` (six uses) and `G4.lean`
(one). `G5`/`G6` import `G4` and therefore inherit its single
`native_decide` use (and, since `G4` imports `E2`, `E2`'s uses as well),
while the V5 and R tiers — all true-kernel certificates — are
`native_decide`-free, including transitively. `G1.lean` documents its
avoidance explicitly.
Three documented `sorry` sites (`D4.lean`, `F3.lean`, `F3R.lean`), one shared
cause (unitary diagonalizability, absent from Mathlib). The workflow included
pre-registered hypotheses; the prover refuted two of them
(`PsiArch_not_convex` in `R5.lean`; the newest-prime-binds refutation in
`G3.lean`), and both refutations are reported in the papers as results. A consolidated all-files `lake build` has not been independently
re-run outside the prover's environment; the per-batch compilation reports are
the primary evidence. Scrutiny welcome — issues/PRs open.

## Layout

- `lean/` — the development (75 files): D/E/F/G/K/T/GW/V5 = paper 1 tiers;
  `R_*`, `R5*` = paper 2 (frontier object, coverage).
- `papers/` — the two preprint PDFs.
- `STATEMENTS.md` — verbatim formal statements of the headline results.
- `Challenge.lean` — the headline statements as one Mathlib-only sorried file.
- `TIER_R_FINAL.md` — closing ledger of the frontier (R) tier.

Key entry points: `V5_1.lean` (the kernel), `V5_5.lean` (true-kernel window,
margin ≥ 0.005), `R_A2/R_A3_A4.lean` (GramState / expand / honest halt),
`R5Final.lean` (coverage_band_final; the Gershgorin-exactly-zero discovery).

## Toolchain and build status

`lean-toolchain` pins Lean 4 `v4.28.0`; `lakefile.toml` /
`lake-manifest.json` pin Mathlib `v4.28.0` and its transitive dependencies —
the environment the prover batches compiled against. The files in `lean/`
import each other under the `RequestProject.*` namespace (the prover
project's name); they are archived here as flat per-batch modules rather
than wired into a single lake target. Reproducing a consolidated build
(placing the modules under `RequestProject/` and running `lake build`) is
stated follow-up work; see the provenance note above.

## License

Apache 2.0 — see [LICENSE](LICENSE).

Author: Rohan Badade — rohan.badade@outlook.com
