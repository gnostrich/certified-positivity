# Certified Positivity — Lean 4 development

[![consolidated build](https://github.com/gnostrich/certified-positivity/actions/workflows/build.yml/badge.svg)](https://github.com/gnostrich/certified-positivity/actions/workflows/build.yml)

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

`comparator.json` selects exactly **four** theorems, all from the Certified
Positivity part of the repository: `true_kernel_grid_margin`,
`true_kernel_grid_posdef` (the explicit positivity window of the genuine screw
kernel on the grid (0.2, 0.4, 0.6), with margin 0.005),
`true_kernel_first_prime_posdef` (positivity on (0.4, 0.9), past the first
prime) and `weil_triangle_prime_side` (the exact prime-side identity). In this
repository's CI, the `lake comparator` shipped with the pinned Lean toolchain
accepts `Solution.lean` against `Challenge.lean` for these four, with permitted
axioms exactly `propext`, `Quot.sound`, `Classical.choice`: statement match,
byte-identical definition graphs, axiom allowlist, and replay through Lean's
kernel and the NanoDa and con-ron binaries in that toolchain. Other results in
the repository (the horizon-threshold G-tier results, the Tier R frontier
work, and the rest of the development) are proved in `RequestProject/` but are
not part of this comparator check. Palomar's own verification of a submission
is separate from this CI check and uses checkers Palomar pins itself.

## Provenance (read first)

The `.lean` files are per-batch deliverables of an automated theorem prover
(Aristotle, by Harmonic). The author set the problems and made the
decisions; the specifications were developed in collaboration with an AI
assistant (Claude, Anthropic), and the statement-level audit of prover
output against those specifications was likewise AI-assisted. No human has
reviewed the proof terms line by line; the trust model is Lean's kernel,
with per-theorem axiom status recorded here and in the papers.
Axiom status of headline theorems:
`propext`, `Classical.choice`, `Quot.sound`. `native_decide` was originally
used in two files, both in numeric bound lemmas: `E2.lean` (six uses,
`E2_log3`/`E2_log5`/`E2_log7`) and `G4.lean` (one use, `G4_log11`); `G5`/`G6`
inherited it transitively via `G4`→`E2`. On 2026-09-14 those four lemmas were
re-proved by the Aristotle prover using Mathlib's
`Real.abs_log_sub_add_sum_range_le` Mercator-series tail bound together with
`Real.log_two_gt_d9`/`Real.log_two_lt_d9`, with all arithmetic discharged by
`norm_num`/`linarith` — kernel-checkable, with no `native_decide` and no
`Lean.ofReduceBool`/`Lean.trustCompiler` axioms. The change was verified by a
full rebuild, `#print axioms` on the affected theorems, and comparator replay
(Lean-kernel and NanoDa) against the updated `Challenge.lean`/`comparator.json`.
The development is now `native_decide`-free everywhere; `G1.lean` — which was
always `native_decide`-free — only mentions `native_decide` in its module
docstring, describing what it avoids. As a consequence, `G3_cert_neg` and
`G5_c_prime` now depend only on `propext`, `Classical.choice`, `Quot.sound`
(they are not part of the current comparator selection; see above).
The three previously documented `sorry` sites (`D4.lean`, `F3.lean`,
`F3R.lean`), whose shared cause was unitary diagonalizability being absent
from Mathlib, were closed on 2026-09-14 by the Aristotle prover in a second
API job, without changing any of the three statements: `F3R.F3R_simple`
(simplicity of the annihilator's roots) by a deeper use of the file's own
Toeplitz shift identity, avoiding unitary diagonalization entirely;
`F3.F3_roots` by transfer from the now-complete `F3R.F3R_roots` (`F3.lean`
now imports `F3R`); and `D4.D4_caratheodory` (the full Carathéodory–Fejér
theorem) via least-singular-block selection, `F3R`, window propagation of the
null relation, and Vandermonde interpolation, with general-purpose lemmas
factored into the new module `RequestProject/D4Aux.lean`. The development is
now sorry-free (and, as above, `native_decide`-free) across all 76 modules,
with every declaration depending only on `propext`, `Classical.choice` and
`Quot.sound`; the change was verified by a full rebuild, `#print axioms` on
the newly closed theorems, and comparator replay (Lean-kernel and NanoDa)
against `Challenge.lean`/`comparator.json`. The comparator theorems were
unchanged by this. The workflow included
pre-registered hypotheses; the prover refuted two of them
(`PsiArch_not_convex` in `R5.lean`; the newest-prime-binds refutation in
`G3.lean`), and both refutations are reported in the papers as results. The consolidated all-files `lake build` has now been independently
re-run outside the prover's environment: on 2026-07-26, in a Claude Code
cloud session (session link in the trailer of the commit introducing this
sentence), all 75 modules then present were built with Lean 4 `v4.28.0` /
Mathlib `v4.28.0` (modules placed under `RequestProject/` per the lakefile
globs) — zero errors, exactly the three disclosed `sorry` warnings (`D4`,
`F3`, `F3R`), and `#print axioms` on the headline theorems matching the axiom
disclosures above; at that time, `G5_c_prime` additionally reported
`Lean.ofReduceBool` and `Lean.trustCompiler` (the `native_decide` axioms), as
disclosed then. That no longer holds: since the 2026-09-14 re-proof of the
`E2`/`G4` bound lemmas described above, `G5_c_prime` (and `G3_cert_neg`) are
on the 3-axiom baseline like everything else. The three disclosed `sorry`
warnings from that 2026-07-26 build no longer hold either: as of 2026-09-14
(see above) the consolidated build emits no `sorry` warnings at all. The
per-batch compilation reports remain the original provenance record.
Scrutiny welcome — issues/PRs open.

## Layout

- `RequestProject/` — the development (76 files): D/E/F/G/K/T/GW/V5 = paper 1
  tiers; `R_*`, `R5*` = paper 2 (frontier object, coverage); `D4Aux.lean` is
  the general-purpose supporting module for `D4.D4_caratheodory` (rank of
  principal submatrices, Vandermonde-atom rank bound, null-vector window
  propagation, and Vandermonde interpolation).
- `papers/` — the two preprint PDFs.
- `STATEMENTS.md` — verbatim formal statements of the headline results.
- `Challenge.lean` — the headline statements as one Mathlib-only sorried file.
- `TIER_R_FINAL.md` — closing ledger of the frontier (R) tier.

Key entry points: `V5_1.lean` (the kernel), `V5_5.lean` (true-kernel window,
margin ≥ 0.005), `R_A2/R_A3_A4.lean` (GramState / expand / honest halt),
`R5Final.lean` (coverage_band_final; the Gershgorin-exactly-zero discovery).

## Toolchain and build status

`lean-toolchain` pins Lean 4 `v4.35.0`; `lakefile.toml` /
`lake-manifest.json` pin Mathlib `v4.35.0` and its transitive dependencies.
The prover batches compiled against Lean and Mathlib `v4.28.0`; the move to
`v4.35.0` (Palomar's minimum is `v4.35.0-rc2`) required proof-script repairs
in 29 files, recorded in `formalization.yaml` under `automation`. The modules are
committed under `RequestProject/` and import each other under the
`RequestProject.*` namespace (the prover project's name, and the lakefile's
`lean_lib` glob target), so `lake build` builds them directly with no
placement step. This consolidated build has been reproduced independently;
see the provenance note above.

## Palomar submission

`comparator.json`, [`Challenge.lean`](Challenge.lean),
[`Solution.lean`](Solution.lean), and `formalization.yaml` together form the
Palomar submission surface for this repository. The compared set is the four
theorems listed in `comparator.json` (named above), each checked against
`propext`, `Quot.sound`, and `Classical.choice` only. No other result in the
repository is part of the submission.

## License

Apache 2.0 — see [LICENSE](LICENSE).

Author: Rohan Badade — rohan.badade@outlook.com
