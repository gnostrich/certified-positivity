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

Comparator ([leanprover/comparator](https://github.com/leanprover/comparator),
pinned) accepts this repository against `Challenge.lean` for all 18 headline
theorems whose permitted axioms are exactly `propext`, `Quot.sound`,
`Classical.choice` — statement match, byte-identical definition graphs, axiom
allowlist, and both Lean-kernel replay and NanoDa replay all pass (config
`comparator.json`, bridge `Solution.lean`, and pins in-repo; re-run in CI).
The set includes the two G-tier statements `G3_cert_neg` and `G5_c_prime`,
whose numeric bound dependencies were re-proved `native_decide`-free on
2026-09-14 (see Provenance below).

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
and have been restored to the comparator surface (see above).
Three documented `sorry` sites (`D4.lean`, `F3.lean`, `F3R.lean`), one shared
cause (unitary diagonalizability, absent from Mathlib). The workflow included
pre-registered hypotheses; the prover refuted two of them
(`PsiArch_not_convex` in `R5.lean`; the newest-prime-binds refutation in
`G3.lean`), and both refutations are reported in the papers as results. The consolidated all-files `lake build` has now been independently
re-run outside the prover's environment: on 2026-07-26, in a Claude Code
cloud session (session link in the trailer of the commit introducing this
sentence), all 75 modules were built with Lean 4 `v4.28.0` / Mathlib
`v4.28.0` (modules placed under `RequestProject/` per the lakefile globs) —
zero errors, exactly the three disclosed `sorry` warnings (`D4`, `F3`,
`F3R`), and `#print axioms` on the headline theorems matching the axiom
disclosures above; at that time, `G5_c_prime` additionally reported
`Lean.ofReduceBool` and `Lean.trustCompiler` (the `native_decide` axioms), as
disclosed then. That no longer holds: since the 2026-09-14 re-proof of the
`E2`/`G4` bound lemmas described above, `G5_c_prime` (and `G3_cert_neg`) are
on the 3-axiom baseline like everything else. The
per-batch compilation reports remain the original provenance record.
Scrutiny welcome — issues/PRs open.

## Layout

- `RequestProject/` — the development (75 files): D/E/F/G/K/T/GW/V5 = paper 1
  tiers; `R_*`, `R5*` = paper 2 (frontier object, coverage).
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
the environment the prover batches compiled against. The modules are
committed under `RequestProject/` and import each other under the
`RequestProject.*` namespace (the prover project's name, and the lakefile's
`lean_lib` glob target), so `lake build` builds them directly with no
placement step. This consolidated build has been reproduced independently;
see the provenance note above.

## Palomar submission

`comparator.json`, [`Challenge.lean`](Challenge.lean),
[`Solution.lean`](Solution.lean), and `formalization.yaml` together form the
Palomar submission surface for this repository. The compared set is the 18
classical-axiom theorems listed in `comparator.json`, each checked against
`propext`, `Quot.sound`, and `Classical.choice` only.

## License

Apache 2.0 — see [LICENSE](LICENSE).

Author: Rohan Badade — rohan.badade@outlook.com
