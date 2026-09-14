# Pending sync — paper PDFs

The PDFs in `papers/` are intentionally one or more revisions behind the
canonical versions, which are maintained off-repo until arXiv submission.
This ledger lists the wording changes pending in the canonical versions but
not yet reflected in the PDFs here. It will be deleted when the PDFs are
replaced with the submitted versions in a single final sync.

## Pending items

1. Acknowledgments in both papers extended with the comparator result —
   eighteen classical-axiom theorems certified against Challenge.lean,
   re-run in CI (Lean kernel and NanoDa replay); wording finalized off-repo.
   The compared set now includes the two G-tier theorems `G3_cert_neg` and
   `G5_c_prime` (see item 2 below).

## Errata (found in a 2026-09-14 audit of the PDFs against the repository)

These are statements in the current PDFs that the repository contradicts,
or that were true at the repository's current commit but were not true when
the PDFs were produced. The repository is the source of truth;
`STATEMENTS.md` and the README already state the facts below. They will be
corrected in the canonical versions before arXiv submission.

2. **Certified Positivity, §3.3 and §6.4** say the legacy `native_decide`
   path was retired in favour of the kernel-pure enclosures of `G1.lean`.
   This is no longer a contradiction at the current commit, but it was false
   when the PDFs (dated 2026-07-26) were produced, and it is false for the
   reason the PDFs give: at that time, nothing consumed `G1`'s enclosures
   (`V5_2.lean` imports `G1` but never references it), while `E2.lean`'s six
   `native_decide` uses remained load-bearing for `E5_cert_pos`,
   `G3_cert_pos`, `G3_cert_neg`, and `G6_cert_pos` via `E3_atom3` /
   `G2_atom5`. On 2026-09-14 those `E2.lean` lemmas (and `G4.lean`'s
   `G4_log11`) were re-proved with kernel-checkable Mercator-series bounds,
   so the `native_decide` path genuinely is retired now, but `G1.lean`
   remains unused by the rest of the development; the retirement was
   achieved by replacing `E2`/`G4`'s proofs directly, not by routing through
   `G1`. The canonical versions should attribute the retirement to the
   2026-09-14 `E2`/`G4` re-proof, not to `G1.lean`.
3. **Certified Positivity, Contributions** claims kernel-pure enclosures of
   `log p / √p` for `p ≤ 11`. This is no longer a contradiction at the
   current commit: `G4_log11` (the only enclosure of `log 11`) was, as of
   2026-09-14, re-proved kernel-pure (no `native_decide`), so a kernel-pure
   enclosure for `p ≤ 11` now genuinely exists. It was false when the PDFs
   were produced: `G1.lean` covers only `p ∈ {2, 3, 5, 7}`, and at that time
   the only enclosure of `log 11` was `G4_log11`, whose proof was the single
   `native_decide` use in `G4.lean`. As with item 2, the canonical versions
   should attribute this to the `E2`/`G4` re-proof, not to `G1.lean`, which
   remains unused.
4. **Certified Positivity, Appendix A** refers to "four batch directories"
   and to "the README's index". The modules are committed flat under
   `RequestProject/`, and the statement inventory is `STATEMENTS.md`.
5. **Certified Positivity** counts "137 machine-checked theorems". The
   repository has 253 `theorem`/`lemma` declarations across 75 modules
   (203 outside the R tier); the canonical version should quote a
   reproducible count.
6. **Certified Frontiers** omits the caveat printed in `TIER_R_FINAL.md`:
   the three-site coverage theorem's mesh condition forces the unique coarse
   grid `(1/5, 2/5, 3/5)`, so it is not a continuum of movable three-site
   configurations.
7. **Both PDFs**, in Table 1 and in the surrounding trust-table prose,
   describe three open `sorry` sites (`D4`, `F3`, `F3R`) attributed to
   unitary diagonalizability being absent from Mathlib. This is no longer
   true: as of 2026-09-14, all three are proved. In a second Aristotle
   (Harmonic) API job that day, the prover closed all three without changing
   any of their statements — `F3R.F3R_simple` (simplicity of the
   annihilator's roots) by a deeper use of the file's own Toeplitz shift
   identity, avoiding unitary diagonalization entirely; `F3.F3_roots` by
   transfer from the now-complete `F3R.F3R_roots` (`F3.lean` now imports
   `F3R`); and `D4.D4_caratheodory` (the full Carathéodory–Fejér theorem) via
   least-singular-block selection, `F3R`, window propagation of the null
   relation, and Vandermonde interpolation, with general-purpose lemmas
   factored into the new module `RequestProject/D4Aux.lean`. The development
   is now sorry-free (and remains `native_decide`-free) across all 76
   modules; the eighteen comparator theorems are unchanged. The canonical
   versions should update Table 1 and the trust-table prose to drop the
   three-sorry-site caveat and record the closure.

None of the above touches the eighteen comparator-certified theorems. Sixteen
of them are in the `V5` and `R` tiers and were already `native_decide`-free
transitively; the compared set now also includes the two G-tier theorems
`G3_cert_neg` and `G5_c_prime`, which became `native_decide`-free on
2026-09-14 and were restored to `Challenge.lean`, `Solution.lean` and
`comparator.json` accordingly.
