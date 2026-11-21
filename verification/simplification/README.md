# Simplification verification

The [repository-wide line reduction](broad-line-reduction.md) gives the comparison against the merge of PR #4, the source checks and the remaining proof dependencies. Earlier changes are documented in the [all-character row proof](row-proof.md) and the [module consolidation and pruning results](fold-and-prune.md).

This branch starts with the [Proof Atlas source release](https://riemann.fairway3games.com/simplification)
derived from [`40e56bab`](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).
The release contains 138,819 Lean modules. The fork also carries its existing `src/Challenge.lean`
for Comparator and the release's `CheckMain.lean` for checking the five theorem types and axioms
after a full build.

The branch applies the [upstream issue #3 correction](https://github.com/leanprover-community/riemann-hypothesis/issues/3)
to remove `plugAll` and its sole explicit caller `everyE₂`. The five-declaration `EveryCharacter`
chain is retained, including `every_character_of_green_v_win`.

The [ranked reduction analysis](reduction-priorities.md) measures further cuts against the reconciled fork and records the Lean pilot checks.

The receipts below apply to the Atlas archive before those two declarations were removed.

- [Release verification](release-verification.json) records the archive digest, source reduction,
  five entry points, and targeted Lean checks.
- [Issue #3 module checks](issue3-lean-check.json) records builds for the Hecke convolution,
  cusp integration, and tableau modules and their dependencies.
- [Split torus check](issue3-split-torus.json) records the `GrpObj` and `MonObj` instance checks.

The complete build and transitive axiom audit are pending. The upstream mirror check compares
the original submission byte for byte. This fork runs the Mathlib-only `Challenge` check.
