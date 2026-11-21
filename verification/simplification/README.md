# Simplification of the five-theorem development

[Geometric Galois seed reduction and analytic estimates](galois-seed.md).

[PR #11 proof substitutions, source sizes and verification](proof-alternatives.md).

The proposed source tree is `6398a58acb44c4e1c67b7f16ca7b60d22050f307`. Compared with [upstream main at ab0b7522](https://github.com/leanprover-community/riemann-hypothesis/tree/ab0b7522a5ccc9b8530edf475af5088f8f6464aa), the only edit in `src/Main.lean` is its import of `Supplements.Kernels.MainTheorems` in place of `MainTheoremsAll`. All five theorem statements and their proof bodies match upstream. `Statements.lean`, the Mathlib-only `Challenge.lean`, the export targets, Comparator configuration, Lean toolchain and Lake manifest also match upstream byte for byte.

## Size

| Measurement | Upstream | Simplified tree for review | Reduction |
| --- | ---: | ---: | ---: |
| All tracked Lean files | 175,195 | 78,351 | 96,844 (55.28%) |
| All tracked Lean lines | 17,374,989 | 15,838,095 | 1,536,894 (8.85%) |
| Project modules imported transitively by `Main`, including `Main` | 175,187 | 78,342 | 96,845 (55.28%) |
| Lean lines in those modules | 17,374,215 | 15,837,261 | 1,536,954 (8.85%) |

Line counts count newline characters in Git blobs. The first two rows include the challenge and Lean verification utilities. The last two count project sources reached from `Main` and exclude Mathlib. The fork's three experiment branches add seven Lean scripts outside `src/`. Those scripts are excluded from the review tree. The project import graph is acyclic. Every module in `src/` except the independent challenge is reachable from `Main`.

## Changes and evidence

1. **Consolidate forwarding declarations and remove redundant imports.** The initial release moved 29,565 forwarding declarations to their providers and used a shared tactic for 1,022 others. After rewiring imports, 6,727 modules became unreachable. The pass removed 199,527 transitive import edges and 263 duplicate imports. It replayed dependency order before shortening each affected header. It also shared an averaging lemma across six callers. The release records separate Lean checks of the extracted callers, Mellin calculation and reflection argument. Lean compared 48 sampled forwarding declarations with their original public types. [Release measurements and check scope](release-verification.json)
2. **Apply the corrected all-character dependency chain.** Removed `plugAll` and its sole explicit caller `everyE₂`. All five declarations on the route to `EveryCharacter` remain, including `every_character_of_green_v_win`. The initial release checks include Hecke convolution, cusp integration, tableaux and the split-torus `GrpObj` and `MonObj` instances raised during review. [Issue #3 and correction](https://github.com/leanprover-community/riemann-hypothesis/issues/3) · [Module builds](issue3-lean-check.json) · [Instance checks](issue3-split-torus.json)
3. **Fold single-use modules and prune unused theorems.** Moved 60,194 same-directory helper modules into 15,856 importers with separate Lean sections for their original scopes. Removed 34,025 theorem commands after checking the original compiled dependencies and references from retained source. The net reduction in this pass was 361,720 lines. External users of a retired module path must import its destination. The fold manifest can be regenerated with the documented commands. [Fold and prune report](fold-and-prune.md)
4. **Share the inputs to the row and window proofs.** Factored the conditional `Row0b → EveryCharacter` argument out of the module that constructs an unconditional row. The window proof and theta matching now consume the same literature inputs. The row uses existing proofs of Jacquet–Shalika rigidity, formal algebraisation and the abelian de Rham theorem. The standalone window target went from 71,167 to 39,568 project modules. Across the repository this pass saved 281 files and 77,690 lines. [Row proof and interface checks](row-proof.md)
5. **Remove a second set of unused declarations and shorten generated expressions.** Removed 20,292 more declarations using the original compiled dependency graph and retained-source references, including references to commands moved by the module folds. The deletion manifest and its replay script reproduce this stage's source tree. Rewrote generated expressions in 29 modules using Lean notation and inference. `FixPiIff.lean` went from 8,023 lines to 36. The earlier `FreeModuleQuotient.lean` pilot went from 2,516 lines to 84. The final pass removed 157,041 lines, including 22,997 from expression rewrites. [Final pass and replay commands](broad-line-reduction.md) · [Pilot and measurements](reduction-priorities.md)

## Verification

The fold/prune stage built 28 targets from clean checkouts covering 104 project modules. The later deletion stage built 32 selected targets covering 212 project modules. A separate clean build covered 28 rewritten algebra modules. Lean checked the full rewritten `FixPiIff` module against original compiled interfaces and compared the theorem's type, universes and binder names. The row wiring test checked the chosen Galois projection and rejected the wrong one. These results apply to the revisions and targets identified in the reports. [Fold builds](fold-and-prune.md#verification) · [Row wiring](row-proof.md#verification) · [Deletion and expression builds](broad-line-reduction.md)

A full build of this reduced `Main`, the five transitive axiom checks and Comparator verification are pending. To check the assembled source, start from a clean checkout without project build artifacts. Fetch the pinned Mathlib cache before entering the offline build environment.

```sh
export LEAN_ABORT_ON_PANIC=1 LAKE_ARTIFACT_CACHE=false
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4
lake exe mathlib/cache get
lake build Main
lake env lean CheckMain.lean
```

Use the independent challenge checkout and export procedure in the [repository README](../../README.md#checking-it) for Comparator. The upstream manual mirror job compares against the original tarball byte for byte and will report differences on the derived tree. The immutable [original submission](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) and [initial simplified archive](https://riemann.fairway3games.com/simplification) identify the two starting points.
