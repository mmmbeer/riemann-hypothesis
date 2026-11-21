# Reducing lines after the row simplification

The baseline is the [merge of PR #4](https://github.com/mmmbeer/riemann-hypothesis/commit/0f8a0bca44c2fe3301ba4738dd7f399f56bedac5). It has 15,995,136 newline-terminated lines in 78,351 tracked Lean files. A reduction of 43% requires removing at least 6,877,909 lines and leaving at most 9,117,227.

The [follow-up on the all-character route](row-proof.md#reusing-principalisation-in-the-all-character-proof) measures a further 20,483-line reduction on the later fork main.

## Tracked source on the review branch

| Tracked Lean source | Merged main (PR #4) | Proposed (PR #5) | Reduction |
| --- | ---: | ---: | ---: |
| Lines | 15,995,136 | 15,838,095 | 157,041 (0.98%) |
| Files | 78,351 | 78,351 | 0 |

The proposal is 6,720,868 lines short of the 43% target. The five public theorem statements in `src/Main.lean`, their definitions in `src/Statements.lean`, the Comparator challenge and `CheckMain.lean` match the baseline byte for byte.

## Unused declarations

The first commit removes 20,292 declarations from 5,222 files across seven top-level source directories. The commands contain 113,296 lines. Removing the blank separators left at deletion boundaries saves another 20,748 lines. The resulting source tree is `e131bb0700adc847cfc3b0219065a07bddd57050`. [GitHub reconstruction](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44925707057)

The search matched entire command bodies from the original submission to the fork, including bodies moved by module consolidation. It screened ordinary theorems, lemmas, definitions and abbreviations. It preserved commands with attributes or an enclosing command, shared generated auxiliaries, and names that retained source could use through its imports. It followed dependencies recursively and checked explicit access to private names. Each manifest row names the declaration and gives its line range on the baseline.

An independent readback found that every selected command matches the original submission byte for byte. No selected range intersects a declaration used by the original five theorem proofs or a shared auxiliary used by those proofs. In the v0.2 project declaration graph, no edge enters the deletion set from outside it. These checks use the compiled dependencies of the original submission. Lean source can also depend on declarations during elaboration. [Dependency data and definitions](https://github.com/james-shore/rh-proof-dependencies/tree/v0.2)

The clean Lean 4.33.1 builds selected 26 directly edited modules and six downstream consumers. Together their project import closures contain 212 distinct modules. Of these, 114 lost a total of 781 declarations. All three builds passed. The independent Mathlib-only Challenge check also passed. [Downstream builds](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44926033584) · [Challenge check](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44925959292)

## Shorter source expressions

Lean's typeclass inference can supply many arguments written explicitly by the original generator. The accepted rewrites cover 29 modules and remove 22,997 lines beyond the unused-declaration pass. The checks compare elaborated theorem types and public binder names. They also compare elaborated values for definitions whose bodies changed. [Initial expression checks](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44927218537) · [Per-declaration checks](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44928318077) · [Edited declarations and source checksums](shorter-expressions.json)

| Example module | Before this rewrite | After this rewrite | Reduction |
| --- | ---: | ---: | ---: |
| [FixPiIff](../../src/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FixPiIff.lean) | 8,023 | 36 | 99.55% |
| [MapPowSub](../../src/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapPowSub.lean) | 266 | 17 | 93.61% |
| [QuantumMinorsCasimir](../../src/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/QuantumMinorsCasimir.lean) | 366 | 134 | 63.39% |
| [Qminor](../../src/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/Qminor.lean) | 384 | 152 | 60.42% |

Twenty-eight rewritten algebra modules built from the combined fork source on clean hosted runners. The largest individual rewrite, `FixPiIff.lean`, uses local-field notation already present in a downstream proof. Lean 4.33.1 compiled that entire 36-line module against digest-verified original project interfaces. It compared the type of `UpperTheory.Reformulated.B.Gr34.mem_UC`, its universe parameters and all binder names with the archived constant. Its axiom report lists `propext`, `Classical.choice` and `Quot.sound`. [Combined source builds for the other 28 modules](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44929307962) · [Archive checksum and compiler output](shorter-expressions.json)

## What would a 43% cut require?

For each row below, start from the fork's baseline import graph, remove every outgoing import of the named module, then traverse again from `Main`. Count the baseline lines of files that disappear from that traversal. This gives an optimistic ceiling for changing those imports in isolation. Any replacement proof can require some of the lost dependencies. The rows overlap.

| Module whose imports are omitted | Files lost from the traversal | Lines in those files |
| --- | ---: | ---: |
| CharacterBoxes.MainConclusion | 68,478 | 13,597,090 |
| CharacterBoxes.EveryCharacterOfRow | 40,877 | 8,241,158 |
| ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin | 28,798 | 5,918,963 |
| DenseThresholdCases.VwinOfRow | 6,397 | 1,153,769 |
| IntegralStructures.RowSrc | 6,032 | 986,301 |

The row theorem's existing proof builds the literature inputs from the Galois row, obtains the window estimate and invokes theta matching. Of the 8,241,158 lines isolated by its imports, a replacement would have to dispense with at least 6,877,909 to reach the target by this route alone. The original compiled duplicate-statement catalog lists only `allChi` and `UpperTheory.FinalTheorems.everyCharacter` for the unconditional `EveryCharacter` result. On the fork, the former calls the latter. The existing window and theta entry points have additional hypotheses. The upstream conductor-one specialization covers ordinary RH. The fork also states three results for Dirichlet characters. [Row proof](row-proof.md) · [Upstream conductor-one specialization](https://github.com/leanprover-community/riemann-hypothesis/pull/38)

The original duplicate-statement catalog has 69,708 groups. Removing the longer copies wherever possible would affect at most 606,437 lines in that source, before counting any replacement. The catalog measures the original submission, and several entries have already changed on the fork. [Duplicate-statement catalog](https://github.com/james-shore/rh-proof-dependencies/blob/v0.2/data/duplicates-statements.tsv.gz)

## Reproduce the deletion checks

Use Python 3.11 or newer, separate clean checkouts of the fork baseline and the original submission at `40e56bab`, and the `decls.csv.gz` and `decl_edges.csv.gz` files from [release v0.2](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2). From this revision run:

```sh
python3 verification/simplification/check-unused-declarations.py /path/to/baseline /path/to/original /path/to/data
python3 verification/simplification/replay-unused-declarations.py /path/to/baseline verification/simplification/unused-declarations.tsv.gz
```

The second command edits the baseline checkout. The source digest above applies immediately after replaying those deletions. The expression rewrites are a later change. A clean build of the reduced `Main`, its five transitive axiom checks and the Comparator run remain pending.
