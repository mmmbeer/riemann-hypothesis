# The all-character proof from the Galois row

`UpperTheory.FinalTheorems.everyCharacter_of_row` proves zero-freeness for every Dirichlet character from the original `Row0b` hypothesis. The [conditional theorem](../../src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacterOfRow.lean) now imports the window and theta arguments. [MainConclusion](../../src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean) supplies the unconditional Galois row. A caller that already has the row can import the conditional theorem without importing the proof that constructs a row.

## Reusing principalisation in the all-character proof

On fork main at `d5566a2ca4df739b4e8793012a2910491dc1646e`, cutting both imports of `EveryCharacterOfRow` disconnects 8,176,545 lines from `Main`. The [earlier measurement](broad-line-reduction.md) counted 8,241,158 lines before the unused declarations and expanded expressions were reduced.

The theta argument already needs principalisation for arithmetic Hilbert–Samuel. The same input proves arithmetic intersection calculus through `GlobalTheory.MixHt.arCalc_of_principalisation`. The published cycle-height theorem takes that calculus as its only premise. Its height-projection result and the existing `GlobalTheory.ChernDegree.chernDegreeComplex` give arithmetic degree. This removes the separate direct-height and Chern-degree constructions. The local-global argument also reuses the Gelfand–Kazhdan duality result already supplied to the automorphy proof. [Revised proof](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean)

The old `FockModels.EveryCharacterE` also brought the Hilbert–Samuel and bigness estimates and a rationality lemma into scope. The revised module imports `MoriwakiBigTheorem.Outright` for the Hilbert–Samuel and bigness estimates and `RowRatWOfRowTest` for the rationality step in the family construction. The older construction itself takes `LocalLanglandsGL` and yields a value of `Nonempty (Hyps …)`. The active theta theorem uses `RecTExists` and `Nonempty (HypsAlt …)`. Substituting the older construction would require a proof connecting those interfaces.

| Measure | Fork main | Revised | Reduction |
| --- | ---: | ---: | ---: |
| Tracked Lean files | 78,358 | 78,242 | 116 |
| Tracked Lean lines | 15,838,761 | 15,818,278 | 20,483 |
| Lines reachable from Main only through the row imports | 8,176,545 | 8,156,062 | 20,483 |
| Project modules reachable from the conditional row theorem | 72,303 | 72,187 | 116 |

The 116 retired modules contain 20,488 lines. The edited module gains five lines for direct imports and proof terms. Counts use newline-terminated lines and exclude Lake packages. The original v0.2 compiled dependency graph has four references from retained declarations into the retired modules. All four came from the three arithmetic helpers rewritten here. The row theorem, window proof, five public endpoints and Comparator challenge retain their source text. [Original dependency data](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2)

Lean 4.33.1 checks the new source terms against the named propositions and theorem signatures recovered from the upstream module archives. The check reads the helpers in source order. It also rejects the wrong Galois projection. The standalone Mathlib challenge and this interface check cover different parts of the submission. A clean build of `Main`, its transitive axiom reports and a Comparator run are still required for end-to-end verification. [Interface check](check-row-wiring.py) · [Signatures and archive digests](row-interface.json)

The [theta covolume follow-up](theta-covolume.md) removes another 89,159 Lean lines from this route.

## What changed

The [window proof](../../src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean) takes its local representation theory, automorphy and cohomology from the same literature input used by theta matching. It supplies the complex multiplication fields separately. The two automorphy records have similarly named Galois fields with different types. The window takes the row from `N.aut.car`. The field `N.aut.gal` proves the paired representation statement.

The [shared input module](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RowLiteratureInputs.lean) contains the common declarations. The local Langlands existence proof uses the witness supplied in the input record. The crystalline-character proof uses its three substantive hypotheses directly.

Three named propositions had two proofs in the combined development. The row argument now uses the proof already present elsewhere in the final result. Each pair has the same named proposition as its complete compiled type.

| Proposition | Retired proof | Retained proof |
| --- | --- | --- |
| Jacquet–Shalika rigidity | `GlobalTheory.JSW.jacquetShalikaRigidity_holds` | `PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity` |
| Formal algebraisation | `PositivityTheory.FormalThickening.formalAlgebraisation` | `GlobalTheory.formalAlgebraisation` |
| Abelian de Rham theory | `PositivityTheory.DualRT.abelianDeRham` | `GlobalTheory.abelianDeRham` |

## Measured source changes

The baseline is the merge of PR #3, `969dda0e440b66ac5ef73e998713e21ac5d12ae4`. Import counts include the target and its transitive project imports. They exclude Mathlib and the toolchain. Repository totals count all tracked `.lean` paths and their newline-terminated lines.

| Measurement | Before | After |
| --- | ---: | ---: |
| Standalone window proof, project modules | 71,167 | 39,568 |
| Smallest public module providing the conditional row theorem | 78,618 | 72,303 |
| Project modules reached by Main | 78,623 | 78,342 |
| Tracked Lean files | 78,632 | 78,351 |
| Tracked Lean lines | 16,072,826 | 15,995,136 |

The 283 retired modules contain 77,415 lines. Two new modules house the shared inputs and the conditional theorem. Net savings are 281 files and 77,690 lines. Earlier estimates identified 8,215,997 declaration lines below the row implication in the original kernel dependency analysis. The revised proof still uses theta matching, covolume estimates and the character window. The net line count above is the realized saving.

## Verification

The revised import graph is acyclic. All surviving proof modules are reachable from Main. The original kernel graph identifies the three replaced proof calls at the boundary of the retired code. The two tactic macros defined in the retired modules have no surviving caller in their former import scope. The public files `Main.lean`, `Statements.lean`, `Challenge.lean` and `CheckMain.lean` match the baseline byte for byte.

Lean 4.33.1 checked the new row and window proof bodies, and five revised helper proofs, against signatures read from 29 digest-verified upstream module archives. The comparison covered 150 compiled constants, including the 91 fields of eight structures. The two row predicates unfold to the same kernel expression. All three pairs of replacement theorems have identical compiled types. A negative test changes the Galois-field selection and Lean rejects it.

To repeat the small check from the repository root with the pinned toolchain, run:

```sh
python3 verification/simplification/check-row-wiring.py --lean "$(lean --print-prefix)/bin/lean"
```

This test uses a temporary Lean file with the imported theorems as premises and the named propositions abstract. It checks the new composition. It does not compile the proofs of those premises. [Recorded interfaces and archive hashes](row-interface.json) · [Upstream cache manifest](https://rh-cache.taucetiproject.org/bootstrap/e50d09817ad81469f737e8f637561e6ccf86c670/modules.jsonl.gz) · [Kernel dependency dataset](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2)

A clean build of the reduced Main, the five endpoint axiom reports and Comparator verification remain pending. On a host sized for the full project, the source checks are:

```sh
export LEAN_ABORT_ON_PANIC=1 LAKE_ARTIFACT_CACHE=false
lake exe mathlib/cache get
lake build Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacterOfRow Main
lake env lean CheckMain.lean
```

The upstream reader’s map documents where windowed zero-freeness and the connected-family construction enter the result. Upstream PRs 12 and 38 address ordinary RH at conductor one. The three Dirichlet endpoints still require the all-character argument. [Upstream proof map](https://github.com/leanprover-community/riemann-hypothesis/issues/5) · [Conductor-one proposal](https://github.com/leanprover-community/riemann-hypothesis/pull/12) · [Principal-character implementation](https://github.com/leanprover-community/riemann-hypothesis/pull/38)
