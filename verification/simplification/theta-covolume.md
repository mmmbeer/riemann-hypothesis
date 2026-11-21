# Narrowing the theta proof's covolume imports

The all-character proof uses `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` to supply the covolume bound for theta matching. The construction needs several intermediate arithmetic estimates that older covolume proofs also imported. Replacing those indirect imports with the defining modules removes 455 source files and 89,159 net Lean lines from the fork. The active theta proof has the same body and hypotheses. [Baseline tree](https://github.com/mmmbeer/riemann-hypothesis/tree/dda1764a958d7fc38c7b0c6d4c8cee9264ed85bb)

## Which dependencies changed

- The current covolume argument imports its Chow hyperplane-section formula, nonvanishing result, toroidal charts and `deep_slim_use` directly. Its conclusion uses the current point conditions for all Dirichlet characters. The older `CovolX` proofs used an earlier row condition. The change removes the unused older entry points and retains the intermediate lemmas the current construction calls. [Theta argument](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean)
- The small-sections inequality uses one result from the geometric-degree module. The proof that a constant metric shift preserves geometric degree still follows by simplifying the definition of the Chern integral. It now needs one project import. [Geometric-degree lemma](../../src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsometricShiftOfIsometric.lean)
- The Moriwaki argument uses one metric identity from a file with 183 direct project imports. The existing proof applies the lift-graph result to the closed factor. One project import supplies both. Four related arithmetic modules now import the providers of their named applications. They retain all 81 theorem declarations. Downstream files import any other lemmas they previously obtained from those headers. [Metric identity](../../src/GroundTheory/HeightsAndTheta/Heights/LocalFiniteness/KeyFormulaVanishingCechMultInvariants.lean) · [Moriwaki estimates](../../src/Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/MoriwakiBigTheorem/Outright.lean)

## Size

| Measurement | PR #9 | This change |
| --- | ---: | ---: |
| Tracked Lean files | 78,242 | 77,787 |
| Tracked Lean lines | 15,818,278 | 15,729,119 |
| Project modules reachable from Main | 78,226 | 77,771 |
| Lean lines reachable from Main | 15,816,778 | 15,727,619 |
| Lines reachable only through the all-character row imports | 8,156,062 | 8,066,903 |
| Lines reachable only through the row's theta import | 5,860,041 | 5,770,882 |

For the last two rows, traverse the project imports from `Main`, remove the specified import edges from `EveryCharacterOfRow`, then traverse again. Count lines in the set difference. All 455 retired modules lie on the theta-only route. The files contain 87,895 newline characters. The edits to 18 surviving Lean files save another 1,264 lines. Counts exclude external packages.

The standalone targets also get smaller. Building the Chow hyperplane-section module now reaches 543 project modules, down from 28,577. The geometric-degree lemma reaches 280, down from 6,271. The metric identity reaches 96, down from 4,600. These targets share dependencies elsewhere in Main, so their individual savings overlap.

## Verification

The final project import graph is acyclic. Every project import resolves. Every source module except the independent Comparator challenge is reachable from Main. The row and window theorem files, the five public statements and proofs in `Main.lean`, the statement definitions, the challenge and `CheckMain.lean` match PR #9 byte for byte.

The original compiled dependency graph has 29 edges from 15 declarations in surviving files into the retired set. All 15 declarations had already been removed before PR #9. The original Lean source-reference indexes for the affected consumers also identify no surviving use of a retired declaration. These checks complement Lean compilation because archived dependencies describe the original submission. [Compiled dependency data](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2)

These commands build three edited modules from a clean checkout with the pinned toolchain and Mathlib.

```sh
lake exe mathlib/cache get
lake build \
  Development.WeilBound.CoreStatements.NefModelVolumes.TopCovolSlim2 \
  Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric \
  GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.KeyFormulaVanishingCechMultInvariants
```

A clean build of the revised `Main`, the five endpoint axiom reports and Comparator verification remain outstanding.
