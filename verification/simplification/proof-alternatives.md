# Alternative proofs in fork PR #11

The baseline is [the merge of PR #10](https://github.com/mmmbeer/riemann-hypothesis/tree/f6fda7efd4bbe81872b27b11e0de17161817a7f8). The five public theorem statements, the challenge, the Comparator configuration and the pinned Lean and Mathlib versions are unchanged.

## Changes by proof

| Proof | Net Lean lines saved | What the caller now uses |
| --- | ---: | --- |
| Haar measure | 7,532 | The existing covariance formula in the covolume proof. The short named wrapper remains available to callers. |
| Unramified doubling | 4,407 | The inert-place doubling theorem with the same compiled type. |
| Galois row | 3,924 | Existing proofs of étale excision and Kummer surjectivity, and a conditional entry point for a supplied odd-rank seed. |
| Cohomological window | 1,019 | The boundedness field of the cuspidal spectrum theorem (951), the existing Clozel cohomology theorem (18), and one local compatibility argument for both callers (50). |
| Tower and covolume | 4,279 | The caller passes its existing `Top.Given` witness to the tower proof. Five arithmetic imports remain necessary for other proofs. |
| Rank-share and layer-cake estimates | 41 | Charges each slope once (21) and uses Mathlib's integral of an indicator function (20). |
| Analytic zero-free criterion | 14 | Replaces a local power-series argument by Mathlib's Cauchy derivative estimate on a closed disk. |
| Common-scale identity | −7 | Generalizes the subgroup sum to arbitrary top weights and evaluation points. A specialization serves the active proof. |
| Standalone integrated rank-loss proof | −132 | Adds a Lean proof of the finite-slope estimate and its comparison with the logarithmic bound. It lives under verification and is outside Main. |

## Measured footprint

| Measure | After #10 | After #11 | Reduction |
| --- | ---: | ---: | ---: |
| Tracked Lean files | 77,787 | 77,691 | 96 |
| Tracked Lean lines | 15,729,119 | 15,708,042 | 21,077 |
| Uncompressed Lean bytes | 896,168,922 | 895,007,191 | 1,161,731 |
| Lean lines reachable from Main | 15,727,619 | 15,706,410 | 21,209 |
| Lines exclusive to the two row imports | 8,066,903 | 8,051,572 | 15,331 |
| Lines exclusive to the theta import | 5,770,882 | 5,759,070 | 11,812 |

The standalone conditional Galois module imports 29,245 modules and 6,265,278 lines including itself. The unconditional module imports 36,453 modules and 7,472,540 lines. Supplying the seed avoids 7,208 modules and 1,207,262 lines for that caller. Both measurements use the final tree. The main theorem still uses the unconditional module.

Counts cover tracked Lean source. Main excludes the independent challenge and utilities outside src. For each exclusive count, remove the named import edge or edges and recount the modules still reachable from Main. The theta count is part of the row count. Exclusive counts can change when two branches begin or stop sharing an import.

## How far the larger replacements go

**Galois seed.** The new `UpperTheory.Gal.Int.galoisLocalGlobal_of_seed` produces `Row0 recT` from `SeedFinOdd` with the existing theta lift as the default. Its callers can also supply a lift. The unconditional row still constructs the seed from geometry. The seed requires one semisimple representation satisfying the local conditions over an arbitrary finite test set, including the crystalline jumps and Frobenius polynomial above ℓ. The two literature fields built from `UpperTheory.One.M.Row` already assume the row they would have to prove. Harris, Lan, Taylor and Thorne give a construction for regular algebraic cuspidal representations. Applying it here also requires the fork's normalizations, its hypotheses on the input representation and its compatibility statements at ℓ. [Harris, Lan, Taylor and Thorne](https://doi.org/10.1186/s40687-016-0078-5) · [Barnet-Lamb, Gee, Geraghty and Taylor](https://arxiv.org/abs/1105.2242) · [Caraiani](https://arxiv.org/abs/1202.4683)

**Window at exponent 401.** The existing chain already uses the shorter `ThmBab` assembly. To remove the larger branch, the proof still needs `ThmHV` and its counting estimates, or independent inputs for `JointWin 401` and `ThmBc 401`. The alternate rank-four symplectic theorem asks for a stronger automorphy witness, including growth and compatibility data. The current row alone does not supply it. [Current assembly](../../src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/HVCore.lean) · [Window target](../../src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean)

**Theta and covolume.** The new tower proof avoids reconstructing the same geometric data. The remaining family estimate has the quantifier order “there exists one constant, for all eligible towers.” A pointwise volume formula still needs the positivity and Hodge comparison for this family. The caller discards two outputs, `ThmB` and `T2`, but the tower proof uses both to derive the mean-slope bound that the caller retains. The Rallis formula addresses a theta inner product. Translating it into the required uniform bound is a further mathematical step. [Gan, Qiu and Takeda](https://arxiv.org/abs/1207.4709) · [Moriwaki](https://arxiv.org/abs/math/0612269) · [Tower proof](../../src/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GoodTowerVolumeTheoremAlt.lean)

**Common scale.** In §3 of the preprint the comparison weight at top `t` is `v t = a t / x`, giving the same argument `x` for all tops. The new `sum_weighted_tops` proves the subgroup average for arbitrary top weights and evaluation points. Setting all evaluation points to `x` gives the common-scale identity. The active proof specializes it to the former constant weight and the original evaluation points. The remaining comparison needs bounds on the change of weights for thick and thin labels and on the weighted character coefficients. The existing call to `ch_core` still uses the established error bounds. [Common-scale comparison, §3](https://hexagonmath.org/pdf/2611.00828v1) · [Character-balance proof](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean)

**Integrated slope loss.** The active rank-share proof now charges each slope once. The active layer-cake proof uses the indicator integral to count clipped slope deficits. The standalone Lean alternative proves the integrated rank-loss inequality, its finite-slope transfer under the frame estimate (2.2), and the comparison with the logarithmic allowance. For nonnegative height and excess parameters H and U it obtains the rational term H U / (H + U), including the degenerate cases. The existing arithmetic argument still substitutes `u / (u + τ)` for the discarded fraction. Passing the actual discarded fractions from `thmF_place` into the family estimate remains open. [Standalone Lean proof](IntegratedRankLoss.lean) · [Active slope proof](../../src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean) · [Integrated estimate, §2](https://hexagonmath.org/pdf/2611.00828v1)

**Oscillation and real poles.** The Kaczorowski–Pintz route needs a quantitative frequency of sign changes to force an oscillation in the specified window. A sequence of sign changes by itself gives no such location. Exceptionally placed real poles require a residue correction across the weighted family. The reviewed Lean sources do not supply the required oscillation estimate for this family. The existing analytic endpoint still proves the criterion used by the fork. [Kaczorowski and Pintz](https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1986.Kaczorowski_1.pdf) · [Weighted correction, §5](https://hexagonmath.org/pdf/2611.00828v1)

## Verification

- Recomputed all tracked Lean files, bytes and newline counts. Checked every project import resolves and the graph is acyclic. Among modules under `src`, only the independent `Challenge` lies outside the closure of `Main`.
- Lean 4.33.1 compared the archived compiled theorem types for the Haar, doubling, étale excision and Kummer substitutions. Archived declaration dependencies and editor references were checked for downstream uses that would lose their imports.
- For the window substitutions, Lean checked the selected spectrum result and the codomain of the Clozel theorem. The shared local-compatibility proof previously occurred twice with identical bodies and used only the finiteness field of each caller's hypothesis.
- Lean checked the two edited tower proof bodies against 17 archived signatures, including the fields of both records and the original boundary type.
- For the conditional Galois row, the old archived proof term is the new helper body with the seed from geometry substituted. Lean checked both new compositions and the default theta lift against the seven archived signatures.
- Lean checked the new rank-share, layer-cake and Cauchy proof bodies with their existing statements. For the Cauchy and integrated rank-loss results, the reviewed axiom reports list only `propext`, `Classical.choice` and `Quot.sound`.
- The finite-slope file also has its own step in the hosted workflow. It can be run directly with `lake env lean verification/simplification/IntegratedRankLoss.lean`.
- Lean compiled the exact weighted-sum identity and the active fixed-weight specialization in a standalone fixture with the upstream summation formula as a premise.
- The fork's hosted checks compile the standalone challenge against Mathlib and typecheck the row and window assembly against recorded interfaces. The same workflow also checks the standalone integrated rank-loss file. [PR checks](https://github.com/mmmbeer/riemann-hypothesis/pull/11/checks)

A clean rebuild of `Main`, fresh axiom reports for all five public theorems and an independent Comparator run remain outstanding. Archived signatures and individual file checks cover the stated substitutions.

Run these from a clean checkout of the merge to reproduce the measurements and run the fork checks.

```sh
python3 verification/simplification/measure-import-footprint.py
python3 verification/simplification/check-row-wiring.py
git diff --numstat f6fda7efd4bbe81872b27b11e0de17161817a7f8 HEAD -- '*.lean'
lake build +Challenge:olean
```
