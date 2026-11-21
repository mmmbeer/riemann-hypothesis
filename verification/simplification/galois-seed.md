# Simplifying the geometric Galois seed

The unconditional Galois row saves 79 project modules and 11,321 Lean lines by sharing the proof of an étale cohomology theorem. The row still constructs its odd-rank seed and takes no additional hypotheses. The baseline is [fork main after PR #11](https://github.com/mmmbeer/riemann-hypothesis/tree/61f068b4403dfb79cac30b547e8f3c4f21201aeb).

| Reachable from | Modules before | Modules after | Lines before | Lines after |
| --- | ---: | ---: | ---: | ---: |
| Main | 77,674 | 77,595 | 15,706,410 | 15,695,089 |
| Unconditional Galois row | 36,453 | 36,374 | 7,472,540 | 7,461,219 |
| Row given an odd-rank seed | 29,245 | 29,245 | 6,265,278 | 6,265,278 |

The remaining difference between the two row entry points is 7,129 modules and 1,195,941 lines. These counts include the entry module and exclude Mathlib. The standalone analytic estimates are outside the import closure of Main. Run `python3 verification/simplification/measure-import-footprint.py` to reproduce the counts.

## What changed in the seed

The former D2 construction assembled naturality, the cup-product ring laws and vanishing on a two-member cover from individual cochain lemmas. The Galois proof already had witnesses for those three facts. It used them in a second proof of the same result. The shared proof now uses those witnesses to establish the six inputs to `D2.goal_of`. The Künneth–Lefschetz caller supplies its own cohomology hypotheses to that result. The E6 caller imports the naturality theorem and the definition of its expected type directly. This removes the last use of the old construction. [Shared D2 proof](../../src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology/EtaleAxioms/A0.lean) · [Galois caller](../../src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/KunnethLefschetz/EtSideGoodHolds.lean) · [E6 caller](../../src/Development/AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology/EtaleAxioms/A11.lean)

## Could a published Galois representation supply the whole seed?

`SeedWU4` asks for one continuous semisimple representation of the prescribed rank. The same representation must meet the unramified conditions, the labeled crystalline jumps and the Frobenius conditions at the eligible places of an arbitrary finite test set. The present construction uses geometry to supply auxiliary representations and a division theorem to recover one witness of the target rank. [Seed statement](../../src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/LimWU4OfLimWU3.lean) · [Geometric construction](../../src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/MainFin.lean)

Harris, Lan, Taylor and Thorne construct compatible systems for regular algebraic cuspidal representations of GL(n). Their compatibility theorem away from the coefficient prime gives part of the comparison. A’Campo, Hevesi, Thorne and Whitmore, Theorem 1.2.1, give labeled Hodge–Tate weights and compatibility after semisimplification at places above the coefficient prime. Corollary 1.2.2 also constrains monodromy. To use these results here, the proof must attach a regular algebraic cuspidal GL(n) representation to the fork’s unitary input, or handle each cuspidal constituent if its transfer is an isobaric sum. It must identify the Satake normalization, the crystalline condition at eligible spherical places and the labeled jumps for that same global witness. A construction that takes the Galois row as an input would be circular. [Harris, Lan, Taylor and Thorne](https://doi.org/10.1186/s40687-016-0078-5) · [A’Campo, Hevesi, Thorne and Whitmore](https://arxiv.org/abs/2607.11763)

## Common-scale coefficients

Write the order at a top as `a(t) = b (x + d(t))` with `|d(t)| ≤ 1` and `x > 1`. Normalizing the weights `a(t)/x` cancels the common factor `b/x`. For a nonempty finite set of tops, the weighted and uniform averages of any complex observable of norm at most one differ by at most `1/(x-1)`. The proof bounds the total absolute deviation of the offsets from their mean by the number of tops. A character evaluated on each top satisfies the observable bound. Adding an existing error for the uniform character average therefore gives the corresponding weighted coefficient error. The follow-up below bounds the signed prime loss for the arithmetic kernel. [Lean estimate](CommonScaleCoefficient.lean) · [Common-scale comparison, §§3–4](https://hexagonmath.org/pdf/2611.00828v1)

### Signed loss on thick labels

The two host constructions now share the finite prime-power expansion and the subtraction of the Fourier main term. Each host proves the splitting and inertia facts it needs. The active character-balance module shrinks from 263 to 119 lines. Its shared provider grows by 36 lines. This removes 108 lines reachable from Main and from each Galois row entry point. The comparison uses [PR #12 at 9c5ef1f](https://github.com/mmmbeer/riemann-hypothesis/tree/9c5ef1fe888275b4898f98a0120c8f849ba912dd). [Shared proof](../../src/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean) · [Host with a specified set of split primes](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean)

The common-scale calculation uses the fork’s actual character sum, prime kernel and weight function. At fixed order `a`, the nonprincipal centering terms cancel when the weight changes from `v` to `w`. The principal character contributes `(a/F) log(w/v)`, where `F` is the number of labels in Φ. Both weights must be positive and the cutoff must cover both arguments. For `v = a/x` and a thick weight in `[b,b+h]`, the excess over `v` is at most `h + b/x`. The opposite logarithmic loss is bounded by `log(1 + 1/x)` before multiplication by `a/F`. [Centering identity and weight bounds](CommonScalePrimeMass.lean) · [Preprint, §3, equation (3.6)](https://hexagonmath.org/pdf/2611.00828v1)

For each prime power `n`, its nonnegative kernel has total mass two, distributed uniformly on the Frobenius coset including at ramified primes. Let `S` be the thick subset of the translation subgroup and let `C` bound the number of tops in any one coset. Summing over translations and tops gives mass at most `2 |S| C`. If every thick weight exceeds its comparison weight by at most `δ`, the signed prime loss in this sum is at most `2 |S| C δ` for `n < x` and at most zero for `n ≥ x`. This is the coefficient before multiplication by `log p` for `n = p^i`. The estimates permit empty sets and ties at the cutoff. [Prime-mass and signed-loss theorems](CommonScalePrimeMass.lean)

To replace the active change-of-argument proof, the remaining step is to sum these bounds with the prime logarithms and stages, add the thin-label error and identify the resulting weighted character average with the input required by `ch_core`. The current caller still uses its original change-of-argument estimate. [Current caller](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean)

## Oscillation and real poles

For a real pole at β, use the correction proportional to `x^β (1 − cos(u log x))`. In the coordinate `t = log x`, the transform is a sum of three elementary Laplace integrals. With the correction subtracted, the coefficients at β and β ± iu are respectively −1 and +1/2, multiplied by the residue. Lean also proves that subtracting a finite family of corrections with nonnegative residues preserves the strict upper sign on a good interval after the usual shift. A separate lemma places a forced positive excursion inside a good power window whenever the exponents satisfy λ(1 − α) ≥ 1. Applying Kaczorowski and Pintz still requires meromorphic continuation of the corrected family transform, a frequency avoiding its existing poles, and the quantitative sign-change theorem for the resulting transform. An unbounded sequence of sign changes can miss the prescribed intervals. [Lean calculation](OscillationCorrection.lean) · [Correction, §5](https://hexagonmath.org/pdf/2611.00828v1) · [Kaczorowski and Pintz, Theorem 1 and Corollary 1](https://personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1986.Kaczorowski_1.pdf)

## Verification

The source measurement checks that all project imports resolve and that the import graph is acyclic. Only the independent Challenge module is outside Main under `src`. An audit of the 20 affected downstream import scopes checked the released declaration dependencies and editor references for their 104 original modules. It found two references to the retired code, the old D2 proof and the naturality witness used by E6. Both are replaced here.

The following commands reproduce the size comparison and run the focused checks on a checkout with the pinned toolchain and Mathlib cache.

```sh
python3 verification/simplification/measure-import-footprint.py
python3 verification/simplification/check-row-wiring.py
lake build +Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.A0:olean +Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.A11:olean
lake build +Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance:olean
lake env lean verification/simplification/CommonScalePrimeMass.lean
lake env lean verification/simplification/CommonScaleCoefficient.lean
lake env lean verification/simplification/OscillationCorrection.lean
```
