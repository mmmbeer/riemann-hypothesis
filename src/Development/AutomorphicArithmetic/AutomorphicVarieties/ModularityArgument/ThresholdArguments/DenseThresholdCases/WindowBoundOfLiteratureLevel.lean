import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CsdMonoOddLitN
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfUsedV
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AlgPosOfExpo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfVanishOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PRepNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdLOfZetaUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.UnramifiedZeta.ZetaUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycFree
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.NormLterm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.LogTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CrossUp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.PartCS
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.NeZeroOfFinprod
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalWeak
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.StUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.GrowthPiJHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRealIntegrands
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapIwasawaDensityEqPairMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelPowerScaling
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeightWhittakerTransformIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalEquationFirstHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNegIdentityGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralIwasawaRightInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIntegralDominatedBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBoundedCompactSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphyGlobal
import GroundTheory.HeightsAndTheta.Theta.SchroedingerTranslates.WmSysEquivDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWhittakerSupportedNearOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseLiftArchimedeanSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualProductWhittakerFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactIntegralProductPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalIntegralEqIwasawaPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaDiagBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaugeSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIntegralGLOfLocHeightLt
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DiscriminantDifferentProductFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaOfSharp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGL3TorusLintegralNeTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGL3ComplexTorusIntegralNeTop
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.ContinuousUnipotentTranslatesHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.InverseLowerLeftStandardElement
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.InverseLowerLeftNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gl3UnipotentYOfMajorant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gl3ConstantTermUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gl3Cuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.OrderedCechToCatCochainsOneApplyValueAtSubset
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.growthAd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondIntegralOfFubini
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDir
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitivePointwiseComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveIntegrableComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGL2BoundComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionPeriodUnipotentSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionPeriodUnipotentThird
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfIntegrableOnHalf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DetNull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSecondGaussDeriv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLeColRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteHIntegralComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeGaussian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeKFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRankTwoFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionIwasawaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSphericalWhittakerDiagLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerDiagonalBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationRationalPlane
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbsNormConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ClozelCohC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRankTwoAutomorphyOfPatching
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InertiaLeRangeOfUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.QuadraticBaseChangeRegularPolarized
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BcRegAlgPolarizedPair
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalGlobalCompatibilityComplex
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsoComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.BOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfLitN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEndsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftingOfCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Sp4In
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcIndCs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KatoTwoWOfPublishedH

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.Lit.Car
end UpperTheory.Lit.Car
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
theorem UpperTheory.V.Af.clozelCohC_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Published.ClozelCohC :=
  fun _ => UpperTheory.V.Z.Coh.clozelCohC
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.QuadraticCharacterUnramified
end GlobalTheory.QuadraticCharacterUnramified
theorem _root_.GlobalTheory.T.inertia_le_range_of_unramified_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ η : HChar F, IsQuadCharOf K η → ∀ (u : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A u → η.UnrAt u → Ine (F := F) A ≤ (res F Ω K).range := by
  intro N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, ha⟩ := N.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι
    (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))
  obtain ⟨ε, hεc, -, hε, hεu⟩ := UpperTheory.exists_quadratic_sign_character F K Ω 2 h2
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv B hB =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hS := Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
    (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by
      obtain ⟨⟨w, hwv, hu', hval⟩, hεv⟩ := not_not.1 hv
      subst hwv
      have h1 := (hE _ hu' B hB).2 σ hσ
      have h3 := (UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ
      have e : δ σ⁻¹ = ε σ⁻¹ := Units.ext (ι.injective (by rw [h1, h3, hval]))
      rwa [map_inv, map_inv, inv_inj] at e
  intro s hs
  have h1 : δ s = 1 := (hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs
  have h3 : ε s = 1 := by
    have e : δ s = ε s := congrFun key s
    rw [← e, h1]
  exact (hε.1 s).1 h3
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BcPolar
theorem bc_regAlg_polarizedPair_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  intro hL F K _ _ _ _ _ _ _ h2 a ha π χ P hreg hpol hBC
  refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ?_⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F K)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hBC.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · obtain ⟨χ', hs, hd⟩ := GlobalTheory.T.base_change_dual_compatible hL.aut.js.1 hL.aut.gk F K h2 a ha π χ P hpol hBC
    obtain ⟨k, hk⟩ := GlobalTheory.BcPolar.exists_sign_twist χ' hs a
    refine ⟨χ' * quadChar K ^ k, fun v => (hk v).trans (zpow_natCast _ _), ?_⟩
    rwa [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
end GlobalTheory.BcPolar
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  atlas_forward_decl _root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LocCompCLit
theorem main_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC :=
  fun H => of_automorphicFormsFiniteGL H.aut.fin
end GlobalTheory.LocCompCLit
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_complex_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC := by
  atlas_forward_decl _root_.GlobalTheory.LocCompCLit.main_alt
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
open private UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
namespace UpperTheory.Gal.SV
theorem attRes_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H
  have hloc := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L
  have hsl := GlobalTheory.T.satakeParameters_local
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have hS := ((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw
  have h1 := frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by
    have g := gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)
    rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
    exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
  rwa [hf, GlobalTheory.RealGal.AttResProof.algSat_pow] at h1
section Descent
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem local_condition_at_place_of_decomposition_le_range (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ha : 1 ≤ a) {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {ι : Qbar l ≃+* ℂ} {π : TR.CuspSub F a} {P : CuspSub K a} (hBC : IsBC π P)
    {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (hG : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι (r.comp (res F Ω K)) wt HT) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A v) (hdec : Dec (F := F) A ≤ (res F Ω K).range) {HTF : (F →+* Qbar l) → Multiset ℤ}
    (hHT : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) : At π ι r HTF h := by
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hl hw => by
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have ST := splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩
  obtain ⟨⟨σ', hσ'⟩, -⟩ := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L K a P w
  obtain ⟨rc', hrc'⟩ := recTExists K Ω A w h'
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi
  have inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y :=
    fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])
  have up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ')) := fun σ hσ hp => by
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    exact gdOf K Ω A w h' rc' hrc' a σ' (UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso i hi.cont
      (GlobalTheory.LocalFieldIso.continuous_symm i hi.cont) _ _ _ _ e he hp)
  have br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL :=
    fun O _ _ _ Bw hj => by
      obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)
      exact ⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩
  refine ⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_,
    fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hy := recTr L.aut.art hi σ σ' e he hrc hrc' hp
    have g := up σ hσ hp
    refine ⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩
    · obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
        (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
      exact ⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩
    · obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
      obtain ⟨-, a2, -, a4⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
      have hpst := (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2
      exact ⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩
  · have g := up σ hσ hp
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    obtain ⟨a1, -, a3, -⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
    have D := GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r
    refine ⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩
    obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ
    have hJ := D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)
    rw [hHT τK, hτK] at hJ
    exact hJ
  · have hp' := ST.1.1 hp
    have g := gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')
    obtain ⟨t, ht⟩ := winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
      (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
    rw [hx.wdOf_eq hl]
    refine UpperTheory.GalN.V.RatioW.descend hi hxx ?_
    rw [(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]
    exact ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    exact (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1
      ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((GlobalTheory.T.aux_statement_23 F K v w i hi.cont a σ σ' e he).2 hs)).1
end Descent
theorem galois_rep_exists_totally_real_rank_two_of_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Bc.QuadBC2 → AdmissibleReal → GaloisRepExistsTotallyRealGL2 := by
  intro litN qbc adm F Ω _ _ _ _ _ _ l _ ι a ha2 ha π χ hreg hpol
  let S : Set (QCM F Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsBC π P}
  have good : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ P : CuspSub ↥Q.K a, IsBC π P}.Infinite := by
    intro v A hA
    obtain rfl := ha2.out
    have hT := GlobalTheory.T.eventually_has_satake_parameters adm F 2 π
    refine (GlobalTheory.T.infinite_quadratic_fields_split_inertia F Ω (fun u => ∃ B, π.HasSat u B) hT v A hA).mono ?_
    rintro Q ⟨hdec, u, A', ⟨B, hB⟩, hA', hine⟩
    refine ⟨hdec, ?_⟩
    rcases qbc F Q.K Q.two π hreg with ⟨η, hq, htw⟩ | hP
    · exact absurd (_root_.GlobalTheory.T.inertia_le_range_of_unramified_alt litN F Ω Q.K Q.two η hq u A' hA' (unrAt_of_isoTwist adm F 2 ha π η htw u B hB)) hine
    · exact hP
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω v0
  have hS : S.Infinite := (good v0 A0 hA0).mono fun Q hQ => hQ.2
  have key : ∀ Q : ↥S, ∃ (P : CuspSub ↥Q.1.K a)
      (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (↥Q.1.K →+* Qbar l) → Multiset ℤ),
      IsBC π P ∧ UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT := by
    rintro ⟨Q, P, hP⟩
    obtain ⟨hregP, χ', hχ'⟩ := _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change litN F ↥Q.K Q.two a ha π χ P hreg hpol hP
    obtain ⟨r, wt, HT, hr⟩ := _root_.UpperTheory.Gal.SV.rowOf' litN.aut.gal ↥Q.K Ω l ι a ha P χ' hregP hχ'
    exact ⟨P, r, wt, HT, hP, hr⟩
  choose P r wt HT hP hr using key
  have hatt : ∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q) := fun Q =>
    ⟨(hr Q).cont, (hr Q).ss,
      _root_.UpperTheory.Gal.SV.attRes_alt litN F Ω ↥Q.1.K l ι a ha π (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)⟩
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.T.galois_rep_patching_infinite_family F Ω l ι a π S hS r hatt
  obtain ⟨HTF, hcard, hwts, hbc⟩ := hodgeTate F Ω l ι a π hreg
  have hgal : ∀ᶠ Q : ↥S in Filter.cofinite,
      UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) :=
    hev.mono fun Q hQ => props_iso (hr Q) hQ.1 hQ.2
  have hHT : ∀ Q : ↥S, (∀ τ : ↥Q.1.K →+* Qbar l, HT Q τ = HTF (τ.comp (algebraMap F ↥Q.1.K))) ∧
      ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt Q - ·) :=
    fun Q => hbc ↥Q.1.K Q.1.two (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)
  obtain ⟨Q0⟩ : Nonempty ↥S := hS.nonempty.to_subtype
  let τ0 : F →+* Qbar l := ι.symm.toRingHom.comp (Classical.arbitrary (InfinitePlace F)).embedding
  have hwt : ∀ Q : ↥S, wt Q = wt Q0 := fun Q =>
    GlobalTheory.T.eq_of_multiset_symmetric_reflections (HTF τ0) (wt Q) (wt Q0) (by rw [← Multiset.card_pos, hcard]; exact ha) ((hHT Q).2 τ0) ((hHT Q0).2 τ0)
  have hpick : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ∃ Q : ↥S, Dec (F := F) A ≤ (res F Ω ↥Q.1.K).range ∧
        UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) := by
    intro v A hA
    have hfin := (Filter.eventually_cofinite.1 hgal).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((good v A hA).diff hfin).nonempty
    refine ⟨⟨Q, hQ.2⟩, hQ.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQ.2⟩, hc, rfl⟩
  have hD : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), At π ι ρ HTF h := fun v A h => by
    obtain ⟨Q, hdec, hQ⟩ := hpick v A h
    exact _root_.UpperTheory.Gal.SV.local_condition_at_place_of_decomposition_le_range litN ha (hP Q) hQ h hdec (hHT Q).1
  have hpl : ∀ w B, π.HasSat w B → PlainAtR π w := fun w B hB => by
    obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω w
    exact (hD w A h).plain B hB
  refine ⟨ρ, wt Q0, HTF, hρc, hρs, hpl, fun w σ hσ hp => ⟨fun A h => (hD w A h).cmp σ hσ hp, fun A h => (hD w A h).ht σ hσ hp⟩,
    fun w hw B hB => ?_, fun w hw A h => (hD w A h).ratio hw, hwts, (hHT Q0).2, fun w A h => (hD w A h).crys⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := GlobalTheory.T.local_global_compatibility_real adm F a π w
  have hS := ((GlobalTheory.T.satakeParameters_local F a w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  exact frob_of hw σ hS fun A h rc hrc => (((hD w A h).cmp σ hσ (hpl w B hB σ hσ) rc hrc).1 hw).isWDOf
    (gdOf F Ω A w h rc hrc a σ (hpl w B hB σ hσ))
end UpperTheory.Gal.SV
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Lit UpperTheory.V.Z.Bc
theorem published_hypotheses_from_patching_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (desc : Z.Desc.DescWeak) : _root_.UpperTheory.V.Af.HypothesesH' :=
  { litN := hN, cohC := _root_.UpperTheory.V.Af.clozelCohC_alt hN, conjC := Z.Coh.clozelConjC, borelC := Z.Coh.borelInjC,
    galR := _root_.UpperTheory.Gal.SV.galois_rep_exists_totally_real_rank_two_of_base_change hN UpperTheory.ConvolutionTheory.R2.quadBC2 admissibleReal, smoR := strongMultOneReal,
    gkR := gelfandKazhdanReal strongMultOneReal, admR := admissibleReal, bc := Br.quadBC0_of_two UpperTheory.ConvolutionTheory.R2.quadBC2,
    newform := newformRepOf cuspSemisimpleReal admissibleReal,
    descU := desc, cyc := cycC_holds, cyc2 := Or.inl UpperTheory.ConvolutionTheory.RankTwoDescent.descS, quat := defQuatExists, ssR := cuspSemisimpleReal }
end UpperTheory.V.HV.DescentVanishingReductions
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology
namespace UpperTheory.V.ZK
theorem lemmaK_of_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hB : BOdd) : ∃ CK, LemmaK CK :=
  lemmaK hB (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK
end UpperTheory.V.ZK
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.ZK
theorem lemmaK_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : ∃ CK, LemmaK CK := _root_.UpperTheory.V.ZK.lemmaK_of_litN_alt hN bOdd
end UpperTheory.V.ZK
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Cu
theorem sp4In_alt (hC : GradeZeroInterpolatingElement.CohomologyHyp) (hF : Published.FerreroWashington) (s2 : _root_.UpperTheory.V.Ws.SeedIIAlt) (s4 : _root_.UpperTheory.V.Cu.SeedIVAlt) (hP : _root_.UpperTheory.V.Ws.PMExAlt) : _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.main4_alt hC hF hFit s2 s4 hP
end UpperTheory.V.Cu
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem sp4In0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.sp4In_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH).coh FW.ferreroWashington (_root_.UpperTheory.V.Z.Bc.seedIIs_alt hH) (_root_.UpperTheory.V.Z.Win.Birth.fourth_initial_of_prints_h hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.pmEx_of_printsH hH)
end UpperTheory.V.HV.DescentVanishingReductions
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem vwin_of_hypotheses_H_E_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : VWin :=
  have hK := _root_.UpperTheory.V.ZK.lemmaK_litN_alt hH.litN
  have hE := _root_.UpperTheory.V.Z.Win.Dn.ends0_alt hH
  have h4 := _root_.UpperTheory.V.HV.DescentVanishingReductions.countII_and_countIII_of_printsH_of_sp4In hH hK (_root_.UpperTheory.V.HV.DescentVanishingReductions.sp4In0_alt hH)
  _root_.UpperTheory.V.HV.Core.of_four_alt hH.litN hK (_root_.UpperTheory.V.Z.J.count_i_of_printed_bound_k_kato_automorphy hH hK (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH hH) (_root_.UpperTheory.V.HV.Core0.automorphyUnramified_of_litN_of_gdEnd hH.litN hE.1)) h4.1 h4.2 (_root_.UpperTheory.V.Z.J.count_v_of_printed_bound_k_reduced_unitary_lift hH hK hE.2)
theorem v_window_of_automorphy_csd_ss_mono_odd (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWin :=
  _root_.UpperTheory.V.HV.DescentVanishingReductions.vwin_of_hypotheses_H_E_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt hN UpperTheory.V.Z.Tf.SR.descWeak)
end UpperTheory.V.HV.DescentVanishingReductions
theorem UpperTheory.V.v_window_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWin :=
  _root_.UpperTheory.V.HV.DescentVanishingReductions.v_window_of_automorphy_csd_ss_mono_odd hN
end
end
