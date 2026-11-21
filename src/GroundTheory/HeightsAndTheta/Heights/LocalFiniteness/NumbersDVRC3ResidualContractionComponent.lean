import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarNumerator
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocNoetherian
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PValuativeCentre
import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartPrimElt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartSpecCount
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocAwaySpec
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldExistsInv
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBasisIsoFree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFreeSheafBasis
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalChartLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMult
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOrderLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimTwoSumReading
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntermediateRingQuotLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLengthMapIdealLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleLocalQuot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCyclePos
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleSpanMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalDomainDimTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotFinsum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotPrimes
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimesSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCount
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.Imports
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPts
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalLift
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalStrict
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimLeOfIsAlgebraicAdjoinSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ResidualNewVarMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagProjTrdegLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffRing
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotColon
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotRing

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount : GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.proof GroundTheory.Heights₂.Heights.Inter.ChartPrimElt.proof GroundTheory.Heights₂.Heights.Inter.LocAwaySpec.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ValuativeCentre.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof



theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleSpanMul.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocCyclePos.proof GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimesSpanSingleton.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalDomainDimTwo.proof GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.proof GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingNoetherian.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof


theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpModel.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpStrictTransform.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpOrderLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalizedQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.LengthMapIdealLe.proof GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpLocalChart.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMinimal.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalChartLength.full


theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof





theorem GroundTheory.Heights₂.Heights.AutoClose.Model_BasisIsoFree.{u} : GroundTheory.Heights₂.Heights.Model.BasisIsoFree.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.Model.BasisIsoFree.proof.{u} GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.proof
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1Indep : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.of_remaining GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj

theorem GroundTheory.Heights₂.Heights.AutoClose.chart_norm_count : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartNormCount.proof GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount GroundTheory.Heights₂.Heights.Inter.ChartNormPts.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarInj.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarInj.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarUnit.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarUnit.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FunctionFieldFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureModel.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_FlagProjTrdegLe : GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ExceptionalContraction.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ExceptionalContraction.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalCorresp.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalCorresp.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalSat.full GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalLift.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalStrict.full


theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContractionComponent.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualContractionComponent.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffRing.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffRing.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotRing.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotColon.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingDimLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal




theorem GroundTheory.Heights₂.Heights.AutoClose.TubeDeepAreaCount : GroundTheory.Heights₂.Heights.TubeDeepAreaCount.Statement :=
  @GroundTheory.Heights₂.Heights.TubeDeepAreaCount.proof GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCount
end
