import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsHomogeneousOfIsMultiHomog
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartCutoffEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDiffEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdFibreRatios
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdGraphModel
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelRank
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelTransc
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGenFibreModelTransport
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartConeLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionNotMem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeRingLaurent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightDiff
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSegreChartFibreSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCriticalFibreInfinite

set_option maxSynthPendingDepth 1


theorem GroundTheory.Heights₂.Heights.AutoClose.ChartDiffEnergy : GroundTheory.Heights₂.Heights.ChartDiffEnergy.Statement :=
  @GroundTheory.Heights₂.Heights.ChartDiffEnergy.proof GroundTheory.Heights₂.Heights.ChartCutoffEnergy.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ClosedPointChart : GroundTheory.Heights₂.Heights.ClosedPointChart.Statement :=
  @GroundTheory.Heights₂.Heights.ClosedPointChart.proof GroundTheory.Heights₂.Heights.ClosedPointUnitSection.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartHessCompare : GroundTheory.Heights₂.Heights.ChartHessCompare.Statement :=
  @GroundTheory.Heights₂.Heights.ChartHessCompare.proof GroundTheory.Heights₂.Heights.HermFormCompare.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DualStdFibreRatios : GroundTheory.Heights₂.Heights.DualStdFibreRatios.Statement :=
  @GroundTheory.Heights₂.Heights.DualStdFibreRatios.proof GroundTheory.Heights₂.Heights.GenFibreModelTransport.proof GroundTheory.Heights₂.Heights.DualStdGraphModel.proof GroundTheory.Heights₂.Heights.DualStdModelRank.proof GroundTheory.Heights₂.Heights.DualStdModelTransc.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DualGeomDegCharts : GroundTheory.Heights₂.Heights.DualGeomDegCharts.Statement :=
  @GroundTheory.Heights₂.Heights.DualGeomDegCharts.proof GroundTheory.Heights₂.Heights.ChartDensityIntegrable.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.PtsSheetOnlyNull : GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.proof GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof



theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents : GroundTheory.Heights₂.Heights.Targets.ChartDivisorComponents.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorComponents.proof GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.GoodChartDim : GroundTheory.Heights₂.Heights.GoodChartDim.Statement :=
  @GroundTheory.Heights₂.Heights.GoodChartDim.proof GroundTheory.Heights₂.Heights.ConeVanishingHomog.proof GroundTheory.Heights₂.Heights.ConeSliceIdeal.proof GroundTheory.Heights₂.Heights.ChartDehomogPrime.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_LelongWeightDiff : GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact


theorem GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartConeLength : GroundTheory.Heights₂.Heights.Targets.ChartConeLength.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartConeLength.proof GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent.proof GroundTheory.Heights₂.Heights.Targets.ChartDehomIdeal.proof


theorem GroundTheory.Heights₂.Heights.AutoClose.PtsSegreChartFibreSum : GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum.proof GroundTheory.Heights₂.Heights.SegreChartZeroSet.proof GroundTheory.Heights₂.Heights.SegreChartProjFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeLocalMass : GroundTheory.Heights₂.Heights.ConeLocalMass.Statement :=
  @GroundTheory.Heights₂.Heights.ConeLocalMass.proof GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite GroundTheory.Heights₂.Heights.NullSmaller.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.MahlerAverageSplit : GroundTheory.Heights₂.Heights.MahlerAverageSplit.Statement :=
  @GroundTheory.Heights₂.Heights.MahlerAverageSplit.proof GroundTheory.Heights₂.Heights.MahlerIntegrand.proof GroundTheory.Heights₂.Heights.SphereMeanFubini.proof GroundTheory.Heights₂.Heights.EvalSpecFirst.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeSmoothLocalGraph : GroundTheory.Heights₂.Heights.ConeSmoothLocalGraph.Statement :=
  @GroundTheory.Heights₂.Heights.ConeSmoothLocalGraph.proof GroundTheory.Heights₂.Heights.PolyLocalGenerators.proof GroundTheory.Heights₂.Heights.HolomorphicImplicitGraph.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeFubini : GroundTheory.Heights₂.Heights.ConeFubini.Statement :=
  @GroundTheory.Heights₂.Heights.ConeFubini.proof GroundTheory.Heights₂.Heights.BallVolume.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SphereMeanLinearBall : GroundTheory.Heights₂.Heights.SphereMeanLinearBall.Statement :=
  @GroundTheory.Heights₂.Heights.SphereMeanLinearBall.proof GroundTheory.Heights₂.Heights.SphereMeanLinear.full

theorem GroundTheory.Heights₂.Heights.AutoClose.GraphAreaIntegral : GroundTheory.Heights₂.Heights.GraphAreaIntegral.Statement :=
  @GroundTheory.Heights₂.Heights.GraphAreaIntegral.proof GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.full

theorem GroundTheory.Heights₂.Heights.AutoClose.AreaFormulaInjSet : GroundTheory.Heights₂.Heights.AreaFormulaInjSet.Statement :=
  @GroundTheory.Heights₂.Heights.AreaFormulaInjSet.proof GroundTheory.Heights₂.Heights.AreaFormulaLocal.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement :=
  @GroundTheory.Heights₂.Heights.ConeJacMeasurable.proof GroundTheory.Heights₂.Heights.TangentJacCompress.proof GroundTheory.Heights₂.Heights.KernelProjMeasurable.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.chow_form_of_incidence_zero_locus : GroundTheory.Heights₂.Heights.ObjectsChow.ChowFormToComplexChowForm.Statement :=
  @GroundTheory.Heights₂.Heights.ObjectsChow.ChowFormToComplexChowForm.proof GroundTheory.Heights₂.Heights.IncidenceZeroLocus.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.AdmissibleAENrm : GroundTheory.Heights₂.Heights.AdmissibleAENrm.Statement :=
  @GroundTheory.Heights₂.Heights.AdmissibleAENrm.proof GroundTheory.Heights₂.Heights.AdmissibleAE.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeKrullDimLe : GroundTheory.Heights₂.Heights.ConeKrullDimLe.Statement :=
  @GroundTheory.Heights₂.Heights.ConeKrullDimLe.proof GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.proof



