import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.InhabitedChartFracSeparable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartNormAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLocalSheets
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleAverage
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ObjectsChowIntChowFormExists
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjFullRankMeetsRegular
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointInj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjFullRankDense
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegularClosureOpen
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.ChartEnergySymm : GroundTheory.Heights₂.Heights.ChartEnergySymm.Statement :=
  @GroundTheory.Heights₂.Heights.ChartEnergySymm.proof GroundTheory.Heights₂.Heights.AutoClose.ChartIbpSymm

theorem GroundTheory.Heights₂.Heights.AutoClose.VertPointInj : GroundTheory.Heights₂.Heights.VertPointInj.Statement :=
  @GroundTheory.Heights₂.Heights.VertPointInj.proof GroundTheory.Heights₂.Heights.AutoClose.VertPointChart

theorem GroundTheory.Heights₂.Heights.AutoClose.VertPointNagata : GroundTheory.Heights₂.Heights.VertPointNagata.Statement :=
  @GroundTheory.Heights₂.Heights.VertPointNagata.proof GroundTheory.Heights₂.Heights.AutoClose.VertPointChart



theorem GroundTheory.Heights₂.Heights.AutoClose.PtsSheetSimpleNull : GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.Statement :=
  @GroundTheory.Heights₂.Heights.PtsSheetSimpleNull.proof GroundTheory.Heights₂.Heights.AutoClose.PtsGenericCount

theorem GroundTheory.Heights₂.Heights.AutoClose.CycleAverage : GroundTheory.Heights₂.Heights.CycleAverage.Statement :=
  @GroundTheory.Heights₂.Heights.CycleAverage.proof GroundTheory.Heights₂.Heights.AutoClose.ConeAverage

theorem GroundTheory.Heights₂.Heights.AutoClose.ConeMapArea : GroundTheory.Heights₂.Heights.ConeMapArea.Statement :=
  @GroundTheory.Heights₂.Heights.ConeMapArea.proof GroundTheory.Heights₂.Heights.AutoClose.ConeMapAreaOne
