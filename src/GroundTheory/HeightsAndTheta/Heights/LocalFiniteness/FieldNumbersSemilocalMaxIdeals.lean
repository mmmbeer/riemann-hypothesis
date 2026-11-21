import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIrreducibleConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFixedBallMass
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocSeparate
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocUnits
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClopenComponents
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueBundlesSecondOfFirst
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDescendHom

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FibreNonempty.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.FibreNonempty.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalResidueLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalResidueLength.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocalize.proof





theorem GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart : GroundTheory.Heights₂.Heights.StokesOnChart.Statement :=
  @GroundTheory.Heights₂.Heights.StokesOnChart.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover GroundTheory.Heights₂.Heights.AutoClose.CutOffLimit
end

section
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalMaxIdeals.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalMaxIdeals.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalMaxIdeals.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_FibreNonempty GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocUnits.proof GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocSeparate.proof GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocalize.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalResidueLength


theorem GroundTheory.Heights₂.Heights.AutoClose.RegFixedBallMass : GroundTheory.Heights₂.Heights.RegFixedBallMass.Statement :=
  @GroundTheory.Heights₂.Heights.RegFixedBallMass.proof GroundTheory.Heights₂.Heights.RegDensNonneg.proof GroundTheory.Heights₂.Heights.AutoClose.StokesOnChart GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
end
