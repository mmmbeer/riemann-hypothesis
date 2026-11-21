import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.CrdTemperate

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace Ad3.LR.B

abbrev U3 : Set M3 := {m | (Matrix.of m).det ≠ 0}

end Ad3.LR.B
