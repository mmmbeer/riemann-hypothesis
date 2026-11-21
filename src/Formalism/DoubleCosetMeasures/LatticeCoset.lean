import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.DoubleCosetEqPreimage
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard

namespace Formalism.DoubleCosetMeasures.Final

open Formalism.DoubleCosetMeasures

theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := Formalism.DoubleCosetMeasures.P.intTwoSided
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := Formalism.DoubleCosetMeasures.P.simpleAdd
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := Formalism.DoubleCosetMeasures.P.intInv
theorem isoInv : Formalism.DoubleCosetMeasures.IsoInv := Formalism.DoubleCosetMeasures.P.isoInv
theorem isoFinite : Formalism.DoubleCosetMeasures.IsoFinite := Formalism.DoubleCosetMeasures.P.isoFinite
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := Formalism.DoubleCosetMeasures.P.suppCompact
theorem suppJ : Formalism.DoubleCosetMeasures.SuppJ := Formalism.DoubleCosetMeasures.P.suppJ
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.lemmaUSplit
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
theorem volJ : Formalism.DoubleCosetMeasures.VolJ := Formalism.DoubleCosetMeasures.P.volJ
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
