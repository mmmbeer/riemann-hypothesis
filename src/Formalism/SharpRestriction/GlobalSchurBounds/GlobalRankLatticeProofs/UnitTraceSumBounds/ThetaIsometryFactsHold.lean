import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoDualPair
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoFunV
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoScaleA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoInvMetric
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalDeg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoDerivB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMinorExpand
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwEval
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

end Formalism.MainNotions.GL3Columns
