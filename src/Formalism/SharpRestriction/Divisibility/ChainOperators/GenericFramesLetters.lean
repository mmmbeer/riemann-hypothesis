import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GenFrameSB

section
open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas




theorem kw_of_cutSB (h : CutKW.KWsb) : CutKW.KW := h minor_span_complement


end Formalism.MainNotions.DIV.Lemmas
end

section
open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem cutKW_holds : CutKW.KW := kw_of_cutSB coeffNormLE_iff_spanNormLE_of_hasCompl

theorem theta_isometry_facts_hold (D : D7) : Formalism.MainNotions.OrbitPlaces.ConclusionW D := by
  intro l _ N0 N1 nu Th B
  apply cutKW_holds

end Formalism.MainNotions.DIV.Lemmas
end
