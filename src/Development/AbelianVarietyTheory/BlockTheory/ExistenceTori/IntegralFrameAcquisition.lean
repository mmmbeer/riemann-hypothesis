import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c)

variable {Xo c}

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
