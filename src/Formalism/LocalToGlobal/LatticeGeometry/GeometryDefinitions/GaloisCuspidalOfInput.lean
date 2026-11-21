import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.QuotientMetricDivisors.Statement

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

example (τ : D.what₂.Tau) : embT D τ = placeRankTwoOne.embTau D τ := rfl

end Formalism.L2.Geo.Def
