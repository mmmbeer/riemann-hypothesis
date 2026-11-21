import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
import Formalism.LocalToGlobal.ProjectiveLattices.ThExpBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndExp
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end ReciprocityTheory.ChartRestriction.G.PullbackSections
