import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

attribute [local instance] Over.cartesianMonoidalCategory

namespace GCorCut

def famCast {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    (e : k = k') (s : Fam Dp F k) : Fam Dp F k' :=
  e ▸ s

def ThFrame {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Dd : DegData V (maximalIdeal V)) (ϖ : V)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam Dd.toPre F 1) : Prop :=
  ∃ (σ : Dd.toPre.SecB 1 0)
    (σF : LB.Sec (LB.LinComb Dd.toPre.P.L (DegPre.famφ Dd.toPre F 0) (DegPre.famε 1))),
    GeneratorPullback.SecScal Dd.toPre.P.L (DegPre.famφ Dd.toPre F 0) (DegPre.famε 1) σF
      (Dd.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB Dd.toPre F).left 1 ∧
    (∀ j, (θ.s 0).f j = σF.f j) ∧
    ¬ ∃ σ' : Dd.toPre.SecB 1 0, ∀ j, σ.f j = constFn Dd.toPre.P.A.hom _ ϖ * σ'.f j

end GCorCut

open GCorCut

variable {D : D7}

end Formalism.MainNotions.ModuliIntegralCharts.H1
