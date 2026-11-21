import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace BoxTuple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def BoxTup (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E)
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E))
    (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) : Prop :=
  NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
  PullAl D' F oD' (star π) g' g s s₂ ∧
  (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
  QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
  PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
  U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
  IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h

end BoxTuple

open BoxTuple

end Formalism.MainNotions.ModuliIntegralCharts.H1
