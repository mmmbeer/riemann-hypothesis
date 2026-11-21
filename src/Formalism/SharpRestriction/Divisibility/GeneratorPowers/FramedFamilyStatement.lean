import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def FramedFamilyStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π : 𝓞 E), π * star π = (g : 𝓞 E) → (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (_PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (p : QkPt D₁.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g)))) (ζ : F),
    w.IsGen → ζ ≠ 0 → FinOrd D₁ F (g' * g) p w ζ →
  ∀ x : TFK (R := T.V) F ⟶ A₁.A, (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) → QkToAkU U₁.toUnifPre F (g' * g) p x →
  ∀ χ₀ : D₁.toPre.X,
    ∃ s : Fam D₁.toPre F g', NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      (∀ α : D₁.toPre.X, (∀ z : D₁.toPre.X, α ≠ χ₀ + g' • z) → ∀ j, (s.s α).f j = 0) ∧
      ∀ s₂ t₀ t : Fam D₁.toPre F (g' * g),
        PullAl D₁ F oD₁ (star π) g' g s s₂ → PhiRel D₁.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D₁.toPre F ζ t₀ t →
        NuGe D₁ (sumQ pD.xe Q) F v (g' * g) t 0 ∧
        (∀ α : D₁.toPre.X, (∀ z : D₁.toPre.X, α ≠ π • χ₀ + p.y + g' • (π • z)) → ∀ j, (t.s α).f j = 0) ∧
        ∃ c₁ : F, Val0 D₁ F (g' * g) (π • χ₀ + p.y) (t.s (π • χ₀ + p.y)) c₁ ∧
          v c₁ = (((sumQ pD.xe Q (π • χ₀ + p.y) : ℚ) / ((g' * g : ℕ) : ℚ) : ℚ) : WithTop ℚ)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
