import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Tls2.Zar3

open GlobalTheory.CompanionTheory.Hypotheses₂

def DualPolarisationOC : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B) (l' : B ⟶ A) (n : ℕ),
      IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → IsDual B A (swap P) →
      Zarhin.IsPolarisation A B P l → 0 < n → IsMonHom l' → l ≫ l' = 𝟙 A ^ n → l' ≫ l = 𝟙 B ^ n →
        Zarhin.IsPolarisation B A (swap P) l'

end PositivityTheory.Tls2.Zar3
