import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def constUnit (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) : Γ((TFK (R := R) F).left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ

theorem ΓSpecIso_hom_constUnit (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (constUnit R F ζ : Γ((TFK (R := R) F).left, ⊤)) = (ζ : F) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (ζ : F)


end GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
