import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelMetric

variable {C : Type} [Field C] (O : ValuationSubring C)

abbrev SO : Scheme.{0} := Spec (CommRingCat.of O)

abbrev TO : Over (SO O) := Over.mk (𝟙 (SO O))

abbrev TC : Over (SO O) := Over.mk (Spec.map (CommRingCat.ofHom O.subtype))

def gen : TC O ⟶ TO O := Over.homMk (Spec.map (CommRingCat.ofHom O.subtype)) (Category.comp_id _)

def cst (c : C) : Γ((TC O).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c

variable {O} (A : Over (SO O)) [GrpObj A] (L : LB A.left)

def IntegralSec (a : ℤ) (s : LB.Sec (LPow A L a (TC O))) (κ : C) : Prop :=
  ∃ s₀ : LB.Sec (LPow A L a (TO O)), ∀ (i : Fin 1 → L.ι) (W : ((TC O) ⊗ A).left.Opens)
    (h₁ : W ≤ (LPow A L a (TC O)).U i) (h₂ : W ≤ (gen O ▷ A).left ⁻¹ᵁ (LPow A L a (TO O)).U i),
    liftFun A W (cst O κ) * (((TC O) ⊗ A).left.presheaf.map (homOfLE h₁).op).hom (s.f i) =
      ((gen O ▷ A).left.appLE _ W h₂).hom (s₀.f i)

end GlobalTheory.ModelMetric
