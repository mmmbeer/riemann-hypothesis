import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusQuotientTorsionLift
open GlobalTheory.UU

def TorusStable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G)
    (V : G.left.Opens) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V

def IsBaseChangeTQ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {X : Type} [AddCommGroup X]
    (f : S' ⟶ S) (F : G'.left ⟶ G.left) (Q' : TQ G' X) (Q : TQ G X) (β : Q'.B.left ⟶ Q.B.left) : Prop :=
  TorusCompat f F Q'.i Q.i ∧ IsGrpPullback Q'.B Q.B f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left

abbrev pt {S : Scheme.{0}} {R : Type} [CommRing R] (p : Spec (CommRingCat.of R) ⟶ S) : Over S := Over.mk p

example {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) :
    TorusStable i ⊤ := fun _ _ _ _ => le_top

example {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) (V : Q.B.left.Opens) :
    TorusStable Q.i (Q.q.left ⁻¹ᵁ V) := fun Z t g h => by
  have := Q.q_hom
  have e : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
    rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Category.assoc, toUnit_unique (t ≫ toUnit _) (toUnit _),
      ← Hom.one_def, _root_.one_mul]
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left] at h ⊢
  rwa [e]

example {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) :
    IsBaseChangeTQ (𝟙 S) (𝟙 _) Q Q (𝟙 _) := by
  refine ⟨TorusCompat.refl _, ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩, by simp⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have a : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have b : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [a, b, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.IndefiniteRowSideFullHecke.TorusQuotientTorsionLift
end
