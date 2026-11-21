import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

variable {K : Type} [Field K]

def tors (B : AbVar K) (n : ℕ) : Subgroup (𝟙_ (Over (Sp K)) ⟶ B.X) := (powMonoidHom n).ker

theorem mem_tors {B : AbVar K} {n : ℕ} {y : 𝟙_ (Over (Sp K)) ⟶ B.X} : y ∈ tors B n ↔ y ^ n = 1 := Iff.rfl

abbrev mulN (B : AbVar K) (n : ℕ) : B.X.left ⟶ B.X.left := (𝟙 B.X ^ (n : ℤ)).left

def transl (B : AbVar K) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) : B.X ⟶ B.X := (toUnit B.X ≫ y) * 𝟙 B.X

theorem transl_mulN (B : AbVar K) (n : ℕ) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) (hy : y ∈ tors B n) :
    (transl B y).left ≫ mulN B n = mulN B n := by
  rw [mulN, ← Over.comp_left]
  congr 1
  rw [zpow_natCast, transl, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow,
    mem_tors.1 hy, MonObj.comp_one, _root_.one_mul]

theorem preimage_le (B : AbVar K) (n : ℕ) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) (hy : y ∈ tors B n) (V : B.X.left.Opens) :
    mulN B n ⁻¹ᵁ V ≤ (transl B y).left ⁻¹ᵁ (mulN B n ⁻¹ᵁ V) := fun x hx => by
  change ((transl B y).left ≫ mulN B n) x ∈ V
  rw [transl_mulN B n y hy]
  exact hx

def act (B : AbVar K) (n : ℕ) (y : tors B n) (V : B.X.left.Opens) :
    Γ(B.X.left, mulN B n ⁻¹ᵁ V) →+* Γ(B.X.left, mulN B n ⁻¹ᵁ V) :=
  ((transl B y.1).left.appLE (mulN B n ⁻¹ᵁ V) (mulN B n ⁻¹ᵁ V) (preimage_le B n y.1 y.2 V)).hom

end GlobalTheory.PushEigen
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH GlobalTheory.PushEigen
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

def ptOverClosureIso (K : Type) [Field K] [IsAlgClosed K] :
    ptOver K (AlgebraicClosure K) ≅ 𝟙_ (Over (Sp K)) := by
  let σ : K ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hI : IsIso (spMap (algebraMap K (AlgebraicClosure K))) := by
    change IsIso (Spec.map σ.toCommRingCatIso.hom)
    infer_instance
  exact Over.isoMk (asIso (spMap (algebraMap K (AlgebraicClosure K)))) (by
    change spMap _ ≫ 𝟙 _ = spMap _
    exact Category.comp_id _)

def ptClosureEquiv {K : Type} [Field K] [IsAlgClosed K] (B : AbVar K) :
    B.Pt ≃* (𝟙_ (Over (Sp K)) ⟶ B.X) where
  toFun x := (ptOverClosureIso K).inv ≫ x
  invFun y := (ptOverClosureIso K).hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ x y

end GlobalTheory.PushEigen
end
end
