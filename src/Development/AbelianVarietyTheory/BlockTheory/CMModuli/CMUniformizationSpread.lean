import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def omegaC (H : Host E) : ℂ := (1 + H.rt0) / 2

def pureSub {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (pos : Bool) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ j, (ty j (H.rt : E) = H.rt0 ↔ pos = false) → P x j = 0}
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  zero_mem' := by
    intro j _
    simp
  smul_mem' := by
    intro a x hx j hj
    rw [hP.1, hx j hj, mul_zero]

def IsCMUnif (H : Host E) {k : Type} [Field k] (κ : k →+* ℂ) (A : Over (Sp k)) [GrpObj A]
    (e : ℂ → (Over.mk (spMap κ) ⟶ A)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ ∃ m n : ℤ, z = m + n * omegaC H) ∧ IsHolTo Set.univ (fun z => (e z).left)

section Alg

variable {k R : Type} [CommRing k] [CommRing R] {X : Scheme.{0}}

abbrev curveOver (A : Over (Sp k)) (a : k →+* R) (y : Sp R ⟶ X) : Over X :=
  Over.mk (pullback.snd A.hom (spMap a) ≫ y)

def img {A : Over (Sp k)} {a : k →+* R} {y : Sp R ⟶ X} {G : Over X} (φ : curveOver A a y ⟶ G)
    {Z : Scheme.{0}} (t : Z ⟶ Sp R) (p : Over.mk (t ≫ spMap a) ⟶ A) : Over.mk (t ≫ y) ⟶ G :=
  (Over.homMk (pullback.lift p.left t (Over.w p)) (pullback.lift_snd_assoc _ _ _ _) : Over.mk (t ≫ y) ⟶ curveOver A a y) ≫ φ

end Alg

example {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (x : pureSub hP true) : P (H.rt • (x : D.La)) = H.rt0 • P x := by
  funext j
  rw [hP.1, Pi.smul_apply, smul_eq_mul]
  by_cases h : ty j (H.rt : E) = H.rt0
  · rw [h]
  · rw [x.2 j (by simp [h]), mul_zero, mul_zero]

example {k R : Type} [CommRing k] [CommRing R] (a : k →+* R) (A : Over (Sp k)) (v : epsR k ⟶ A) :
    ∃ vR : Over.mk (spMap (algebraMap R (DualNumber R)) ≫ spMap a) ⟶ A,
      vR.left = spMap (Chart.dualMapR a) ≫ v.left := by
  refine ⟨Over.homMk (spMap (Chart.dualMapR a) ≫ v.left) ?_, rfl⟩
  have hv : v.left ≫ A.hom = spMap (algebraMap k (DualNumber k)) := Over.w v
  change (spMap (Chart.dualMapR a) ≫ v.left) ≫ A.hom = spMap (algebraMap R (DualNumber R)) ≫ spMap a
  rw [Category.assoc, hv, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext b <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread
