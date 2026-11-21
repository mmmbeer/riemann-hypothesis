import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pureVec {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (ε : Bool) : Submodule (𝓞 E) D.La where
  carrier := {v | ∀ i, ¬ (ty i (H.rt : E) = H.rt0 ↔ ε = true) → P v i = 0}
  zero_mem' i _ := by simp
  add_mem' {a b} ha hb i hi := by simp [ha i hi, hb i hi]
  smul_mem' a v hv i hi := by rw [hP.1, hv i hi, mul_zero]

def PureSpan {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : Prop :=
  ∀ v : D.La, ∃ n : ℕ, 0 < n ∧ n • v ∈ pureVec hP true ⊔ pureVec hP false

section Maps

variable {S X Y : Scheme.{0}} (C : Over S) (G : Over X) (f : Y ⟶ S) (x : Y ⟶ X)

abbrev MapOver : Type := Over.mk (pullback.snd C.hom f ≫ x) ⟶ G

variable {C G f x}

def MapOver.ev (φ : MapOver C G f x) {T : Scheme.{0}} (t : T ⟶ Y) (p : Over.mk (t ≫ f) ⟶ C) :
    Over.mk (t ≫ x) ⟶ G :=
  Over.homMk (pullback.lift p.left t (Over.w p) ≫ φ.left) (by
    have := Over.w φ
    simp only [Over.mk_left, Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at this ⊢
    rw [Category.assoc, this, pullback.lift_snd_assoc])

end Maps

section Clauses

variable {S X Y : Scheme.{0}} {C : Over S} [GrpObj C] {G : Over X} [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}

end Clauses

end GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign
