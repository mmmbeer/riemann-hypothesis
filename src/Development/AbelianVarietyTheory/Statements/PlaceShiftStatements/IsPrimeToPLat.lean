import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.LTors

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

example : IsAlgClosed (AlgebraicClosure (ZMod 3)) := inferInstance

end GlobalTheory.AV.LTors
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.LTors GlobalTheory.PDivGroup GlobalTheory.Dieu
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogParam

def zpW (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

abbrev eh {k : Type} [Field k] {A : AbVar k} (x : End A) : A.X ⟶ A.X := Hom.hom (A := A) (B := A) x

def oactOf {k : Type} [Field k] {C : Type} [CommRing C] (A : AbVar k) (φ : C →+* End A) : OAct C A.X where
  act c := eh (φ c)
  hom c := inferInstance
  one := by rw [map_one]; rfl
  mul a b := by rw [mul_comm, map_mul]; rfl
  add a b := by rw [map_add]; rfl

structure Pt (p : ℕ) {k : Type} [Field k] {O : Type} [Ring O] (star : O ≃+* Oᵐᵒᵖ) (A₀ : AbVar k)
    (ι₀ : O →+* End A₀) (c₀ : Pic A₀.X.left) where

  A : AbVar k

  act : O →+* End A

  c : Pic A.X.left
  ample : IsAmpleCls c
  rosati : ∀ b : O, IsAdj (A := A) (B := A) c c (act b) 1 (act (star b).unop)
  primeToP : ∃ e : ℕ, e.Coprime p ∧ ∀ (Y : Over (Sp k)) (x : Y ⟶ A.X),
    AbVar.lam c (fst Y A.X ≫ x) (snd Y A.X) = 0 → x ^ e = 1

  f : A₀ ⟶ A

  N : ℕ
  N_pos : 0 < N
  isog : IsIsogeny f
  lin : ∀ b : O, ι₀ b ≫ f = f ≫ act b

  den : ℕ

  num : ℕ
  den_pos : 0 < den
  num_pos : 0 < num
  pol : den • AbVar.lam c (fst A₀.X A₀.X ≫ f.hom) (snd A₀.X A₀.X ≫ f.hom) = num • AbVar.lam c₀ (fst A₀.X A₀.X) (snd A₀.X A₀.X)

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

variable {O : Type} [Ring O] {star : O ≃+* Oᵐᵒᵖ} {A₀ : AbVar k} {ι₀ : O →+* End A₀} {c₀ : Pic A₀.X.left}

def Pt.mOf (P : Pt p star A₀ ι₀ c₀) : ℤ := padicValRat p ((P.num : ℚ) / (P.den * P.N ^ 2))

variable (p) in

def IsPrimeToPLat (ι₀ : O →+* End A₀) (L : ∀ (l : ℕ) [Fact l.Prime], Submodule ℤ_[l] (Vl l A₀)) : Prop :=
  (∀ (l : ℕ) [Fact l.Prime], l ≠ p → (L l).FG ∧ Submodule.span ℚ_[l] (L l : Set (Vl l A₀)) = ⊤ ∧
      ∀ (b : O), ∀ x ∈ L l, vmap l (ι₀ b) x ∈ L l) ∧
    Set.Finite {l : ℕ | ∃ h : l.Prime, haveI := Fact.mk h; L l ≠ LinearMap.range (tv l A₀)}

variable [CharP k p] [PerfectRing k p]

abbrev VM (T : Theory p) (G : PDivGroup p k) : Type :=
  FractionRing (WittVector p k) ⊗[WittVector p k] T.M G

def incl (T : Theory p) (G : PDivGroup p k) : T.M G →ₗ[WittVector p k] VM T G :=
  TensorProduct.mk (WittVector p k) (FractionRing (WittVector p k)) (T.M G) 1

def latp (T : Theory p) {G₀ : PDivGroup p k} (t₀ : G₀.TorsionTower A₀.X) (P : Pt p star A₀ ι₀ c₀)
    {G : PDivGroup p k} (t : G.TorsionTower P.A.X) : Submodule (WittVector p k) (VM T G₀) :=
  Submodule.comap ((P.N : WittVector p k) • LinearMap.id)
    (Submodule.map (incl T G₀) (LinearMap.range (T.map (t₀.map t P.f.hom))))

end

end GlobalTheory.IsogParam
end
end
