import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

def tors {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℕ) : Subgroup (T ⟶ P.A) where
  carrier := {x | x ^ k = 1}
  one_mem' := one_pow k
  mul_mem' := by
    intro x y hx hy
    haveI := P.isAb.comm
    have hc : Commute x y := mul_comm x y
    have hx' : x ^ k = 1 := hx
    have hy' : y ^ k = 1 := hy
    show (x * y) ^ k = 1
    rw [hc.mul_pow, hx', hy', _root_.mul_one]
  inv_mem' := by
    intro x hx
    have hx' : x ^ k = 1 := hx
    show x⁻¹ ^ k = 1
    rw [inv_pow, hx', inv_one]

def unitSpec {K : Type} [CommRing K] (u : Kˣ) : Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom u

example {S : Scheme.{0}} (P : PolAV S) (T : Over S) (x : T ⟶ P.A) : x ∈ tors P T 0 := pow_zero x

example {S : Scheme.{0}} (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) :
    x * y = lift x y ≫ μ[P.A] ∧ (1 : T ⟶ P.A) = toUnit T ≫ η[P.A] := ⟨rfl, rfl⟩

example {K : Type} [CommRing K] : Function.Injective (unitSpec (K := K)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective

end GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws
