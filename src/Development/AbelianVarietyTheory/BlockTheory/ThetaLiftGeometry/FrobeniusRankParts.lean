import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

section Twist

variable {Γ : Type} [Group Γ] {O : Type} [CommRing O] {a : ℕ}

def twistRep (ρ : Γ →* GL (Fin a) O) (ξ : Γ →* Oˣ) : Γ →* GL (Fin a) O where
  toFun g := Units.map (Matrix.scalar (Fin a) : O →+* Matrix (Fin a) (Fin a) O).toMonoidHom (ξ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    have hc : ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) * Matrix.scalar (Fin a) (ξ h : O) =
        Matrix.scalar (Fin a) (ξ h : O) * ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) :=
      ((Matrix.scalar_commute (ξ h : O) (fun r => Commute.all _ r) _).eq).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (Matrix.scalar (Fin a) (ξ h : O)), ← hc, mul_assoc]


end Twist

section Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations

end
