import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.LiftWord

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def FrobLift (p : ℕ) {W : Type*} [CommRing W] (σ : RingAut W) : Prop := ∀ a : W, (p : W) ∣ σ a - a ^ p

def FactX2mul : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (m m' : Matrix (Fin n) (Fin n) R),
    actF K 1 = K ∧ actF (actF K m) m' = actF K (m * m')

def FactX2wedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X : Fin n → R) (m : Matrix (Fin n) (Fin n) R),
    actF (wedgeF K X) m = wedgeF (actF K m) (Matrix.vecMul X m)

def FactX2contr : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (Y : Fin n → R) (m : (Matrix (Fin n) (Fin n) R)ˣ),
    actF (contrF K Y) (↑m : Matrix _ _ R) =
      contrF (actF K (↑m : Matrix _ _ R)) (Matrix.vecMul Y (↑m⁻¹ : Matrix _ _ R).transpose)

def MinorMap : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ) (m : Matrix (Fin n) (Fin n) R)
    (I J : Finset (Fin n)), φ (minorF m I J) = minorF (m.map φ) I J

def ContractWedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X Y : Fin n → R),
    contrF (wedgeF K X) Y = (fun I => (∑ a, X a * Y a) * K I) - wedgeF (contrF K Y) X

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
