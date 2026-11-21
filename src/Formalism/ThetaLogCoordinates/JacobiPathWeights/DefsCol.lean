import Mathlib

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

abbrev Form (R : Type*) (n : ℕ) := Finset (Fin n) → R

def sg {n : ℕ} (I : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (I.filter fun j => m < j).card

variable {R : Type*} [CommRing R] {n : ℕ}

def oneF : Form R n := fun I => if I = ∅ then 1 else 0

def wedgeF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ I, ((sg I m : ℤ) : R) * K (I.erase m) * X m

def contrF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : R) * X m * K (insert m I)

def stepF (up : Bool) (K : Form R n) (X : Fin n → R) : Form R n :=
  if up then wedgeF K X else contrF K X

variable {ι : Type*}

def colUp (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (l : ℕ) : Bool := isVec (lt l) == primal

def colDeg (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) : ℕ → ℤ
  | 0 => 0
  | l + 1 => colDeg primal isVec lt l + (if colUp primal isVec lt l then 1 else -1)

def colCostly (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (l : ℕ) : Prop :=
  if primal then
    (if isVec (lt l) then (r : ℤ) ≤ colDeg primal isVec lt l else colDeg primal isVec lt l ≤ (r : ℤ))
  else isVec (lt l) = true

instance (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (l : ℕ) :
    Decidable (colCostly r primal isVec lt l) := by unfold colCostly; infer_instance

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
