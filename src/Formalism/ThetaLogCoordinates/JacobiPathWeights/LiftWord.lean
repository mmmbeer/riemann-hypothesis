import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DefsCol

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι : Type*}

def stepQ (p : ℕ) (lt : ℕ → ι) (s : ι → ℤ) (l : ℕ) : ℕ :=
  if l = 0 then 1 else p ^ (s (lt l) - s (lt (l - 1))).toNat

def levP (p : ℕ) (s : ι → ℤ) (z : ℤ) (i : ι) : ℕ := p ^ (z - s i).toNat

def minorF {R : Type*} [CommRing R] {n : ℕ} (m : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    (m.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det
  else 0

def actF {R : Type*} [CommRing R] {n : ℕ} (K : Form R n) (m : Matrix (Fin n) (Fin n) R) : Form R n :=
  fun J => ∑ I : Finset (Fin n), K I * minorF m I J

def heavy (r K : ℕ) (isVec : ι → Bool) (x : ι × Fin (r + K)) : Prop := isVec x.1 = true ↔ r ≤ x.2.val

instance (r K : ℕ) (isVec : ι → Bool) (x : ι × Fin (r + K)) : Decidable (heavy r K isVec x) := by
  unfold heavy; infer_instance

def sigM {W O : Type*} [CommRing W] [CommRing O] [Algebra W O] {τ : Type*} {n : ℕ} (σ : RingAut W) (s : ℤ)
    (m : Matrix (Fin n) (Fin n) W) : Matrix (Fin n) (Fin n) (MvPolynomial τ O) :=
  m.map fun a => C (algebraMap W O ((σ ^ s) a))

def frameM {W O : Type*} [CommRing W] [CommRing O] [Algebra W O] (r K : ℕ) (primal : Bool) (lt : ℕ → ι)
    (σ : RingAut W) (s : ι → ℤ) (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ) (l : ℕ) :
    Matrix (Fin (r + K)) (Fin (r + K)) (MvPolynomial (ι × Fin (r + K)) O) :=
  if primal then sigM σ (s (lt (l - 1))) (↑h : Matrix _ _ W)
  else (sigM σ (s (lt (l - 1))) (↑h⁻¹ : Matrix _ _ W)).transpose

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
