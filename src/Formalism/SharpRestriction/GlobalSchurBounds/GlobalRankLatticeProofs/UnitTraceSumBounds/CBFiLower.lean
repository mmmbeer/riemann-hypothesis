import Mathlib

noncomputable section

open Finset MeasureTheory

namespace Formalism.MainNotions.Ext.CutB

abbrev cBNC {N : ℕ} (ε : Fin N → Bool) : Type := {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ε ab.1 ≠ ε ab.2}

def cBpp {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if h : a < b ∧ ε a ≠ ε b then z ⟨(a, b), h⟩
    else if h' : b < a ∧ ε b ≠ ε a then star (z ⟨(b, a), h'⟩) else 0

def cBp {N : ℕ} (ε : Fin N → Bool) : ℕ := (univ.filter (fun a => ε a = true)).card

def cBq {N : ℕ} (ε : Fin N → Bool) : ℕ := (univ.filter (fun a => ε a = false)).card

def cBhs {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖ ^ 2

def cBlead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) (hi : i ≤ N) : Matrix (Fin i) (Fin i) ℂ :=
  A.submatrix (Fin.castLE hi) (Fin.castLE hi)

def cBV {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℝ :=
  cBhs ((1 - Matrix.diagonal (fun a : Fin N => if a.val < i then (1 : ℂ) else 0)) * X *
    Matrix.diagonal (fun a : Fin N => if a.val < i then (1 : ℂ) else 0))

end Formalism.MainNotions.Ext.CutB
