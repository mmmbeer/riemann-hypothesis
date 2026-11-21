import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField GlobalTheory.ChowHt

namespace GlobalTheory.IndefiniteRowSideFullHecke.FramedLatticeZeroCycleHeight

structure IsFramedLattice {F : Type} [Field F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop where

  pos : 0 < N

  span : Function.Surjective w.mulVec

  frame : ∀ σ, IsUnit (A σ).det

example : IsFramedLattice (!![2, 3] : Matrix (Fin 1) (Fin 2) ℚ) (fun _ => !![5]) where
  pos := Nat.one_pos
  span := fun x => ⟨![x 0 / 2, 0], by
    funext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring⟩
  frame := fun _ => by simp

end GlobalTheory.IndefiniteRowSideFullHecke.FramedLatticeZeroCycleHeight
