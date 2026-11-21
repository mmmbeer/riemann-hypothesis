import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_frame {r n : ℕ} (h : r + 1 = n) (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G) (I : Matrix (Fin n) (Fin r) ℂ)
    (Z : Matrix (Fin n) (Fin 1) ℂ) (FA : Matrix (Fin r) (Fin r) ℂ) (hA : IsUnit FA) (εA : Fin r → Bool)
    (h1 : Iᴴ * G * I = FAᴴ * Formalism.REAL.Jm εA * FA) (h2 : Iᴴ * G * Z = 0) (h3 : Zᴴ * G * Z = 1) :
    ∃ (ε : Fin n → Bool) (FB : Matrix (Fin n) (Fin n) ℂ), IsUnit FB ∧ FBᴴ * Formalism.REAL.Jm ε * FB = G ∧
      ∀ (y : Fin r → ℂ) (a : ℂ), eu (FB *ᵥ (I *ᵥ y + a • fun i => Z i 0)) ^ 2 = eu (FA *ᵥ y) ^ 2 + ‖a‖ ^ 2 := by
  let e : Fin r ⊕ Fin 1 ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  let P : Matrix (Fin n) (Fin n) ℂ := (fromCols I Z).submatrix id e.symm
  let Q : Matrix (Fin n) (Fin n) ℂ := (fromBlocks FA 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm
  let ε : Fin n → Bool := fun i => Sum.elim εA (fun _ => true) (e.symm i)
  have hJ : Formalism.REAL.Jm ε = (fromBlocks (Formalism.REAL.Jm εA) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [ε, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply]
  have h4 : Zᴴ * G * I = 0 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have key : Pᴴ * G * P = Qᴴ * Formalism.REAL.Jm ε * Q := by
    have a1 : Pᴴ * G * P = ((fromCols I Z)ᴴ * G * fromCols I Z).submatrix e.symm e.symm := rfl
    rw [a1, hJ]
    simp only [Q, conjTranspose_submatrix, submatrix_mul_equiv]
    congr 1
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, h1, h2, h3, h4,
      fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hQ : IsUnit Q := by
    rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
    simpa [Q, det_submatrix_equiv_self, det_fromBlocks_zero₂₁] using hA
  have hJ2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, diagonal_mul_diagonal]
    rw [← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hP : IsUnit P.det := by
    have hd := congrArg det key
    have q := ((Matrix.isUnit_iff_isUnit_det _).1 hQ).ne_zero
    have j : (Formalism.REAL.Jm ε).det ≠ 0 := fun h0 => by
      have := congrArg det hJ2
      rw [det_mul, h0, det_one] at this; simp at this
    simp only [det_mul, det_conjTranspose] at hd
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hd
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 q) j) q hd.symm
  refine ⟨ε, Q * P⁻¹, hQ.mul ((Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 hP)), ?_, fun y a => ?_⟩
  · calc (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᴴ * G * (P * P⁻¹) := by rw [← key]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [Matrix.mul_nonsing_inv _ hP]; simp
  · have b1 : I *ᵥ y + a • (fun i => Z i 0) = P *ᵥ (Sum.elim y (fun _ => a) ∘ e.symm) := by
      simp only [P]
      rw [submatrix_mulVec_equiv]
      funext i
      simp [mulVec, dotProduct, Function.comp_def, mul_comm]
    rw [b1, mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hP]
    simp only [Q]
    rw [submatrix_mulVec_equiv]
    simp only [eu]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp]
    simp [Function.comp_def, fromBlocks_mulVec]

variable {D : D7}

end GlobalTheory.SepPer.Model

end
