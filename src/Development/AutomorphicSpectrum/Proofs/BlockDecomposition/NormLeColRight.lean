import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableBoundedMulWeightFive
open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.ParsC

noncomputable section

namespace GlobalTheory.CompanionTheory.ParsC.Theta

def Llin : V2 →ₗ[ℝ] M23 × V2 where
  toFun y := (col 0 y, 0)
  map_add' a b := by
    ext i j <;> first
      | (fin_cases i <;> fin_cases j <;> simp [col])
      | simp
  map_smul' c a := by
    ext i j <;> first
      | (fin_cases i <;> fin_cases j <;> simp [col])
      | simp

def L : V2 →L[ℝ] M23 × V2 := LinearMap.toContinuousLinearMap Llin

lemma norm_le_col_left (κ : M22) (y : V2) : ‖κ‖ ≤ ‖col κ y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h := (norm_le_pi_norm (col κ y i) (Fin.castSucc j))
  have h' := norm_le_pi_norm (col κ y) i
  refine le_trans (le_of_eq ?_) (h.trans h')
  fin_cases i <;> fin_cases j <;> simp [col]

lemma norm_le_col_right (κ : M22) (y : V2) : ‖y‖ ≤ ‖col κ y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h := (norm_le_pi_norm (col κ y i) 2)
  have h' := norm_le_pi_norm (col κ y) i
  refine le_trans (le_of_eq ?_) (h.trans h')
  fin_cases i <;> simp [col]

lemma weight_le (κ : M22) (y q : V2) (N i : ℕ) :
    (1 + ‖κ‖) ^ N * (1 + ‖q‖) ^ i * (1 + ‖y‖) ^ 5 ≤ (1 + ‖((col κ y, q) : M23 × V2)‖) ^ (N + i + 5) := by
  set x : M23 × V2 := (col κ y, q)
  have h1 : ‖κ‖ ≤ ‖x‖ := (norm_le_col_left κ y).trans (norm_fst_le x)
  have h2 : ‖y‖ ≤ ‖x‖ := (norm_le_col_right κ y).trans (norm_fst_le x)
  have h3 : ‖q‖ ≤ ‖x‖ := norm_snd_le x
  rw [pow_add, pow_add]
  have a1 : (1 + ‖κ‖) ^ N ≤ (1 + ‖x‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) _
  have a2 : (1 + ‖q‖) ^ i ≤ (1 + ‖x‖) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) _
  have a3 : (1 + ‖y‖) ^ 5 ≤ (1 + ‖x‖) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) _
  gcongr

end GlobalTheory.CompanionTheory.ParsC.Theta
