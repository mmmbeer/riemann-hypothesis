import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.Top.Model

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_pk_mul (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (Q : RP Ψ N) : degFl (pk τ k * Q) = 0 :=
  Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k Q hk


theorem degFl_C_mul (c : ℝ) (Q : RP Ψ N) : degFl (C c * Q) = c * degFl Q := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring


theorem degFl_add (P Q : RP Ψ N) : degFl (P + Q) = degFl P + degFl Q := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]












theorem gap_zero (u : Wt Ψ N) (τ : Ψ) : gap 0 u τ = 0 := by simp [gap]



end GlobalTheory.CompanionTheory.Ar.Top.Model
