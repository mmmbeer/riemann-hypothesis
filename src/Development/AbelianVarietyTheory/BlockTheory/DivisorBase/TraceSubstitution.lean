import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds

open MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceSubstitution

open Formalism.GradedWeylDivisibility Formalism.L2.DIV

def substTr {r r' : ℕ} (n : ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    MvPolynomial (Fin r × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin r' × Fin n) ℂ :=
  aeval fun v => ∑ b : Fin r', C (x b v.1) * X (b, v.2)

def substTrO {r r' : ℕ} (n : ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Option (Fin r' × Fin n)) ℂ :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r', C (x b v.1) * X (some (b, v.2)))

theorem substTr_mem {r r' n : ℕ} (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ)
    {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n ν) : substTr n x f ∈ dualWeyl ℂ r' n ν := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWH_algHom (substTr n x) (colW r n) (colW r' n) (fun v => ?_) hf.1, ?_⟩
  · rw [substTr, aeval_X]
    exact IsWeightedHomogeneous.sum _ _ _ fun b _ => (isWeightedHomogeneous_X ℂ _ (b, v.2)).C_mul _
  · intro l j hlj
    have h1 : (colAddGen ℂ l j).comp (substTr n x) = (substTrO n x).comp (colAddGen ℂ l j) := by
      apply MvPolynomial.algHom_ext
      intro v
      by_cases h : v.2 = j
      · simp [substTr, colAddGen, substTrO, h, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      · simp [substTr, colAddGen, substTrO, h]
    have h2 : (rename (R := ℂ) (some : Fin r' × Fin n → Option (Fin r' × Fin n))).comp (substTr n x) =
        (substTrO n x).comp (rename some) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [substTr, substTrO]
    have e1 := DFunLike.congr_fun h1 f
    have e2 := DFunLike.congr_fun h2 f
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hf.2 l j hlj]

def rhoNu {r r' n : ℕ} (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    dualWeyl ℂ r n ν →ₗ[ℂ] dualWeyl ℂ r' n ν :=
  (substTr n x).toLinearMap.restrict fun _ hf => substTr_mem ν x hf

def invNorm {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : dualWeyl ℂ r n ν) : ℝ :=
  √((fockS f.1 f.1).re / (fockS (hw ℂ hn ν) (hw ℂ hn ν)).re)

end GlobalTheory.IndefiniteRowSideFullHecke.TraceSubstitution
