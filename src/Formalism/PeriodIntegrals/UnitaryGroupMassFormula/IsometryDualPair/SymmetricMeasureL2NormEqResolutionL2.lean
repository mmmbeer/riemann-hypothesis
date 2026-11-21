import Mathlib
import Formalism.PeriodIntegrals.IsoDualPair

noncomputable section

open scoped ComplexConjugate

namespace PI.IsoDualPair.UnitaryGroupMassFormula

open PI.IsoDualPair

instance finite_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Finite (ColChoice N nu) := by
  unfold ColChoice
  have : ∀ a, Finite (Fin a ↪o Fin N) := fun a =>
    Finite.of_injective (fun e : Fin a ↪o Fin N => (e : Fin a → Fin N))
      (fun e f h => DFunLike.coe_injective h)
  infer_instance

noncomputable instance fintype_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Fintype (ColChoice N nu) := Fintype.ofFinite _

variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}

lemma prC_eq (φ ψ : LaC N nu) : prC φ ψ = ∑ J, φ J * ψ J := finsum_eq_sum_of_fintype _

lemma symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : l2 φ = ∑ J, ‖φ J‖ ^ 2 := finsum_eq_sum_of_fintype _

lemma l2_conj (φ : LaC N nu) : l2 (fun J => conj (φ J)) = l2 φ := by
  rw [symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2]
  simp

end PI.IsoDualPair.UnitaryGroupMassFormula
