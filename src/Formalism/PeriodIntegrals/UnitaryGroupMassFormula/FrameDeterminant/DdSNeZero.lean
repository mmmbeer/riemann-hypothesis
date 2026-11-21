import Mathlib
import Formalism.PeriodIntegrals.TripleFrameDeterminant
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LocalDet

section
noncomputable section

open NumberField

namespace PI.FlagFrameDeterminants

open Formalism.MainNotions.S

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

theorem frameExp_succ (r j : ℕ) : frameExp r (j + 1) = frameExp r j + (r - j) := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  omega

end Gen

end PI.FlagFrameDeterminants
end
end

section
noncomputable section

open NumberField

namespace PI.FlagFrameDeterminants

open Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.IsoDetDefs

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}




theorem e_mem_xa (F : FlagG S r T) {j : ℕ} (a : Fin r) (ha : a.val < j) : F.e a ∈ F.Xa j :=
  Submodule.subset_span ⟨a, ha, rfl⟩


end Gen

end PI.FlagFrameDeterminants
end
end

section
noncomputable section

namespace PI.TripleFrameDeterminant.W

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NFAll : Prop :=
  ∀ {D : D7} (X : TermTie D) (u : D.what₂.Word), LatticeIndexAndWeightTheory.TieOK X u →
    ∀ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t → LatticeIndexAndWeightTheory.NF X t

end PI.TripleFrameDeterminant.W

end
end

section
noncomputable section

open NumberField

namespace PI.TripleFrameDeterminant.W

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.IsoDetDefs PI.FlagFrameDeterminants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

end PI.TripleFrameDeterminant.W
end
end
