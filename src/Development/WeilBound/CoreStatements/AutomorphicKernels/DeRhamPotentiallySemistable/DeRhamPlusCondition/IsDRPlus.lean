import Development.WeilBound.CoreStatements.PublishedTheorems.PotentialSemistability.DeRhamPotSemistableLit

noncomputable section

namespace PfDRPst

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

def IsDRPlus {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) {d : ℕ}
    (ρ : K.fixingSubgroup →* GL (Fin d) ℚ_[l]) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) (BdR l),
    (∀ i j, P i j ∈ Set.range (algebraMap (BdRp l) (BdR l))) ∧ P * Q = 1 ∧
    ∀ σ : K.fixingSubgroup, (ρ σ : Matrix (Fin d) (Fin d) ℚ_[l]).map (qQ l) * P.map (σD σ.1) = P

end PfDRPst
