import Mathlib

noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

abbrev CoarseVar (I1 I2 : Type) : Type := I1 ⊕ (I2 ⊕ I2)

def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)

end Formalism.InvariantFactorPaths.BranchingDimensions
