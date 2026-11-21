import Mathlib

namespace Formalism.SL.NC

open Finset

def NormCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (c : K),
      |((univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = c)).card : ℝ)
          - (Fintype.card L : ℝ) ^ n / (Fintype.card K : ℝ)|
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

end Formalism.SL.NC
