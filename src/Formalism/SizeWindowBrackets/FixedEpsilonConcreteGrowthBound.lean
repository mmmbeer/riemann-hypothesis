import Formalism.SizeWindowBrackets.ErrorFormsEventualPowerBound
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LTop7

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LErr7
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6

def cTop7 (eD eL : ℝ) : ℝ := max (eD + 1) (max (eL + 2) 3)

section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataT

def FixedEpsilonConcreteGrowthBound : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2Core eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)

end Formalism.LFunctionChainParameters.LTop7
