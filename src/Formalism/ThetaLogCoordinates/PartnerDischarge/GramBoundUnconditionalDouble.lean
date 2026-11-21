import Formalism.ThetaLogCoordinates.PartnerDischarge.StatementPW
import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementF
import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementH
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep

namespace Formalism.InvariantFactorPaths.OddLevelGainBounds

open Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

def GramBoundUnconditionalDouble : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (a κ : ℝ),
    1 ≤ a → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → (LLw.total : ℝ) ≤ 2 * a →
    2 * (((K + 3) * r ^ 2 : ℝ) * logEightAPlusR p a r) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ

end Formalism.InvariantFactorPaths.OddLevelGainBounds

namespace Formalism.InvariantFactorPaths.OddLevelGainBounds

open Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.KP.LL MvPolynomial Finset

end Formalism.InvariantFactorPaths.OddLevelGainBounds
