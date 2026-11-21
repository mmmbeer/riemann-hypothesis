import Formalism.FockGram.FockGramProofs.FockHerm
import Formalism.FockGram.FockGramProofs.FockSesq
import Formalism.FockGram.FockGramProofs.FockPerm
import Formalism.FockGram.FockGramProofs.DetSymPow
import Formalism.FockGram.FockGramProofs.SubIndexNorm
import Mathlib
import Formalism.FockGram.FockGramProofs.CovolGram
import Formalism.FockGram.FockGramProofs.HermDualOf
import Formalism.FockGram.FockGramProofs.HermitianTensorMulHermitian
import Formalism.FockGram.StatementFock
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive

section
open Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.E

def SymGramPosSemidef : Prop :=
  ∀ (𝕜 σ : Type) [RCLike 𝕜] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ 𝕜),
    G.PosSemidef → (symGram a G).PosSemidef

end Formalism.E
end
end

section
namespace Formalism.E

theorem fockHerm : FockHerm := fischerInnerConjSymm_holds

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
end
