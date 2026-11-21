import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

def SqrtNegInCyclotomic : Prop :=
  ∀ (l : ℕ), l.Prime → l % 4 = 3 → ∀ (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ l →
    IsSquare (-(l : F))

end Formalism.IrreducibleCountingLemmas.WindowSums
