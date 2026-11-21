import Formalism.FlagUnipotentLattices.InterlaceBlocksW

open Finset TensorProduct

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def QDetNegTranspose : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ x : ℂ, Formalism.REAL.qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E ((n : ℂ) - 1 - x)

end Formalism.HermitianLatticeCounting.S8
