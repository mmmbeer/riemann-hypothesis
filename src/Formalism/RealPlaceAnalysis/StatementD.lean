import Formalism.RealPlaceAnalysis.StatementA

open Finset

noncomputable section

namespace Formalism.REAL

def rhoS (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)

end Formalism.REAL
