import Formalism.FlagUnipotentLattices.BlockDistFromLows
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.InterlacingOfBlocksSecondCase

open Formalism.HermitianLatticeCounting.S8 Finset MeasureTheory Filter Topology TensorProduct

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

example (f : Fin 2 → ℝ) (g : ℝ) : (∑ i, f i + g) = (∑ i, f i) + g := rfl


end Formalism.HermitianLatticeCounting.P
