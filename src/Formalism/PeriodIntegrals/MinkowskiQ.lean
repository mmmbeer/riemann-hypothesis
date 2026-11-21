import Mathlib
import Formalism.PeriodIntegrals.Minkowski

namespace PI

def MinkowskiBoundQ : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
