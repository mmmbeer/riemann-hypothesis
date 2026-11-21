import Formalism.RealPlaceAnalysis.Complexify

open Matrix

noncomputable section

namespace Formalism.REAL

def lminor {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) : ℂ :=
  (Matrix.of fun a b : Fin i => x (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) a)
    (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) b)).det

def LminorPos : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Yᴴ = Y → ∀ i : Fin (n + 1),
    (lminor (NormedSpace.exp Y) i).im = 0 ∧ 0 < (lminor (NormedSpace.exp Y) i).re

end Formalism.REAL
