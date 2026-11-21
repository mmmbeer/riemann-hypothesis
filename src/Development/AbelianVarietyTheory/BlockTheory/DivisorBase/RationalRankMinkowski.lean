import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRankMinkowski

open Formalism.BasicNotions Formalism.MainNotions

def minkExp (n p : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), n / (p ^ i * (p - 1))

def minkNum (n : ℕ) : ℕ := ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime, p ^ minkExp n p

example : minkNum 1 = 2 ∧ minkNum 2 = 24 ∧ minkNum 3 = 48 ∧ minkNum 4 = 5760 := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRankMinkowski

end
