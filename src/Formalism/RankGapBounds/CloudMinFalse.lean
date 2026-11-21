import Mathlib

namespace Formalism.RankGapBounds.JumpSetsAlt

open Finset

def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l

def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat

def CloudMinFalse : Prop :=
  ¬ ∀ (l k : ℕ) (U : Fin k → ℤ) (xm xp : ℤ), l.Prime → StrictAnti U →
    (∀ a, xm ≤ U a ∧ U a ≤ xp) →
    (eExp U l : ℝ) ≤ min ((k : ℝ) ^ 2 * (Nat.log l ((xp - xm).toNat + k) : ℝ))
                         ((k : ℝ) * (((xp - xm).toNat : ℝ) + k) / ((l : ℝ) - 1))

def witnessU : Fin 10 → ℤ := ![114, 113, 112, 111, 110, 4, 3, 2, 1, 0]

def WitnessBig : Prop := 25 ≤ eExp witnessU 101

end Formalism.RankGapBounds.JumpSetsAlt
