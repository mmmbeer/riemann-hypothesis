import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

noncomputable section

open PowerSeries

namespace GlobalTheory.Col

variable {R : Type} [CommRing R]

def pmeas (p r : ℕ) (g : PowerSeries R) (x : ℕ) : R :=
  ∑ m ∈ Finset.range (r + 1), Algebra.trace R (lev R p m) (ev R p m ((1 + X) ^ (p ^ r - x % p ^ r) * g))

def chSum (p m : ℕ) [NeZero p] (ch : (ZMod (p ^ m))ˣ →* Rˣ) (g : PowerSeries R) : lev R p m :=
  ∑ b : (ZMod (p ^ m))ˣ, ev R p m (PowerSeries.C (ch b : R) * sb (b : ZMod (p ^ m)).val g)

end GlobalTheory.Col
