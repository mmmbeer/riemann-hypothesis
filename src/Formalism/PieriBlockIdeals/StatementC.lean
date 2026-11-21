import Formalism.RankGapBounds.LargePrimeFactor

open Real Finset

namespace Formalism.CohomologicalDescent.Cor

open Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def DB {ι : Type} (D : Data ι) (τ : ι) : ℤ := D.xlo τ - D.maxB τ

def coefficientBoundTau {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ :=
  ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
    + (D.ecl τ l : ℝ)
    + (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)
    + (if ((D.d0 τ l : ℕ) : ℤ) < DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0)
    + ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))

def BlockIdealBound5 {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.lJ < (l : ℝ) → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l →
    D.t + 2 * D.kap l < l →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (coefficientBoundTau D τ l) else (D.ex τ l : ℝ))

end

end Formalism.CohomologicalDescent.Cor
