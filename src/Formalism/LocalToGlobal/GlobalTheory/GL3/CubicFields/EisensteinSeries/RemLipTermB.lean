import Mathlib

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT

open MeasureTheory

def qv (a b t : ℝ) : ℝ := (t + a) ^ 2 + b ^ 2

def fF (y a b σ t : ℝ) : ℝ := y ^ σ * qv a b t ^ (-σ)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT

open MeasureTheory

def maj (y b t : ℝ) (a : ℝ) (s : ℝ) : ℝ := (s - 1) * (2 * Real.exp |Real.log y| * y) *
  ((1 + 2 * |Real.log y| + 4 * |Real.log b|) * qv a b t ^ (-(3 / 2) : ℝ) + 4 / b * qv a b t ^ (-1 : ℝ))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.RLT
end
end
