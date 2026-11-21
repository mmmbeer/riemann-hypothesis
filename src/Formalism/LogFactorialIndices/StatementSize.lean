import Mathlib

noncomputable section

namespace Formalism.LatticeIndexTer

def ph (u : ℝ) : ℝ := u * Real.log u - u

def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i

def Interlace : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 1 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)

end Formalism.LatticeIndexTer
