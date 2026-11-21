import Mathlib
open ValuativeRel MeasureTheory Matrix Filter Topology

namespace GlobalTheory.CompanionTheory.GLSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def small (ϖ : k) (n l : ℕ) : Set (GL (Fin n) k) :=
  {g | (∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)
        ≤ valuation k ϖ ^ l) ∧
    ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ϖ ^ l}

end GlobalTheory.CompanionTheory.GLSmall
