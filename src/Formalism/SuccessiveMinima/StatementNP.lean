import Mathlib

open Filter Topology

noncomputable section

namespace Formalism.FN

variable {K : Type*} [NormedField K]

def ConvOn (a : ℕ → K) (r : ℝ) : Prop :=
  Tendsto (fun k : ℕ => ‖a k‖ * r ^ k) atTop (𝓝 0)

def gNorm (a : ℕ → K) (r : ℝ) : ℝ := ⨆ k : ℕ, ‖a k‖ * r ^ k

def wdeg (a : ℕ → K) (r : ℝ) : ℕ := sSup {k : ℕ | ‖a k‖ * r ^ k = gNorm a r}

def evalS (a : ℕ → K) (x : K) : K := ∑' k : ℕ, a k * x ^ k

def NewtonSlope : Prop :=
  ∀ {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] (a : ℕ → K) (r₁ r₂ : ℝ),
    0 < r₁ → r₁ < r₂ → ConvOn a r₂ → a ≠ 0 →
      gNorm a r₁ * (r₂ / r₁) ^ wdeg a r₁ ≤ gNorm a r₂

example (p : ℕ) [Fact p.Prime] : IsAlgClosed (PadicAlgCl p) := inferInstance
example (p : ℕ) [Fact p.Prime] : NormedAlgebra ℚ_[p] (PadicAlgCl p) := inferInstance
example (p : ℕ) [Fact p.Prime] : IsUltrametricDist (PadicAlgCl p) := inferInstance
example (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℚ_[p] := inferInstance
example (p : ℕ) [Fact p.Prime] : CompleteSpace ℚ_[p] := inferInstance

end Formalism.FN
