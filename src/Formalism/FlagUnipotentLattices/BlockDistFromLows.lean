import Formalism.FlagUnipotentLattices.QDetNegTranspose

open Finset MeasureTheory Filter Topology TensorProduct

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def BlockDistFromLows : Prop :=
  ∀ (m t : ℕ) (b e : ℕ → ℝ),
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ j < m, ((t : ℝ) + 3) / 2 ≤ |b i - e j|) →
    ∀ i < m, ∀ j < m, i ≠ j → (t : ℝ) + 3 ≤ |e i - e j| ∧
      ∀ len ≤ t + 1, ∀ x ∈ blockP (-e i) len, (t : ℝ) / 2 + 3 ≤ |x + e j|

def kCh (k : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 => kCh k t j + t j + 1

def ExplicitC : Prop :=
  ∀ (n : ℕ) (q h : ℝ), 2 ≤ n → 0 ≤ q → q ≤ (n : ℝ) / 2 →
    16 * (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) * Real.sqrt q ≤ 8 * ((n : ℝ) ^ 2 + 2) * Real.sqrt q ∧
    43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ 43 * (n : ℝ) ^ 3 ∧
    (43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ h →
      120 * n * (q * Real.sqrt q) ≤ h ∧ 8 * ((n : ℝ) ^ 2 + 2) * Real.sqrt q + 16 * ((n : ℝ) - 1) * q < h ∧
        16 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h)

end Formalism.HermitianLatticeCounting.S8
