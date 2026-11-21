import Formalism.FlagUnipotentLattices.FlagUnipotentLattice

open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def HeightThresholdInequalities : Prop :=
  ∀ (n q : ℕ) (h s : ℝ), 1 ≤ n → 1 ≤ q → s ≤ 9 * (n : ℝ) * q →
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
    16 * (n : ℝ) * q + 8 * s * Real.sqrt (2 * (q : ℝ)) < h ∧ 16 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) < h

open Classical in

def FarSum3 : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h ε : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 ≤ B → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → Real.exp (B * ε) ≤ 2 →
    32 * B ≤ h * ε → 16 ≤ h * ε ^ 2 →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) → (∀ γ ∈ S, ∃ v, ε < d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤
      A * (2 * Fintype.card ι) * 3 ^ Fintype.card ι * Real.exp (-(h * ε ^ 2 / 16))

def Ch (c C₁ Cg : ℝ) : ℝ := 16 / c ^ 2 * (4 * C₁ + 6) * (Cg + 4)

def beP (n P : ℕ) (b : ℝ) : ℝ := Real.sqrt n * b ^ 2 + 3 / 2 * (n : ℝ) ^ ((3 : ℝ) / 2) + 3 * P

end Formalism.HermitianLatticeCounting.S7
