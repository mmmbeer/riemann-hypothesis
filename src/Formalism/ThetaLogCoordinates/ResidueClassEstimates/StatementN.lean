import Mathlib

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Consequences : Prop :=
  ∀ (r K Ns p E0 mS : ℕ) (a Y Q : ℝ), 2 ≤ r → 4 * r ≤ Ns → 13 ≤ p → 1 ≤ Y → 1 ≤ Q →
    1088 * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
    32 * p * Y * ((r + K : ℕ) : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    8 ≤ Ns ∧ 416 ≤ a ∧ 1 ≤ Real.log a ∧ 1088 * Ns ^ 2 ≤ r + K ∧
    160 * (Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ∧ 5 * Ns ≤ r + K ∧ 32 * Y ≤ a ∧ 8 * (Ns : ℝ) ≤ a ∧
    32 * (E0 : ℝ) ≤ a ∧ r + K ≤ 2 * (K - 2 * Ns) ∧ Ns + r ≤ K

def PowMulFloorDivLe : Prop :=
  ∀ (p k Dt Do ao : ℕ) (a Y : ℝ), 1 ≤ p → 1 ≤ k → 0 < Y → Dt ≤ Do → (ao : ℝ) ≤ 2 * a →
    (p : ℝ) ^ Dt * (⌊((ao : ℝ) / (p : ℝ) ^ Do) / ((k : ℝ) ^ 2 * Y)⌋₊ : ℝ) ≤ 2 * a / ((k : ℝ) ^ 2 * Y)

def ReducedDegree : Prop :=
  ∀ (k Ns : ℕ) (a Y at' E' E0 Et : ℝ), 0 < Y → 1 ≤ k → 0 ≤ a → E' ≤ E0 → 32 * E0 ≤ a →
    Et ≤ 4 * Ns * a / ((k : ℝ) ^ 2 * Y) → 160 * (Ns : ℝ) ≤ (k : ℝ) ^ 2 * Y → a ≤ at' →
    (9 / 10 : ℝ) * at' ≤ at' - E' - Et

def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0

def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)

end Formalism.InvariantFactorPaths.BranchingDimensions
