import Mathlib
import Formalism.LogFactorialIndices.StatementSize

open Finset MeasureTheory
open scoped Real Nat

noncomputable section

namespace Formalism.DimensionVariation

def DominanceMono : Prop :=
  ∀ (r : ℕ) (s μ ν : Fin r → ℝ), Antitone s → (∀ i, 0 ≤ s i) → (∀ i, 0 ≤ μ i) → (∀ i, 0 ≤ ν i) →
    (∀ k : ℕ, (∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), μ i) ≤
      ∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), ν i) →
    (∑ i, μ i) = ∑ i, ν i →
    (∏ i, s i ^ μ i) ≤ ∏ i, s i ^ ν i

def ClassSchur : Prop :=
  ∀ (Cl Cl' : Type) [Fintype Cl] [Fintype Cl'] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ) (T : Cl → Cl' → A →L[ℂ] B) (tmax : ℝ)
    (fn : Cl → A),
    (∀ L, 0 < γ L ∧ γ L ≤ 1) → (∀ L', 0 < γ' L' ∧ γ' L' ≤ 1) → (∀ L L', ‖ε L L'‖ = 1) →
    (∀ L L', ‖T L L'‖ ^ 2 ≤ tmax) →
    (∑ L', γ' L' * ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2) ≤
      ((Fintype.card Cl : ℝ) * (Fintype.card Cl' : ℝ)) * tmax * ∑ L, γ L * ‖fn L‖ ^ 2

end Formalism.DimensionVariation
