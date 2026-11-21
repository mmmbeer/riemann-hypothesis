import Formalism.FlagUnipotentLattices.GramSubmersionSplit

namespace Formalism.HermitianLatticeCounting.S4

open Finset

def WeightedAmplitudeSqSumBoundTwoTypeClasses : Prop :=
  ∀ (k r q : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be : Ty → ℝ) (isBe : Ty → Prop),
    4 * r + 7 ≤ k → 2 ≤ q → 1 ≤ H → (Nonempty Ty → (q : ℝ) ≤ H) → 0 ≤ nn →
    (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H ^ (r + 2) →
    (∀ t, 1 ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, isBe t → μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * be t ^ (k - 1)) →
    (∀ t d, ¬ isBe t → μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (be t / q) ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ 4 * H ^ (4 * (r + 1)) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    (∀ t d, isBe t → ‖amp t d‖ ≤ 7 * (q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2
      ≤ H ^ (39 * (r + 1) ^ 2) * (q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) * nn

def NonGenericBoundLargeHeight : Prop :=
  ∀ (k r : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be : Ty → ℝ),
    2 ≤ H → 0 ≤ nn → (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H →
    (∀ t, 1 ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * be t ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ 4 * H ^ (4 * (r + 1)) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ H ^ (39 * (r + 1) ^ 2) * nn

def GeomPowers : Prop :=
  ∀ (q k N : ℕ), 2 ≤ q → 2 ≤ k →
    ∑ i ∈ range (N + 1), ((q : ℝ) ^ i) ^ (k - 1) ≤ 2 * ((q : ℝ) ^ N) ^ (k - 1)

def ConductorCharacterLeakBound : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (cond : AddChar T ℂ → ℕ) (q a ρ j : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    ((univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ j).card : ℝ) ≤ (q : ℝ) ^ j →
    (∀ i, j < i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    (∀ ψ : AddChar T ℂ,
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ ((cond ψ - j) * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    ((univ.filter fun u => Q u = 0).card : ℝ)
      ≤ 8 / 7 * (q : ℝ) ^ j * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)

end Formalism.HermitianLatticeCounting.S4
