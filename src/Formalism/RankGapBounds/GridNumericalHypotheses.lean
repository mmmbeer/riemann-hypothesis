import Mathlib
import Formalism.RankGapBounds.RandomSubsetCounterexample

section
namespace Formalism.RankGapBounds.AbsolutelyIrreducibleSpan

structure Hyp (k m t r N : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  N_def : N = k + m * (t + r + 8)
  h₀_big : (t : ℝ) + 2 * (N : ℝ) ^ 3 < h₀

end Formalism.RankGapBounds.AbsolutelyIrreducibleSpan
end

section
namespace Formalism.RankGapBounds.ExistsSmulMemTer

abbrev G0 := ZMod 2 × ZMod 2
abbrev GG (e : ℕ) := G0 × ZMod (2 ^ e)

def sg : G0 := (1, 0)
def c0 : G0 := (0, 1)
def cc (e : ℕ) : GG e := (c0, 0)

def InPhi {e : ℕ} (γ : GG e) : Prop := γ.1.2 = 0

def place {e : ℕ} (γ : GG e) : GG e := if γ.1.2 = 0 then γ else γ + cc e

def OrbitCoord : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ), (place (i • φ + ((0 : G0), t))).2 = t + i • φ.2

end Formalism.RankGapBounds.ExistsSmulMemTer
end

section
namespace Formalism.RankGapBounds.V4

open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer

def RankGapPrintedLemma : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 16 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

def RankGapDecayHypothesis : Prop :=
  ∀ n m γ : ℝ, 3 ≤ n → 1 ≤ m → m ≤ n → n ^ 7 ≤ γ →
    120 * n * (m / 2) ^ ((3 : ℝ) / 2) ≤ γ

structure GridNumericalHypotheses (k m t r : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  h₀_big : (t : ℝ) + 2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < h₀

end Formalism.RankGapBounds.V4
end
