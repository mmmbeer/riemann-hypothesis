import Mathlib
import Formalism.GrowthSums.StatementA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def CappedGainSubLE : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de v i₀ : ℝ)
    (i : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → TTodd ⊆ TT → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) →
    (∀ s e, 0 ≤ i s e) → (∀ s e, e ∉ E → i s e = 0) →
    gamP p * ∑ s ∈ TT, al s - i₀ - ∑ s ∈ TT, ∑ e ∈ E, i s e - de ≤ v →
    i₀ + ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e ≤ ∑ s ∈ TT \ TTodd, al s →
    (∀ s ∈ TTodd, ∀ e, i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    gainG p TT TTodd al cap de - ∑ s ∈ TT \ TTodd, al s ≤ v

end Formalism.GrowthSums
