import Formalism.StatementOC

open Finset

noncomputable section

namespace Formalism

def IsCMType {l : ℕ} (Φ : Finset (ZMod l)ˣ) : Prop := ∀ g : (ZMod l)ˣ, g ∈ Φ ↔ -g ∉ Φ

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1

open Classical in
def HalfTypes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ σ : (ZMod l)ˣ, σ ≠ 1 → σ ≠ -1 →
    2 * ((Finset.univ.filter (fun Φ : Finset (ZMod l)ˣ => IsCMType Φ ∧ 1 ∈ Φ ∧ counts Φ σ)).card)
      = (Finset.univ.filter (fun Φ : Finset (ZMod l)ˣ => IsCMType Φ ∧ 1 ∈ Φ)).card

open ArithmeticFunction Classical in

def WeightedVonMangoldtSumInClasses (l : ℕ) (Φ : Finset (ZMod l)ˣ) (a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊a / b⌋₊,
    if h : IsUnit (n : ZMod l) then
      (if counts Φ h.unit then Λ n * (a / n - b) else 0)
    else 0

end Formalism
