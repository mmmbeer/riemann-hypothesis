import Formalism.FlagUnipotentLattices.CuspidalityThreshold

open MeasureTheory NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

def ResidueRingCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ),
    Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E

def FlagUnipotentLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (P : Ideal (𝓞 E)) (F : ℕ → Submodule (𝓞 E) (Fin n → E)),
    F 0 = P • L → F n = L → (∀ i < n, ∀ x ∈ F (i + 1), γ *ᵥ x - x ∈ F i) →
    ∀ x ∈ L, ((γ - 1) ^ n) *ᵥ x ∈ P • L

end Formalism.HermitianLatticeCounting.S7
