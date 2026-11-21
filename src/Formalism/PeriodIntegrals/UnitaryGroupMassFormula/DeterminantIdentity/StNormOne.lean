import Mathlib
import Formalism.PeriodIntegrals.DetIdPG

open NumberField

noncomputable section

namespace PI.DIP

def detId (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}

def IsLat (E : Type) [Field E] [NumberField E] (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤

def StNormOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ x, c (c x) = x) →
    ∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) → 𝔞 * 𝔟 = 1 →
      ∃ (h : ℕ) (z : E), 0 < h ∧ z * c z = 1 ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {z}

end PI.DIP
