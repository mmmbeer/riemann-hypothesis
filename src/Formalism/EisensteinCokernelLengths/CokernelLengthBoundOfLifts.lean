import Mathlib
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids

noncomputable section

open Classical

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts

open Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.V2

def LenBound2 : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (ℓ ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def CokernelLengthBoundOfLifts : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V₁ : Type) [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
    [Module O V₁] [IsScalarTower O AA V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
    [Module O V₂] [IsScalarTower O AA V₂]
    (W₁ : WachDatum E n V₁) (W₂ : WachDatum E n V₂) (h : Hom W₁ W₂) (g g₀ e e' : ℕ)
    (s₀ : Finset ((ZMod n → V₂) × (ZMod n → V₂))),
    W₂.FIN g → s₀.card ≤ g₀ → (↑s₀ : Set ((ZMod n → V₂) × (ZMod n → V₂))) ⊆ W₂.Zf →
    (∀ p ∈ W₂.Zf, (B.ℓ ^ e : ℕ) • p ∈ Submodule.span O (↑s₀ : Set ((ZMod n → V₂) × (ZMod n → V₂))) ⊔ h.Im) →
    (∀ p ∈ Submodule.span O (↑s₀ : Set ((ZMod n → V₂) × (ZMod n → V₂))), (B.ℓ ^ e' : ℕ) • p ∈ h.Im) →
    h.col ≤ ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) *
      Module.length O (O ⧸ Ideal.span {(B.ℓ : O)})

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts
