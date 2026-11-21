import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

def SpecK {O A T' G : Type*} [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    {P : Type*} [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A) (v₁ : L)
    (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl))) (ℓ e' : ℕ) {j : ℕ}
    (κ : Fin j → G → L) (Kc : Fin j → G → A) : Prop :=
  (∃ Kz : Fin j → coZ1s (resRep (uRep O (M := P) r χ) Dl),
    (∀ a (g : Dl), Kc a g = inc ((Kz a : Dl → P) g)) ∧ ∀ a, Submodule.mkQ _ (Kz a) ∈ Hf₁) ∧
  ∀ a, ∀ g ∈ Dl, Kc a g • v₁ = ((ℓ : O) ^ e') • κ a g

def Speck {O A T' G : Type*} [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    {P : Type*} [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (δO : O) (Dl : Subgroup G) (inc : P →ₗ[A] A)
    (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl))) (ℓ e' : ℕ)
    (u : G → O) (k0 : G → A) : Prop :=
  (∃ kz : coZ1s (resRep (uRep O (M := P) r χ) Dl),
    (∀ g : Dl, k0 g = inc ((kz : Dl → P) g)) ∧ Submodule.mkQ _ kz ∈ Hf₁) ∧
  (∀ g, ∃ a : A, k0 g = a * E) ∧
  ∀ g ∈ Dl, ∀ m : M, k0 g • m = ((ℓ : O) ^ e' * δO * u g) • m

def StatCompColK : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] O P]
    (L : Type) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    [Module ℤ_[ℓ] L] [IsScalarTower ℤ_[ℓ] O L]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A) (v₁ : L) (ev : P →ₗ[O] L)
    (hev : ∀ p, ev p = inc p • v₁), Function.Surjective ev →
    ∀ (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl)))
      (Hf₂ : Submodule O (H1z (resRep (uRep O (M := L) r χ) Dl))) (e' j : ℕ)
      (κ : Fin j → G → L) (κz : Fin j → coZ1s (resRep (uRep O (M := L) r χ) Dl)),
    (∀ a (g : Dl), (κz a : Dl → L) g = κ a g) → (∀ a, Submodule.mkQ _ (κz a) ∈ Hf₂) →
    LiftSrcO ℓ Hf₁ Hf₂ (mapH1 _ _ ev (ev_equiv r χ Dl inc v₁ ev hev)) e' →
    ∃ Kc : Fin j → G → A, SpecK r χ Dl inc v₁ Hf₁ ℓ e' κ Kc

def StatCompColk : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    [Module ℤ_[ℓ] P] [IsScalarTower ℤ_[ℓ] O P]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (δO : O) (Dl : Subgroup G) (inc : P →ₗ[A] A)
    (ev : P →ₗ[O] ↥(Ideal.span {δO})),
    (∀ p, ∃ a : A, inc p = a * E) → (∀ p (m : M), inc p • m = ((ev p : ↥(Ideal.span {δO})) : O) • m) →
    ∀ (hev : ∀ g p, ev (uElt r χ g • p) = ev p), Function.Surjective ev →
    ∀ (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl)))
      (Hf₂ : Submodule O (H1z (Representation.trivial O Dl ↥(Ideal.span {δO})))) (e' : ℕ)
      (u : G → O) (uz : coZ1s (Representation.trivial O Dl ↥(Ideal.span {δO}))),
    (∀ g : Dl, (((uz : Dl → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u g) →
    Submodule.mkQ _ uz ∈ Hf₂ →
    LiftSrcO ℓ Hf₁ Hf₂ (mapH1 _ _ ev (ev_equiv_triv r χ Dl ev hev)) e' →
    ∃ k0 : G → A, Speck M r χ E δO Dl inc Hf₁ ℓ e' u k0

end Formalism.RepresentationBoundsCohomology.JL
