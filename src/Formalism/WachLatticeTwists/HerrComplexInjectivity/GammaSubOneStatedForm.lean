import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneInvariants
import Formalism.WachLatticeTwists.HerrComplexInjectivity.Statement

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def IsProdP {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    {M₀ : ℕ} (V' : WachMod (S.prodBase ι pr) M₀ (ι → D)) (W : NData S ι pr D) : Prop :=
  (∀ x, x ∈ V'.N ↔ ∀ i, x i ∈ W.N i) ∧ (∀ x i, V'.φ x i = W.φ i (x (pr i))) ∧
    (∀ x i, V'.γ x i = W.γ i (x i))

def IsLat {A' : Type} [CommRing A'] {D₁ : Type} [AddCommGroup D₁] [Module A' D₁] (ℓ : ℕ) (ϖ : A')
    (N₁ : Submodule A' D₁) : Prop :=
  Module.Free A' ↥N₁ ∧ Module.Finite A' ↥N₁ ∧
  (∀ (a : ℕ) (d : D₁), ∃ k : ℕ, ∃ n ∈ N₁, ∃ d' : D₁, ϖ ^ k • d = n + (ℓ : A') ^ a • d') ∧
  (∀ d : D₁, (ℓ : A') • d ∈ N₁ → d ∈ N₁) ∧
  (∀ d : D₁, (∃ k : ℕ, ϖ ^ k • ((ℓ : A') • d) ∈ N₁) → ∃ k : ℕ, ϖ ^ k • d ∈ N₁)

def FreeN {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ), ∀ i, Nonempty (Module.Basis κ A ↥(W.N i))

def CoboundaryRealisedByExtension {O A' : Type} [CommRing O] [CommRing A'] [Algebra O A'] {B : Base O A'} {M₀ : ℕ}
    {D : Type} [AddCommGroup D] [Module A' D] [Module O D] [IsScalarTower O A' D]
    (V' : WachMod B M₀ D) (ϖ : A') : Prop :=
  ∀ y z m : D, V'.C1 y z → y = V'.φ m - m → z = V'.γ m - m →
    ∃ (D₁ D₂ : Type) (_ : AddCommGroup D₁) (_ : Module A' D₁) (_ : Module O D₁)
      (_ : IsScalarTower O A' D₁) (_ : AddCommGroup D₂) (_ : Module A' D₂)
      (i : D →ₗ[A'] D₁) (p : D₁ →ₗ[A'] D₂) (φ₁ γ₁ : D₁ →ₗ[O] D₁) (e : D₁),
      Function.Injective i ∧ (∀ x, p x = 0 ↔ ∃ x₀, i x₀ = x) ∧ Function.Surjective p ∧
      (∀ a : A', a • p e = 0 → a = 0) ∧ IsLat B.p ϖ (Submodule.span A' {p e}) ∧
      (∀ (a : A') (x : D₁), φ₁ (a • x) = B.φ a • φ₁ x) ∧
      (∀ (a : A') (x : D₁), γ₁ (a • x) = B.γ a • γ₁ x) ∧
      (∀ x, φ₁ (i x) = i (V'.φ x)) ∧ (∀ x, γ₁ (i x) = i (V'.γ x)) ∧
      φ₁ e = e + i y ∧ γ₁ e = e + i z ∧
      (∀ N₁ N₂ : Submodule A' D₁, IsLat B.p ϖ N₁ → IsLat B.p ϖ N₂ →
        GammaTrivialFiniteHeightLattice B φ₁ γ₁ N₁ → GammaTrivialFiniteHeightLattice B φ₁ γ₁ N₂ → N₁ = N₂)

end Formalism.RepresentationBoundsCohomology.JN
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

def GammaSubOneStatedForm : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D)
    (κ : Type) [Fintype κ] (b : ∀ i, Module.Basis κ A ↥(W.N i)),
    S.s = 1 → W.P2 →
    (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) →
    (∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i) →
    (∀ i d k, ρ i d (b i k : D) = (b i k : D)) →
    (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) →
    (∀ a : A, (∀ d : Δ, d • (S.π * a) = S.π * a) →
      ∃ a' : A, (∀ d : Δ, d • a' = a') ∧ S.π * a = IB.j B.X * a') →
    GammaSubOneInvariants IB W ρ

def DeltaN {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    {Δ : Type} [Group Δ] [MulSemiringAction Δ A] (W : NData S ι pr D)
    (ρ : ι → Δ →* Module.End O D) : Prop :=
  (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) ∧
  (∀ i d x, W.φ i (ρ (pr i) d x) = ρ i d (W.φ i x)) ∧
  (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) ∧
  (∀ i d, ∀ x ∈ W.N i, ∃ x' ∈ W.N i, ρ i d x - x = S.π • x') ∧
  FreeN W

def StatDeltaBasis : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (Δ : Type) [Group Δ]
    [Fintype Δ] [MulSemiringAction Δ A] (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D] (W : NData S ι pr D)
    (ρ : ι → Δ →* Module.End O D),
    S.Rad → IsUnit ((Fintype.card Δ : ℕ) : A) → DeltaN W ρ →
    (∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i) ∧
    ∃ (κ : Type) (_ : Fintype κ) (b : ∀ i, Module.Basis κ A ↥(W.N i)),
      ∀ i d k, ρ i d (b i k : D) = (b i k : D)

def StatInvExists : Prop :=
  ∀ (O A A₀ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀] [Algebra O A₀]
    (S : HidaSetting O A) (B : Base O A₀) (Δ : Type) [Group Δ] [Fintype Δ] [MulSemiringAction Δ A]
    (IB : InvBase S B Δ) (ι : Type) (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D]
    [Module O D] [IsScalarTower O A D] (W : NData S ι pr D) (ρ : ι → Δ →* Module.End O D),
    (∀ i d (a : A) x, ρ i d (a • x) = (d • a) • ρ i d x) →
    (∀ i d x, W.φ i (ρ (pr i) d x) = ρ i d (W.φ i x)) →
    (∀ i d x, W.γ i (ρ i d x) = ρ i d (W.γ i x)) →
    ∃ (D' : Type) (_ : AddCommGroup D') (_ : Module A₀ D') (_ : Module O D')
      (_ : IsScalarTower O A₀ D') (j : D' →ₗ[O] (ι → D)) (φ' γ' : D' →ₗ[O] D'),
      IsInv IB W ρ j φ' γ'

end Formalism.RepresentationBoundsCohomology.JN
end
end
