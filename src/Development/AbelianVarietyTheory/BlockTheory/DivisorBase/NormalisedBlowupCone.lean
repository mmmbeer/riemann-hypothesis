import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Pol

def PosForm (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Type :=
  {β : levelForms H 1 X // ∀ y, 0 ≤ (β : LinearMap.BilinForm ℤ X) y y}

variable {H : Host E}

abbrev PosForm.form {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (β : PosForm H X) : LinearMap.BilinForm ℤ X := β.1.1

def IsCuspLattice (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Prop :=
  Module.Finite (𝓞 E) X ∧ Module.Projective (𝓞 E) X ∧ Module.finrank (𝓞 E) X ≤ q

def IsSemilinearOverK (H : Host E) {X X₁ : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁]
    (r : X →+ X₁) : Prop :=
  ∃ σ : 𝓞 E ≃+* 𝓞 E, σ H.rt = H.rt ∧ ∀ (a : 𝓞 E) (x : X), r (a • x) = σ a • r x

abbrev ConeFn (H : Host E) : Type 1 := ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X], PosForm H X → ℕ

def IsPolarisation (q : ℕ) (ψ : ConeFn H) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X], IsCuspLattice E q X → ∀ β : PosForm H X,
    (β.1 ≠ 0 → 0 < ψ X β) ∧
    ∃ ℓ : levelForms H 1 X →ₗ[ℤ] ℤ, ℓ β.1 = ψ X β ∧ ∀ γ : PosForm H X, (ψ X γ : ℤ) ≤ ℓ γ.1) ∧
  ∀ (X X₁ : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁],
    IsCuspLattice E q X → IsCuspLattice E q X₁ → ∀ r : X →+ X₁, Function.Surjective r → IsSemilinearOverK H r →
      ∀ (β : PosForm H X) (β₁ : PosForm H X₁), (∀ y z, β.form y z = β₁.form (r y) (r z)) → ψ X β = ψ X₁ β₁

theorem IsPolarisation.zero {q : ℕ} {ψ : ConeFn H} (h : IsPolarisation q ψ) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (hX : IsCuspLattice E q X) {β : PosForm H X} (e : β.1 = 0) : ψ X β = 0 := by
  obtain ⟨-, ℓ, h1, -⟩ := h.1 X hX β
  rw [e, map_zero] at h1
  omega

end Pol

section Blow

def idealAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] (χ : Sp R ⟶ X) : Ideal R :=
  ((J.comap χ).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

example {X : Scheme.{0}} {R : Type} [CommRing R] (χ : Sp R ⟶ X) : idealAlong ⊤ χ = ⊤ := by
  simp [idealAlong, Ideal.map_top]

end Blow

section Main

variable {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F}

variable {Y : Model Xo c β}

end Main

end GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone
