import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace PositivityTheory.JLift

variable {R : Type} [CommRing R] {I : Ideal R} {X₀ : Scheme.{0}}

structure Pt (κ : DividedPowers I) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) : Type 1 where

  T : Thick κ s₀

  y : Sp T.B ⟶ X.left
  w : y ≫ X.hom = spMap (algebraMap R T.B)
  red : spMap T.π ≫ y = T.x ≫ i

variable {κ : DividedPowers I} {s₀ : X₀ ⟶ Sp R} {X : Over (Sp R)} {i : X₀ ⟶ X.left}

def Pt.IsChart (a : Pt κ s₀ X i) : Prop :=
  a.T.J = I.map (algebraMap R a.T.B) ∧ IsOpenImmersion a.y

def TrivBy (z : Z1 (O κ s₀)) (t : ∀ a : Pt κ s₀ X i, a.T.B) : Prop :=
  ∀ (a b : Pt κ s₀ X i) (φ : a.T ⟶ b.T), spMap (φ.φ : a.T.B →+* b.T.B) ≫ a.y = b.y → ev z φ = t b - φ.φ (t a)

def Triv (X : Over (Sp R)) (i : X₀ ⟶ X.left) (z : Z1 (O κ s₀)) : Prop :=
  ∃ t : ∀ a : Pt κ s₀ X i, a.T.B, TrivBy z t

def IsSqIdeal (T : Thick κ s₀) (K : Ideal T.B) : Prop :=
  K ≤ T.J ∧ (∀ a ∈ K, ∀ b ∈ K, a * b = 0) ∧ ∀ n, 2 ≤ n → ∀ a ∈ K, T.δ.dpow n a = 0

def IsConn (z : Z1 (O κ s₀)) (T : Thick κ s₀) (η : Ω[T.B⁄R]) : Prop :=
  ∀ (T' : Thick κ s₀) (K : Ideal T'.B), IsSqIdeal T' K → ∀ (ψ ψ' : T ⟶ T') (D : Ω[T.B⁄R] →+ T'.B),
    (∀ (b : T.B) (ω : Ω[T.B⁄R]), D (b • ω) = ψ.φ b * D ω) →
    (∀ b : T.B, D (KaehlerDifferential.D R T.B b) = ψ'.φ b - ψ.φ b) → (∀ b : T.B, ψ'.φ b - ψ.φ b ∈ K) →
    ev z ψ' - ev z ψ = D η

def OmFrame {R' : Type} [CommRing R'] (σ : R →+* R') (J : Ideal R') (B : Type) [CommRing B] [Algebra R' B]
    {P : Type 1} [AddCommGroup P] [Module R P] (θ : P → Ω[B⁄R']) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module B M], (∀ r ∈ J, ∀ m : M, algebraMap R' B r • m = 0) →
    ∀ l : P →+ M, (∀ (r : R) (p : P), l (r • p) = algebraMap R' B (σ r) • l p) →
      ∃! D : Ω[B⁄R'] →ₗ[B] M, ∀ p, D (θ p) = l p

def CoFrame {R' : Type} [CommRing R'] (σ : R →+* R') {Y : Scheme.{0}} (s : Y ⟶ Sp R')
    {P : Type 1} [AddCommGroup P] [Module R P] (ω : P → Form s) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra R' B] (x : Sp B ⟶ Y) (hx : x ≫ s = spMap (algebraMap R' B)),
    IsOpenImmersion x → OmFrame σ ⊥ B fun p ↦ connForm (ω p).1 x hx

def LocFrame (J : Ideal R) {P : Type 1} [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀)) (T : Thick κ s₀)
    (ζ : P → T.B) : Prop :=
  ∀ (T' : Thick κ s₀) (ψ₀ : T ⟶ T') (l : P →ₗ[R] T'.B), (∀ p, l p ∈ J.map (algebraMap R T'.B)) →
    ∃! ψ : T ⟶ T', (∀ b : T.B, ψ.φ b - ψ₀.φ b ∈ J.map (algebraMap R T'.B)) ∧
      ∀ p, ev (z p) ψ + ψ.φ (ζ p) = ev (z p) ψ₀ + ψ₀.φ (ζ p) + l p

def Frame (J : Ideal R) {P : Type 1} [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀))
    (t : P → ∀ a : Pt κ s₀ X i, a.T.B) : Prop :=
  ∀ x : X.left, ∃ a : Pt κ s₀ X i, a.IsChart ∧ x ∈ Set.range a.y ∧ LocFrame J z a.T fun p ↦ t p a

theorem redIsMor (κ : DividedPowers I) (w : i ≫ X.hom = s₀) :
    IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ s₀ (RingHom.id R) i :=
  IsMor.of_dividedPowersZeroIdeal κ (by rw [GlobalTheory.Cris.spMap_id, Category.comp_id, Category.comp_id, w])

def PreChart {R₁ : Type} [CommRing R₁] {I₁ : Ideal R₁} {κ₁ : DividedPowers I₁} {s₁ : X₀ ⟶ Sp R₁} {ρ : R →+* R₁}
    (M : IsMor κ s₀ κ₁ s₁ ρ (𝟙 X₀)) {X₁ : Over (Sp R₁)} {i₁ : X₀ ⟶ X₁.left} (a₁ : Pt κ₁ s₁ X₁ i₁)
    (T : Thick κ s₀) (r : T ⟶ M.obj a₁.T) : Prop :=
  a₁.IsChart ∧ Function.Surjective r.φ ∧
    (∀ b : T.B, r.φ b = 0 ↔ b ∈ (RingHom.ker ρ).map (algebraMap R T.B)) ∧
    T.J = I.map (algebraMap R T.B) ∧ Algebra.Smooth R T.B

end PositivityTheory.JLift
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.JLift

def DPFlat : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A)

def NilpotentDividedPowerTrivial : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left)
    (h : IsPullback i X₀.hom X.hom (spMap π)), Flat X.hom →
    ∀ z : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Triv X i ((redIsMor κ h.w).coef.pullbackOneCocycle z) → H1.mk _ z ∈ F1 (X.hom ≫ 𝟙 _)

def Conn : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (T : Thick κ s₀), T.J = I.map (algebraMap R T.B) →
    (∃ e : Z1 (O κ s₀) →ₗ[R] Ω[T.B⁄R], ∀ z, IsConn z T (e z)) ∧ ∀ z e e', IsConn z T e → IsConn z T e' → e = e'

def Glue : Prop :=
  ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), Function.Surjective ρ → IsNilpotent (RingHom.ker ρ) →
    ∀ (X₁ : Over (Sp R₁)) (W : Type) (B B₁ : W → Type) [∀ k, CommRing (B k)] [∀ k, CommRing (B₁ k)] [∀ k, Algebra R (B k)]
      (y₁ : ∀ k, Sp (B₁ k) ⟶ X₁.left) (q : ∀ k, B k →+* B₁ k), (∀ k, IsOpenImmersion (y₁ k)) → (∀ k, Function.Surjective (q k)) →
      (∀ k, RingHom.ker (q k) = (RingHom.ker ρ).map (algebraMap R (B k))) → (∀ k, Algebra.Smooth R (B k)) →
      (∀ k, y₁ k ≫ X₁.hom ≫ spMap ρ = spMap ((q k).comp (algebraMap R (B k)))) →
      (∀ (x : X₁.left) (U : X₁.left.Opens), x ∈ U → ∃ k, x ∈ Set.range (y₁ k) ∧ Set.range (y₁ k) ⊆ (U : Set X₁.left)) →
    ∀ ψ : ∀ k l, Set.range (y₁ l) ⊆ Set.range (y₁ k) → (B k →ₐ[R] B l),
      (∀ k l h (u : B₁ k →+* B₁ l), spMap u ≫ y₁ k = y₁ l → ∀ b, u (q k b) = q l (ψ k l h b)) →
      (∀ k h b, ψ k k h b = b) → (∀ k l m h h' h'' b, ψ l m h' (ψ k l h b) = ψ k m h'' b) →
    ∃ (X : Over (Sp R)) (i₂ : X₁.left ⟶ X.left) (y : ∀ k, Sp (B k) ⟶ X.left), IsPullback i₂ X₁.hom X.hom (spMap ρ) ∧ Smooth X.hom ∧
      (∀ k, IsOpenImmersion (y k)) ∧ (∀ k, y k ≫ X.hom = spMap (algebraMap R (B k))) ∧ (∀ k, spMap (q k) ≫ y k = y₁ k ≫ i₂) ∧
      ∀ k l h, spMap (ψ k l h : B k →+* B l) ≫ y k = y l

def Transfer : Prop :=
  ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), Function.Surjective ρ →
    ∀ (I : Ideal R) (κ : DividedPowers I) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R) (s₁ : X₀ ⟶ Sp R₁)
    (M : IsMor κ s₀ κ₁ s₁ ρ (𝟙 X₀)) (X₁ : Over (Sp R₁)) (i₁ : X₀ ⟶ X₁.left) (a₁ : Pt κ₁ s₁ X₁ i₁) (T : Thick κ s₀) (r : T ⟶ M.obj a₁.T),
    PreChart M a₁ T r → ∀ (P : Type 1) [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀)) (e : P → Ω[T.B⁄R]) (ζ : P → T.B) (ζ₁ : P → a₁.T.B),
    (∀ p, IsConn (z p) T (e p)) → (∀ p, r.φ (ζ p) + ev (z p) r = ζ₁ p) →
    (∀ e₁ : P → Ω[a₁.T.B⁄R₁], (∀ p, IsConn (M.coef.pullbackOneCocycle (z p)) a₁.T (e₁ p)) →
      OmFrame ρ ⊥ a₁.T.B fun p ↦ e₁ p + KaehlerDifferential.D R₁ a₁.T.B (ζ₁ p)) →
    OmFrame (RingHom.id R) (RingHom.ker ρ) T.B fun p ↦ e p + KaehlerDifferential.D R T.B (ζ p)

def Build : Prop :=
  ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I)
    (π : R →+* R₀) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (X₁ : Over (Sp R₁)) (X₀ : Over (Sp R₀)) (i₁ : X₀.left ⟶ X₁.left) (h₁ : IsPullback i₁ X₀.hom X₁.hom (spMap π₁)), Smooth X₁.hom →
    ∀ (M : IsMor κ (X₀.hom ≫ spMap π) κ₁ (X₀.hom ≫ spMap π₁) ρ (𝟙 _)) (P : Type 1) [AddCommGroup P] [Module R P], Module.Projective R P →
    ∀ (z : P →ₗ[R] Z1 (O κ (X₀.hom ≫ spMap π))) (ω₁ : P →ₛₗ[ρ] Form (X₁.hom ≫ 𝟙 _)),
    (∀ p, M.pull1 (H1.mk _ (z p)) = (redIsMor κ₁ h₁.w).pull1 (Form.cl _ (ω₁ p))) → CoFrame ρ (X₁.hom ≫ 𝟙 _) ω₁ →
    ∃ (X : Over (Sp R)) (i₂ : X₁.left ⟶ X.left), IsPullback i₂ X₁.hom X.hom (spMap ρ) ∧ Smooth X.hom ∧
      ∃ t : P →ₗ[R] (∀ a : Pt κ (X₀.hom ≫ spMap π) X (i₁ ≫ i₂), a.T.B), (∀ p, TrivBy (z p) (t p)) ∧ Frame J z t

end PositivityTheory.JLift
end
end
