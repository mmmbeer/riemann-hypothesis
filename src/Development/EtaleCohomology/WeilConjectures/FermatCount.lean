import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace IsProjOver)

namespace LateralTheory.EWeil

attribute [local instance] MvPolynomial.gradedAlgebra

def Base : Prop :=
  (A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11) ∧
  (B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ DivisorPicardCompatibility ∧ B6h1 ∧ B7) ∧ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5) ∧ D1 ∧ (E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6 ∧ E8)

section Defs
variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k]

def IsFrob {Ω : Type} [Field Ω] [Algebra k Ω] (σ : Ω ≃ₐ[k] Ω) : Prop := ∀ x, σ x = x ^ Nat.card k

abbrev HX (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) : Type 1 :=
  HQ l (sch.obj (geom Ω p)) n 0

def geoF {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) :
    HX l Ω p n →ₗ[ℚ_[l]] HX l Ω p n := galHQ l Ω p n 0 σ⁻¹

def IsEig {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (σ : Ω ≃ₐ[k] Ω)
    (α : AlgebraicClosure ℚ_[l]) : Prop :=
  Module.End.HasEigenvalue ((geoF l p n σ).baseChange (AlgebraicClosure ℚ_[l])) α

def WtIn {X : Scheme.{0}} (p : X ⟶ Sp k) (n : ℤ) (S : Set ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ α, IsEig l p n σ α →
    ∀ ι : AlgebraicClosure ℚ_[l] →+* ℂ, Real.logb (Nat.card k) (‖ι α‖ ^ 2) ∈ S

def FinT {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (a : ℕ) (n i : ℤ), Finite (Ht (l ^ a) (sch.obj (geom Ω p)) n i)

def SmProj (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop := SmoothOfRelativeDimension d p ∧ IsProjOver p

def IsCI (d r : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k) : Prop := SmoothOfRelativeDimension d p ∧
  ∃ (f : Fin r → MvPolynomial (Fin (d + r)) k)
    (e : X ≅ Sp (MvPolynomial (Fin (d + r)) k ⧸ Ideal.span (Set.range f))),
    e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) = p

inductive Peel : ℕ → ∀ {Y : Scheme.{0}} (_ : Y ⟶ Sp k) {X : Scheme.{0}} (_ : X ⟶ Sp k), Prop
  | base {d : ℕ} {Y : Scheme.{0}} (pY : Y ⟶ Sp k) : SmProj d pY → Peel d pY pY
  | step {e : ℕ} {Y X Y' Z : Scheme.{0}} (pY : Y ⟶ Sp k) (pX : X ⟶ Sp k) (pY' : Y' ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens) :
      Peel (e + 1) pY pX → Peel e pY' (ι ≫ pX) → IsClosedImmersion ι → (U : Set X) = (Set.range ι)ᶜ →
      Peel (e + 1) pY (U.ι ≫ pX)

abbrev fibre {R k' : Type} [CommRing R] [Field k'] {X : Scheme.{0}} (f : X ⟶ Sp R) (φ : R →+* k') :
    pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ Sp k' := pullback.snd _ _

abbrev bc (k' : Type) [Field k'] [Algebra k k'] {X : Scheme.{0}} (p : X ⟶ Sp k) : geom k' p ⟶ Sp k' := pullback.snd _ _

end Defs

def GysinSeq : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (e r : ℕ) {X Z : Scheme.{0}} [CompactSpace X] (p : X ⟶ Sp k) (ι : Z ⟶ X) (U : X.Opens), IsClosedImmersion ι →
  SmoothOfRelativeDimension (e + r) p → SmoothOfRelativeDimension e (ι ≫ p) → (U : Set X) = (Set.range ι)ᶜ →
  (FinT l (ι ≫ p) → (FinT l p ↔ FinT l (U.ι ≫ p))) ∧ (FinT l p → FinT l (U.ι ≫ p) → FinT l (ι ≫ p)) ∧
  (FinT l p → FinT l (ι ≫ p) → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ →
    ∃ (g : ∀ a b : ℤ, a + 2 * r = b → (HX l Ω (ι ≫ p) a →ₗ[ℚ_[l]] HX l Ω p b))
      (δ : ∀ b a : ℤ, a + 2 * r = b + 1 → (HX l Ω (U.ι ≫ p) b →ₗ[ℚ_[l]] HX l Ω (ι ≫ p) a)),
      (∀ a b h, Function.Exact (g a b h) (pullHQ l (sch.map (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl)) b 0)) ∧
      (∀ b a h, Function.Exact (pullHQ l (sch.map (geomMap Ω (p := U.ι ≫ p) (q := p) U.ι rfl)) b 0) (δ b a h)) ∧
      (∀ b a h, Function.Exact (δ b a h) (g a (b + 1) h)) ∧
      (∀ a b h x, geoF l p b σ (g a b h x) = (Nat.card k : ℚ_[l]) ^ r • g a b h (geoF l (ι ≫ p) a σ x)) ∧
      ∀ b a h x, δ b a h (geoF l (U.ι ≫ p) b σ x) = (Nat.card k : ℚ_[l]) ^ r • geoF l (ι ≫ p) a σ (δ b a h x))

def Artin : Prop := Base → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ (d : ℕ) {X : Scheme.{0}} [IsAffine X] (p : X ⟶ Sp Ω), SmoothOfRelativeDimension d p →
  ∀ n i : ℤ, (d : ℤ) < n → Subsingleton (Ht q (sch.obj X) n i)

def Trace : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ r : ℕ, 0 < r →
  (Nat.card {x : Sp Ω ⟶ X // x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
      Spec.map (CommRingCat.ofHom ((σ ^ r : Ω ≃ₐ[k] Ω) : Ω →+* Ω)) ≫ x = x} : ℚ_[l]) =
    ∑ n ∈ Finset.range (2 * d + 1), (-1) ^ n * LinearMap.trace ℚ_[l] _ ((geoF l p n σ : Module.End ℚ_[l] _) ^ r)

def FermatCount : Prop := ∀ (F : Type) [Field F] [Finite F] (m e : ℕ), 0 < m → 0 < e →
  ((Nat.card {x : Fin m → F // ∑ i, x i ^ e = 0} : ℝ) - (Nat.card F : ℝ) ^ (m - 1)) ^ 2 ≤
    (e : ℝ) ^ (2 * m) * (Nat.card F : ℝ) ^ m

def Model : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ Sp k), SmProj d p →
  ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : Algebra k k') (Y U : Scheme.{0}) (pY : Y ⟶ Sp k') (pU : U ⟶ Sp k') (r : ℕ),
    Peel d pY pU ∧ IsCI d r pU ∧ ∀ S, WtIn l pY d S → WtIn l p d S

end LateralTheory.EWeil

end
