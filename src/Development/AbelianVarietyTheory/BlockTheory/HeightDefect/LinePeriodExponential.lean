import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LogarithmicDifferentialCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

instance factPrime (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def chi (H : Host E) : DirichletCharacter ℂ H.d := (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

def dlogL (H : Host E) : ℝ := (deriv (chi H).LFunction 1 / (chi H).LFunction 1).re

def logOmCurve (H : Host E) : ℝ := Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) - dlogL H

def logOm (H : Host E) : ℝ := Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - dlogL H

theorem chi_ne_one (H : Host E) : chi H ≠ 1 := by
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; have := H.d_mod; omega
  rw [chi, MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)]
  exact quadraticChar_ne_one h2

variable {H : Host E}

section Curve

variable {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'}

def IsCurveFibre (f : R →+* R') (C : Ell H R ω) (C' : Ell H R' ω') (φ : C'.P.A.left ⟶ C.P.A.left) : Prop :=
  ω' = f ω ∧ IsPolFibre f C.P C'.P φ ∧ (∀ a, (C'.act.act a).left ≫ φ = φ ≫ (C.act.act a).left) ∧
    IsVecOver f φ C.v C'.v

structure IsCurveExp (C : Ell H R ω) (s : R →+* ℂ) (e : ℂ → (Over.mk (spMap s) ⟶ C.P.A)) : Prop where
  add : ∀ z w, e (z + w) = e z * e w
  onto : Function.Surjective e
  ker : ∀ z, e z = 1 ↔ ∃ m n : ℤ, z = m + n * s ω
  hol : IsHolTo Set.univ fun z => (e z).left

end Curve

def HasPeriod {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) : Prop :=
  ∃ n : (M →+* ℂ) → ℝ, (∀ s, 0 < n s ∧ ∀ r, IsLieNormSq C.P C.v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
    x = -meanLog M n

theorem HasPeriod.unique {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} {C : Ell H (𝓞 M) ω} {x y : ℝ}
    (hx : HasPeriod C x) (hy : HasPeriod C y) : x = y := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨n', hn', rfl⟩ := hy
  rw [show n = n' from funext fun s => ((hn' s).2 _).1 (((hn s).2 _).2 rfl)]

section Family

variable {R : Type} [CommRing R] {ω : R}

structure IsHomFam (C : Ell H R ω) (t : SAB H (Sp R)) {D : Datum H} (L : Submodule (𝓞 E) D.La)
    (φ : L → (C.P.A ⟶ t.G)) : Prop where
  hom : ∀ a, IsMonHom (φ a)
  add : ∀ a b, φ (a + b) = φ a * φ b
  smul : ∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s
  lin : ∀ (k : OK H) a, C.act.act k ≫ φ a = φ a ≫ t.act.act (k : 𝓞 E)

structure IsPolFam (C : Ell H R ω) (t : SAB H (Sp R)) {D : Datum H} (L : Submodule (𝓞 E) D.La) (ε : ℤˣ)
    (φ : L → (C.P.A ⟶ t.G)) : Prop extends IsHomFam C t L φ where
  lam : ∃ h, IsKForm D ε h ∧ ∀ a b : L, LamEq t.PP.L (φ a) (φ b) C.P.L (C.act.act (h a b)) (𝟙 C.P.A)


end Family

structure IsExp {S : Scheme.{0}} (t : SAB H S) (y : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (ex : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop where
  period : IsPeriod D ty Pe
  add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ z ∈ Pe.range
  lin : ∀ (a : 𝓞 E) z, ex (fun k => ty k (a : E) * z k) = ex z ≫ t.act.act a
  hol : IsHolTo Set.univ fun z => (ex z).left
  weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
    Out.WeilIs t.G t.PP.L k (ex ((k : ℂ)⁻¹ • Pe a)) (ex ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

theorem isHolTo_comp {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} {c : V → W} (hc : Differentiable ℂ c) (hB : ∀ z, c z ∈ B)
    (h : IsHolTo B y) : IsHolTo Set.univ fun z => y (c z) := fun U f => by
  obtain ⟨h₁, h₂⟩ := h U f
  refine ⟨?_, h₂.comp hc.differentiableOn fun z hz => ⟨hB z, hz.2⟩⟩
  convert h₁.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨hB z, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩


def typeVal (H : Host E) (b : Bool) : ℂ := if b then H.rt0 else -H.rt0

structure LatData {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (Λ : ℝ) where
  A : Bool → Datum H
  sigP : (A true).p = 1 ∧ (A true).q = 0
  sigM : (A false).p = 0 ∧ (A false).q = 1
  ψ : ∀ j : Fin D.p ⊕ Fin D.q, (A j.isLeft).La →ₗ[𝓞 E] D.La
  hh : Fin D.p ⊕ Fin D.q → 𝓞 E
  pure : ∀ j a, ψ j a ∈ PureType.lat hP (typeVal H j.isLeft)
  form : ∀ j a b, D.EF (ψ j a) (ψ j b) = (A j.isLeft).EF (hh j • a) b
  span : ∀ x : D.La, ∃ N : ℕ, 0 < N ∧ N • x ∈ ⨆ j, LinearMap.range (ψ j)
  one_le : 1 ≤ Λ
  bound : ∀ j (τ : E →+* ℂ), ‖τ (hh j : E)‖ ≤ Λ ^ 2

namespace LatData

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe} {Λ : ℝ}

def IsConj (X : LatData hP Λ) : Prop :=
  ∃ κ : (X.A true).La ≃ₗ[𝓞 E] (X.A false).La, ∀ a b, (X.A false).EF (κ a) (κ b) = -(X.A true).EF a b

end LatData


section Degree

variable {K : Type} [Field K] [NumberField K]

def IsDegDe (x : KeyIn K) (δ : ℝ) : Prop :=
  ∃ (oa : HeightOneSpectrum (𝓞 K) → ℤ) (nth : (K →+* ℂ) → ℝ),
    (∀ 𝔭, ∃ a M, KeyPow.IsLocalModel x 𝔭 a M ∧ 𝔭.valuation K a = WithZero.exp (-oa 𝔭)) ∧
    (Function.support oa).Finite ∧
    (∀ σ, 0 < nth σ ∧ ∃ (x' : KeyIn ℂ) (nη : ℝ), KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) nη) ∧
    δ = (∑ᶠ 𝔭, (oa 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) + (1 / 2) * ∑ σ, Real.log (nth σ)) /
      Module.finrank ℚ K

def IsDegDeOf (P : Out.PolAV (Sp (𝓞 K))) (δ : ℝ) : Prop :=
  ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left), IsPolFibre (algebraMap (𝓞 K) K) P x.P φ ∧ IsDegDe x δ

end Degree

end GlobalTheory.IndefiniteRowSideFullHecke.LogarithmicDifferentialCharacter
end
