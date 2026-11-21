import Formalism.ConjugateSelfDual.StatementRest

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section basic

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]

def IsFinitePlace (F : Type*) [Field F] [NumberField F] {Ω : Type*} [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v

def IsPlaceAbove (F : Type*) [Field F] [NumberField F] {Ω : Type*} [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (p : ℕ) : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal

def tw (e : ℤ) (χ : G F Ω →* (Qbar l)ˣ) : G F Ω →* (Qbar l)ˣ := (cyc F Ω l) ^ e * χ

def ResidualSS (ρ : G F Ω →* GL (Fin n) (Qbar l)) (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∀ (σ : G F Ω) (i : ℕ),
    ‖((ρ σ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly -
        ∏ j : Fin n, (X - C (((c j σ : (Qbar l)ˣ)) : Qbar l))).coeff i‖ < 1

def InertiaDiagAt (ρ : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∃ g : GL (Fin n) (Qbar l), ∀ σ ∈ Inertia (F := F) A,
    ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => (((c i σ : (Qbar l)ˣ)) : Qbar l)

def OrdExactAt (ρ : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∃ g : GL (Fin n) (Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id) ∧
    ∀ σ ∈ Inertia (F := F) A, ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i i =
        (((c i σ : (Qbar l)ˣ)) : Qbar l)

def OrdResidAt (ρ : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∃ g : GL (Fin n) (Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id) ∧
    (∀ σ ∈ Inertia (F := F) A, ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i i =
        (((c i σ : (Qbar l)ˣ)) : Qbar l)) ∧
    ∀ σ ∈ A.decompositionSubgroup F, ∀ i : Fin n,
      ‖((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i i -
        (((c i σ : (Qbar l)ˣ)) : Qbar l)‖ < 1

structure HasShape (ρ : G F Ω →* GL (Fin n) (Qbar l)) (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop where
  cont : Continuous ρ
  irred : Irred ρ
  ord : ∀ A, IsPlaceAbove F A l → OrdExactAt ρ A c
  away : ∀ A, IsFinitePlace F A → ¬ IsPlaceAbove F A l → InertiaDiagAt ρ A c
  resid : ResidualSS ρ c

end basic

section proposals

variable {l : ℕ} [Fact l.Prime]

def ConjSelfDualOne {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {n : ℕ} {R : Type*} [CommRing R]
    (ρ : G K Ω →* GL (Fin n) R) : Prop :=
  ∃ s : K ≃+* K, s ≠ RingEquiv.refl K ∧
    ∃ (τ : Ω ≃+* Ω) (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)),
    (∀ x, τ (τ x) = x) ∧
    ∃ J : Matrix (Fin n) (Fin n) R, IsUnit J.det ∧ J.transpose = J ∧
      ∀ σ : G K Ω, (ρ σ : Matrix (Fin n) (Fin n) R).transpose * J *
        (ρ (conjGal s τ hτ σ) : Matrix _ _ _) = J

def SymplecticWith {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {n : ℕ} {R : Type*} [CommRing R]
    (r : G ℚ Ω →* GL (Fin n) R) (ν : G ℚ Ω →* Rˣ) : Prop :=
  ∃ J : Matrix (Fin n) (Fin n) R, IsUnit J.det ∧ J.transpose = -J ∧ (∀ i, J i i = 0) ∧
    ∀ σ, (r σ : Matrix (Fin n) (Fin n) R).transpose * J * (r σ : Matrix _ _ _) =
      (((ν σ : Rˣ)) : R) • J

def SymplecticRankFourModularity (Ω : Type*) [Field Ω] [Algebra ℚ Ω] (S : CuspSpectrum ℚ 4) (l : ℕ) [Fact l.Prime] (e a : ℤ)
    (χ ξ : G ℚ Ω →* (Qbar l)ˣ) : Prop :=
  ∀ r : G ℚ Ω →* GL (Fin 4) (Qbar l), HasShape r ![tw a ξ * tw e χ, tw e χ, tw a ξ, 1] →
    (∀ A, IsPlaceAbove ℚ A l → OrdResidAt r A ![tw a ξ * tw e χ, tw e χ, tw a ξ, 1]) →
    SymplecticWith r (tw a ξ * tw e χ) →
    ∀ ι : Qbar l →+* ℂ, ∃ π : S.Rep, (∀ τ, S.wt π τ = ![e + a, e, a, 0]) ∧ FrobMatch r ι (S.hecke π)

end proposals

end ReciprocityTheory.Gal
