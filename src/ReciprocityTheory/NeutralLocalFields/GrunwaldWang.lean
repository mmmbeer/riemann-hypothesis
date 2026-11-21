import Mathlib

open NumberField IsDedekindDomain

namespace Neutral.GrunwaldWang

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

def LiesAbove (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A.nonunits ↔ x ∈ v.asIdeal

def IsComplexConjugationAt (w : InfinitePlace K) (c : Ω ≃ₐ[K] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ InfinitePlace.mk (j.comp (algebraMap K Ω)) = w

def Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (m : ℕ), 0 < m → ¬ 8 ∣ m →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (A : T → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ χ : ∀ v : T, (A v).decompositionSubgroup K →* Multiplicative (ZMod m), (∀ v, Continuous (χ v)) →
    ∀ (R : Finset (InfinitePlace K)) (c : R → (Ω ≃ₐ[K] Ω)), (∀ w, IsComplexConjugationAt w.1 (c w)) →
    ∀ ε : R → Multiplicative (ZMod m), (∀ w, ε w ^ 2 = 1) →
      ∃ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod m), Continuous ψ ∧
        (∀ v : T, ψ.comp ((A v).decompositionSubgroup K).subtype = χ v) ∧ ∀ w : R, ψ (c w) = ε w

end Neutral.GrunwaldWang
