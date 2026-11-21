import Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic

noncomputable section

open Polynomial MeasureTheory
open scoped TensorProduct NumberField ComplexConjugate

namespace Formalism.IrreducibleCountingLemmas.Z

def DegreeOneSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
    P.inertiaDeg ℤ = 1 → P.ramificationIdx (𝓞 F) = 1 →
    ((P.under (𝓞 F)).primesOver (𝓞 E)).ncard = 2

def DirectedHomLine : Prop :=
  ∀ (k V W : Type) [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (Vs : ι → Submodule k V)
    (H : Submodule k (V →ₗ[k] W)), Monotone Vs → (⨆ i, Vs i) = ⊤ →
    (∀ i, ∀ l ∈ H, ∀ l' ∈ H, l.domRestrict (Vs i) ≠ 0 →
      ∃ c : k, l'.domRestrict (Vs i) = c • l.domRestrict (Vs i)) →
    ∀ l ∈ H, ∀ l' ∈ H, l ≠ 0 → ∃ c : k, l' = c • l

def UnipotentTwistCharpoly : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A U : Module.End K V), Commute A U → IsNilpotent (U - 1) → (A * U).charpoly = A.charpoly

def GeneralizedEigenSplit : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (γ₀ γ : Module.End K V) (c : K) (t : ℕ) (s : K[X]), Commute γ₀ γ →
    γ₀.charpoly = s * (X - C c) ^ t → s.eval c ≠ 0 →
    IsCompl (LinearMap.ker (aeval γ₀ s)) (γ₀.maxGenEigenspace c) ∧
    Module.finrank K (γ₀.maxGenEigenspace c) = t ∧
    (∀ v ∈ LinearMap.ker (aeval γ₀ s),
      γ₀ v ∈ LinearMap.ker (aeval γ₀ s) ∧ γ v ∈ LinearMap.ker (aeval γ₀ s)) ∧
    ∀ v ∈ γ₀.maxGenEigenspace c, γ₀ v ∈ γ₀.maxGenEigenspace c ∧ γ v ∈ γ₀.maxGenEigenspace c

def SchurOrthogonalityCompact : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (τ : G →* (V →ₗ[ℂ] V)),
    (∀ g x y, inner ℂ (τ g x) (τ g y) = inner ℂ x y) → (∀ x, Continuous fun g => τ g x) →
    (∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ u₁ u₂ v₁ v₂ : V,
      (Module.finrank ℂ V : ℂ) * ∫ g, inner ℂ v₁ (τ g u₁) * conj (inner ℂ v₂ (τ g u₂)) ∂μ =
        ((μ Set.univ).toReal : ℂ) * (inner ℂ u₂ u₁ * inner ℂ v₁ v₂)

def BCCyclicVector : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (g : Module.End K V), g.charpoly.Separable → ∃ e : V, ∀ v : V, ∃ p : K[X], aeval g p e = v

open scoped Classical in

def BCIsolation : Prop :=
  ∀ (H : Type) [Monoid H] (I J : Type) [Fintype I] [Fintype J] (χ : I → H →* ℂ) (χ' : J → H →* ℂ)
    (a : I → ℂ) (b : J → ℂ), (∀ f : H, ∑ i, a i * χ i f = ∑ j, b j * χ' j f) →
    ∀ c : H →* ℂ, ∑ i with χ i = c, a i = ∑ j with χ' j = c, b j

end Formalism.IrreducibleCountingLemmas.Z
