import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers

noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain ArithmeticFunction
open Formalism.HermitianLattices.GL2PrimeSums (Li PP)

def QE : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u →
    ‖psi0 χ u + zsum χ {ρ | |ρ.im| < T} (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ {ρ | |ρ.im| < 1} (fun ρ => 1 / ‖ρ‖))

def QF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    (ntZeros χ ∩ {ρ | |ρ.im - t| ≤ 1}).Finite ∧
      zsumR χ {ρ | |ρ.im - t| ≤ 1} (fun _ => 1) ≤ C * Real.log (q * (|t| + 2))

def QA : Prop :=
  ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
      2 ≤ bigQ K L → ∃ (θ : (L ≃ₐ[K] L) → ℝ) (β : ℝ),
        (((∀ σ, θ σ = 0) ∧ ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (b : ℝ), χ ^ 2 = 1 → 1 - 1 / (8 * Real.log (bigQ K L)) < b → b < 1 →
            ¬ HeckeZero L χ b) ∨
          ∃ χ₁ : (L ≃ₐ[K] L) →* ℂˣ, χ₁ ^ 2 = 1 ∧ 1 - 1 / (8 * Real.log (bigQ K L)) < β ∧ β < 1 ∧ HeckeZero L χ₁ β ∧
            ∀ σ, (θ σ : ℂ) = (χ₁ σ : ℂˣ)) ∧
        ∀ (σ : L ≃ₐ[K] L) (X : ℝ), bigQ K L ^ c₂ ≤ X →
          |(Module.finrank K L : ℝ) * piC L σ X - (Li X - θ σ * Li (X ^ β))| ≤
            C * (Real.exp (-(c₃ * Real.log X / Real.log (bigQ K L))) +
              Real.exp (-(Real.sqrt (c₃ * Real.log X) / Real.sqrt (Module.finrank ℚ K)))) * (Li X - θ σ * Li (X ^ β))

def QB : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
    2 ≤ bigQ K L → ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (β : ℝ), χ ^ 2 = 1 → β < 1 → HeckeZero L χ β →
      c / bigQ K L ^ 2 ≤ (1 - β) * Real.log (bigQ K L)

def RayField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

end GlobalTheory.NT

end
