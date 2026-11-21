import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfTriangleInequality
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.TheoremCountStatementOfGeometry
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfEnd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FfHasInfChar

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def ffg_IsSq {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ IsURepOn (UJset ε) σ' ∧ IsIrredOn (UJset ε) σ' ∧ IsSqIntOn ε σ'

def ffg_Equiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

def QOrth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ffg_IsSq ε σ' → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ' d) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
      (H'' : Type) [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [CompleteSpace H'']
      (σ'' : Matrix (Fin n) (Fin n) ℂ → (H'' →L[ℂ] H'')), ffg_IsSq ε σ' → ffg_IsSq ε σ'' → ¬ ffg_Equiv ε σ' σ'' →
      ∀ (a b : H') (a' b' : H''), ∫ g, coefOn σ' a b g * star (coefOn σ'' a' b' g) ∂(Formalism.REAL.muG ε) = 0

def FCharOther (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε) ≠ 0 → ff_HasInfChar ε π' (χ n lam)

def FKTypeOther : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∫ g, ⟪x, Ψ (umat g) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε) ≠ 0 →
      ∃ S : Submodule ℂ H', IsKTypeOf ε π' (Formalism.QuantumDeterminants.lowK ε lam) S

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool}




def ffg_CoefOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ v w : H, φ = coefOn σ v w

def ffg_Other {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H') (_ : CompleteSpace H')
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (v w : H'),
    ffg_IsSq ε σ' ∧ ¬ ffg_Equiv ε σ' σ ∧ φ = coefOn σ' v w





end SlopeTestRemainingChoices



end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FConvEig (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ → ff_DSSum ε Ψ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), ffg_IsSq ε π' → ∀ (x y : H) (a b : H'),
      ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
        (∀ g₀ : Formalism.REAL.UJ ε, F (umat g₀) =
          ∫ g, ⟪x, Ψ (umat (g * g₀)) y⟫_ℂ * star (coefOn π' a b g) ∂(Formalism.REAL.muG ε)) ∧
        ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = χ n lam k * F g

section Congr

variable {n : ℕ} {ε : Fin n → Bool}

end Congr

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def VolumeCountGeometryConditions (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.FinVol ∧ AllCount X (2 * (X.I.n : ℝ) ^ 2) ∧ GeoS X cε Cv Cd Cq



def Rest (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  (FPsiEig χ ∧ FConvEig χ ∧ QOrth ∧ QInfChar ∧ QClass χ) ∧ cu_StepsEnd n₀ A 46 ∧ DistTri ∧
    VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq

end Formalism.MainNotions.LeviCoordinates
end
end
