import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SmoothCartan
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic MeasureTheory
open scoped Matrix ComplexOrder

namespace GlobalTheory.Mt

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

namespace CartanData

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

def IsAdm {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i j, D.lie.IsSmoothFun (F := ℂ) fun g => ξ g i j) ∧
  ∃ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef ∧ (∀ X ∈ D.p, Q * D.dξ ξ X = (D.dξ ξ X)ᴴ * Q) ∧
    ∀ X ∈ D.k, Q * D.dξ ξ X = -((D.dξ ξ X)ᴴ * Q)

def repξ (Γ : Subgroup G) {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ Γ (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toRingEquiv.toMonoidHom.comp
    (ξ.comp Γ.subtype)

def MatsushimaLattice : Prop :=
  ∀ (Γ : Subgroup G) [DiscreteTopology Γ] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant], CompactSpace (GlobalTheory.AutomorphicL2Unitary.Quot Γ) →
  ∀ (π : UnitaryRep G (GlobalTheory.AutomorphicL2Unitary.L2 Γ μ)), (∀ g, (π.toHom g : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ →L[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) = GlobalTheory.AutomorphicL2Unitary.R Γ μ g) →
  ∀ (d : ℕ) (ξ : G →* Matrix (Fin d) (Fin d) ℂ), D.IsAdm ξ →
  ∀ q, Nonempty (groupCohomology (Rep.of (repξ Γ ξ)) q ≃ₗ[ℂ] D.HGK π ξ q)

end CartanData

end GlobalTheory.Mt
