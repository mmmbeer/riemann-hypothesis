import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces

section
noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW

def FirstTermWeak : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t), T.rank + T'.rank = 2 * A.rank → T'.rank < T.rank → 0 < T'.rank →
  ∀ (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ)) (ω' : GA D (dblSp A) × GA D T' →* Module.End ℂ (WO (dblSp A) T' → ℂ)), IsWeilDatumO ψ (dblSp A) T 1 χ ω → IsWeilDatumO ψ (dblSp A) T' 1 χ ω' →
  ∀ (a : GL (Fin A.rank) (AE D)) (b : GL (Fin T.rank) (AE D)), IsMaj A a → IsMaj T b → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → HasIw d (Kmax T b) →
  ∀ (μ₀ : Measure (WO A T)) (𝓕₀ : Set (WO A T)), IsCovolOne (ratL T A) μ₀ 𝓕₀ →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (sS : RealMat (dblSp A)) (sT : RealMat T), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) → (IsAniso T' ∨ ∃ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r') (b' : GL (Fin T'.rank) (AE D)), IsAniso T₀ ∧ 0 < r' ∧ IsMaj T' b' ∧ HasIw d₀ (Kmax T' b')) →
  ∀ φ, IsFockVec ψ θ (dblSp A) T sS sT φ → IsKFinVec ω (Khat A a) φ →
    ∃ (Ψ : WO (dblSp A) T' → ℂ) (B : GA D (dblSp A) → ℂ), IsThetaFunO ψ (dblSp A) T' Ψ ∧ IsKFinVec ω' (Khat A a) Ψ ∧ (∃ (E : GA D T' → ℂ → ℂ) (c : ℂ → ℂ) (s₀ : ℂ) (σ : ℝ), (∀ s : ℂ, σ < s.re →
  ∀ g, ThetaPairConv ω' m Ψ (fun h => E h s) g) ∧
      ∀ g, ResidueAt (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) s₀ (B g)) ∧
      EisCoeffAt A (flat A a (swSec A T ω μ₀ 𝓕₀ φ) (sZero A T)) (sZero A T) (-1) B

end GlobalTheory.RegSW

end
end

section
noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.OrthSumSp (posSp hypSp hypSumDec posSp_sigOK hypSp_sigOK)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW.WeakModel

variable {D : D7}

def IsPairRes {S T' : HSp D} (ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (m : Measure (GA D T'))
    (Ψ : WO S T' → ℂ) (B : GA D S → ℂ) : Prop :=
  ∃ (E : GA D T' → ℂ → ℂ) (c : ℂ → ℂ) (s₀ : ℂ) (σ : ℝ), (∀ s : ℂ, σ < s.re → ∀ g, ThetaPairConv ω' m Ψ (fun h => E h s) g) ∧
    ∀ g, ResidueAt (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) s₀ (B g)

def Met (A T T' : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ))
    (ω' : GA D (dblSp A) × GA D T' →* Module.End ℂ (WO (dblSp A) T' → ℂ)) (a : GL (Fin A.rank) (AE D))
    (μ₀ : Measure (WO A T)) (𝓕₀ : Set (WO A T)) (m : Measure (GA D T')) (φ : WO (dblSp A) T → ℂ),
    IsWeilDatumO ψ (dblSp A) T 1 χ ω ∧ IsWeilDatumO ψ (dblSp A) T' 1 χ ω' ∧ m.IsHaarMeasure ∧ IsCovolOne (ratL T A) μ₀ 𝓕₀ ∧
    swSec A T ω μ₀ 𝓕₀ φ 1 = 1 ∧
    ∃ (Ψ : WO (dblSp A) T' → ℂ) (B : GA D (dblSp A) → ℂ), IsThetaFunO ψ (dblSp A) T' Ψ ∧ IsKFinVec ω' (Khat A a) Ψ ∧
      IsPairRes ω' m Ψ B ∧ EisCoeffAt A (flat A a (swSec A T ω μ₀ 𝓕₀ φ) (sZero A T)) (sZero A T) (-1) B


theorem isAniso_pos (D : D7) (n : ℕ) : IsAniso (posSp D n) :=
  GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite _ (posSp_sigOK D n) fun _ => .inl rfl



end GlobalTheory.RegSW.WeakModel

end
end
