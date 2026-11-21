import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramAtP

noncomputable section
namespace GlobalTheory.Core.Rk.IP.FockModel
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem resEta_one_dbl (A : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) : ResEta D 1 (dblSp A).rank :=
  ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (A.rank + A.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def Hyp (A B : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B) (a : GL (Fin A.rank) (AE D))
    (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (mH : Measure (GA D B)) (φ : WO (dblSp A) B → ℂ),
    IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ IsMaj A a ∧ IsInfFam θ ∧
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) ∧
    IsCovolOne (ratL B A) ν 𝓕 ∧ mH.IsHaarMeasure ∧ IsFockVec ψ θ (dblSp A) B sS sB φ ∧ swSec A B omh ν 𝓕 φ 1 = 1

theorem hyp (A B : HSp D) (hA : HSpace.SigOK A) (hB : HSpace.SigOK B) (ha : 1 ≤ A.rank) (hab : A.rank < B.rank) :
    Hyp A B := by
  obtain ⟨ψ, θ, χA, χB, sA, sB, cA, a, om, ν, 𝓕, Φ, hP, hΦ, h1, -⟩ := Model.exists_pair_unram A B hA hB ha
    (t := B.rank - A.rank) (by omega) (by omega) _ _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat B)
  obtain ⟨-, -, -, hθ, -, -, hsA, hsB, -⟩ := hP.setting
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨omh, homh⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hP.weil.std (dblSp A) B 1 χB ⟨η, hη⟩
    ⟨continuous_const, fun _ => rfl⟩ hP.weil.hecT (resEta_one_dbl A hP.weil.resT) hP.weil.resT
  obtain ⟨c1, c2⟩ := Cartan.cartan_dbl D θ A sA a hθ hsA hP.maj_eq
  refine ⟨ψ, χB, omh, a, θ, _, sB, ν, 𝓕, Measure.haar, delta A B Φ Φ, homh, hP.maj, hθ, c1, hsB, c2, hP.covol,
    inferInstance, GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ A B sA sB hP.weil.std hθ Φ Φ hΦ hΦ, ?_⟩
  have e1 : omh (1, 1) = 1 := map_one omh
  have e2 : om (1, 1) = 1 := map_one om
  simp only [wcoef, e2, Module.End.one_apply] at h1
  simp only [swSec, e1, Module.End.one_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta, h1]




end GlobalTheory.Core.Rk.IP.FockModel

end
