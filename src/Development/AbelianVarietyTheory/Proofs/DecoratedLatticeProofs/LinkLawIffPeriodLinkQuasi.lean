import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.QuasiFamilyPeriods
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMapStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApplyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBounded

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct ENNReal NNReal ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods (conjTr JacobiConj PeriodsAgree PeriodLink PeriodLinkQuasi)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
  {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}

def form (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (F : WO B.V₀ J.W₀ → ℂ) : ℂ :=
  ∫ h₀ in B.vA.𝓕, φ h₀ * s.om₀ (B.o.emb (h₀, 1), 1) F 0 ∂B.vA.μ

theorem heisO_heisO (S T : HSp D) (x y : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y F) = ψ (symplOH S T x y) • heisO ψ S T (x + y) F := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_left,
    AddChar.map_add_eq_mul, add_assoc]
  ring

end GlobalTheory.LinkCompare

end
