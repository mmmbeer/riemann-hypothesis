import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.UpNonzero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)
open GlobalTheory.LFun (Fam twist segFam seg val above IsCont Bounded IsSysParamD IsParamFunV UnrAt)
open GlobalTheory.CompanionTheory.OntoAll

namespace GlobalTheory.CompanionTheory.Ipf.Aut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ReachOrth : Prop :=
  ∀ (c₁ c₂ : EigSys D) (B₁ B₂ : Fam D.host.E), IsSysParamD D (badPl R A.μ0) D.R.r c₁ B₁ →
    IsSysParamD D (badPl R A.μ0) D.R.r c₂ B₂ → (∃ w ∉ badE R, B₁ w ≠ B₂ w) →
    (∀ k, k < D.R.m → ∀ u₁ ∈ reachedAll R c₁ k, ∀ u₂ ∈ reachedAll R c₂ k, IsIP R A.μ0 k u₁ u₂ 0) ∧
    ∀ u₁ ∈ reachedAll R c₁ (D.R.m - 1), ∀ u₂ ∈ reachedAll R c₂ (D.R.m - 1), ∀ x₁ x₂,
      IsUpTop R A.μ0 u₁ x₁ → IsUpTop R A.μ0 u₂ x₂ → ⟪x₁, x₂⟫_ℂ = 0

end GlobalTheory.CompanionTheory.Ipf.Aut

end
