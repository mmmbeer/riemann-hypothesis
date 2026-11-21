import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.UpNonzero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Doubling (io hgt flat zetaA ZetaConvA IsMaj dblSp Khat HasIwasawa degPS)
open GlobalTheory.FinZeta (projV embV Kv Gv IsLocKer VacFin bddAut)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction (ofFr ipTh ptAt actSrc actTgt IsJoint UnitHighest kfin alS alT NodeGap)
open GlobalTheory.AdelicScalar (l2)
open scoped InnerProductSpace GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.CompanionTheory.Ipf.Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FPl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

def infJ (V : HSp D) (J : Subgroup (GA D V)) : Set (GA D V) := {g | ∃ k ∈ J, g * k⁻¹ ∈ GinfC V}

structure IsLevelS (V : HSp D) (Sb : Finset (FPl D)) (J : Subgroup (GA D V)) : Prop where
  fin : J ≤ GfC V
  compact : IsCompact (J : Set (GA D V))
  isOpen : IsOpen (infJ V J)
  split : ∀ g ∈ GfC V, g ∈ J ↔ (∃ k ∈ J, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v

section Real

variable {V : HSp D} {PS : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V PS)

end Real

structure IsStep (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) {PS PT : D.what₂.Tau → SPar} (M : DSModel S PS) (M' : DSModel T PT)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Sb : Finset (FPl D)) (f₀ fF : WO S T → ℂ) : Prop where
  weil : IsWeilDatumO ψ S T χS χT om
  inf : IsInfFam θ
  parS : PS = parB (Ptw D) k
  parT : PT = parB (Ptw D) (k + 1)
  expo : ∀ τ, HasInfExp D χS τ (alS D k τ) ∧ HasInfExp D χT τ (alT D k τ)
  rank : T.rank = S.rank + D.R.t
  noQ : LS.Q = ∅
  places : ∀ v, v ∈ Sb ↔ ∃ PP ∈ LS.Pg, PP.under (𝓞 D.host.F) = v
  frameS : ∃ N : ℕ, Lev.IsBaseFrame S βS ΛS N ∧ ∀ v : FPl D, (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ Sb
  frameT : ∃ N : ℕ, Lev.IsBaseFrame T βT ΛT N ∧ ∀ v : FPl D, (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ Sb
  vec : IsStepVecOf ψ θ S T (cart M) (cart M') ΛS ΛT βS βT LS χj ∅ (fun _ => 1) f₀ fF
  unr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → GlobalTheory.LFun.UnrAt χS w ∧ GlobalTheory.LFun.UnrAt χT w
  tame : ∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP χS (χj PP) (-1) ∧ Formalism.IndefR.Fin.TameAt e PP χT (χj PP) (-1)

open GlobalTheory.LFun Formalism.UG in

def SumGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (z : ℂˣ) (X : ℂ)
    (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → ‖X‖ * (qV E w : ℝ) ^ (r - 1) < 1 →
    (∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      ∀ k₁ ∈ KGL w r, ∀ k₂ ∈ KGL w r, φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * X ^ (∑ i, |d i|).toNat) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ),
      IsSatVecGL w ρ x B →
      (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) →
      ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) →
        HasSum (fun y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => φ y.out * ℓ (ρ y.out x))
          (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) *
            eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) *
            (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x)

open GlobalTheory.LFun Formalism.UG in

def SumU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r : ℕ),
    IsUnramInv ϖ σ q → ∀ (X : ℂ) (φ : GU σ r → ℂ), ‖X‖ * (q : ℝ) ^ (2 * (r - 1)) < 1 →
    (∀ (d : Fin r → ℤ) (t : GU σ r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ r, ∀ k₂ ∈ KU σ r,
      φ (k₁ * t * k₂) = X ^ (∑ i, max (d i) 0).toNat) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ),
      IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) →
        HasSum (fun y : GU σ r ⧸ KU σ r => φ y.out * ℓ (ρ y.out x))
          (eulerFac (GlobalTheory.LGrp.bcParam r α) ((q : ℂ) ^ (r - 1) * X) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * X)) * ℓ x)

end GlobalTheory.CompanionTheory.Ipf.Loc

end
