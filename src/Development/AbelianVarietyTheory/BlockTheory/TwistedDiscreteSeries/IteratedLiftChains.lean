import Mathlib
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

def cuspidalL2Subspace : Submodule ℂ (DividedPowerChartLift V ν) :=
  (Submodule.span ℂ {x | ∃ (φ : GA D V → ℂ) (h : MemL2Quotient (GQ V) ν φ),
    IsAutFun V φ ∧ IsCuspFun V φ ∧ x = h.toL2}).topologicalClosure

def IsCuspIrr (W : Submodule ℂ (DividedPowerChartLift V ν)) : Prop := IsIrredSubrep (RG V ν) W ∧ W ≤ cuspidalL2Subspace V ν

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}

def locRep (hW : IsCuspIrr V ν W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Representation ℂ (GLoc D.sp.cm.sig V.gram v) W :=
  ((ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := W)).toMonoidHom.comp hW.1.1.rep).comp
    (emb D.sp.cm.sig V.gram v)

def SphAt (hW : IsCuspIrr V ν W) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  GlobalTheory.LGrp.IsSpherical (locRep hW v) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)

variable (W) in

def HasRealType (θ : InfFam D) (S : D.what₂.Tau → SPar) : Prop :=
  ∃ M : DSModel V S, ∀ τ, ∃ A : M.H τ →L[ℂ] DividedPowerChartLift V ν, A ≠ 0 ∧ (∀ x, A x ∈ W) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x, A (M.rep τ g x) = RG V ν (atTau θ V τ g) (A x)

end Cusp

def IsAdmDatum (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (Φ : WO A B → ℂ) : Prop :=
  IsThetaFunO ψ A B Φ ∧
    IsLatVac (heisO ψ A B) (latO A B (L0c D A) (L0c D B) fun v => ¬ IsSplit (E := D.host.E) v) Φ

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

inductive IsIterLift : ∀ k, (GA D (Yc D k) → ℂ) → Prop
  | base {f : GA D (Yc D 0) → ℂ} (hf : IsAutFunSm θ (Yc D 0) f) (h : MemL2Quotient (GQ (Yc D 0)) (ν 0) f) (hσ : h.toL2 ∈ σ) :
      IsIterLift 0 f
  | step {k : ℕ} {u : GA D (Yc D k) → ℂ} (hu : IsIterLift k u) {Φ : WO (Yc D k) (Yc D (k + 1)) → ℂ}
      (hΦ : IsAdmDatum ψ (Yc D k) (Yc D (k + 1)) Φ)
      (hi : ∀ h, IntegrableOn (fun g => th k g h Φ * u g) (𝓕 k) (ν k)) :
      IsIterLift (k + 1) fun h => ∫ g in 𝓕 k, th k g h Φ * u g ∂ν k

end Chain

example : (4 : ℂ) ∈ excluded 4 3 := Or.inl (by norm_num)

example {C : Type} [CommGroup C] (μ : ℕ → C) (η : C) :
    (chrStep μ η 1).2 = μ 1 ∧ (chrStep μ η 2).2 = μ 2 * η⁻¹ := by
  constructor <;> simp [chrStep, Nat.odd_iff]

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
