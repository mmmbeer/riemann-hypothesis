import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ipO {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f f' : WO S T → ℂ) : ℂ :=
  ∫ w in 𝓕, f w * starRingEnd ℂ (f' w) ∂μ

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ x, ‖ψ x‖ = 1) →
    ∀ f, IsThetaFunO ψ S T f → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL T S) 𝓕 μ → MemLp f 2 (μ.restrict 𝓕)

def IsRealFrame {S T : HSp D} {k : ℕ} (L : (Fin k → ℝ) →+ WO S T) : Prop :=
  Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧ ∀ w : WO S T, w.map (finPart D) = 0 → ∃ t, L t = w

def dH (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {k n : ℕ} (L : (Fin k → ℝ) →+ WO S T) (l : Fin n → Fin k)
    (f : WO S T → ℂ) (w : WO S T) : ℂ :=
  iteratedFDeriv ℝ n (fun t : Fin k → ℝ => heisO ψ S T (L t) f w) 0 (fun i => Pi.single (l i) 1)

def sobO (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {k : ℕ} (L : (Fin k → ℝ) →+ WO S T) (N : ℕ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ l : Fin n → Fin k, Real.sqrt (∫ w in 𝓕, ‖dH ψ L l f w‖ ^ 2 ∂μ)

end Formalism.IndefR.Eqv

end
