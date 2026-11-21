import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.PeriodIntegrals.AdelFinVol
import Formalism.PeriodIntegrals.AdelClassFin
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.PublishedAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StrongApproxSU (D : D7) : Prop :=
  ∀ V : HSp D, 2 ≤ V.rank → ∀ e : AE D, IsSplitIdem D e → ∀ g : GA D V, (mt V g).det = 1 →
    g ∈ closure {x : GA D V | ∃ γ ∈ GQ V, (mt V γ).det = 1 ∧
      ∃ h : GA D V, (mt V h).det = 1 ∧ SuppAt e V h ∧ x = γ * h}

variable {D : D7}

def AtTauExists (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∀ τ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) → ∃ x, IsAtTau θ V τ g x

theorem atTauExists_of {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (V : HSp D) :
    AtTauExists θ V := by
  intro τ g hg
  obtain ⟨x, hx, -⟩ := Formalism.IndefR.Eqv.atTauExUnique_holds (D := D) θ hθ V τ g hg
  exact ⟨x, hx⟩

end Formalism.IndefR.PublishedAut

end
