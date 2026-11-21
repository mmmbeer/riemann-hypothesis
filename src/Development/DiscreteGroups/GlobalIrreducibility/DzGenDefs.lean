import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace DiscreteGroups.sglob.DzType

def eOne (m : ℕ) : (Σ _ : Fin m, Fin 1) ≃ Fin m := Equiv.sigmaUnique (Fin m) fun _ => Fin 1

def psOne (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :=
  parInd (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))

def GenA : Prop :=
  GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ),
      (psOne k m).IsIrreducible ∧ IsSpherical (psOne k m) ∧ HasCentralChar (psOne k m) 1

end DiscreteGroups.sglob.DzType
