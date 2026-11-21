import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality

open Formalism.MainNotions.S GlobalTheory.Count

def SatIn (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun _ hy => hy.1
  · intro y hy
    refine Submodule.subset_span ⟨hy, fun s hs => ?_⟩
    rw [Submodule.mem_bot] at hs
    subst hs
    simp [Formalism.UG.hform]

end GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality
