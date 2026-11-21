import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FamilySizeBound

noncomputable section

namespace GlobalTheory.DataRowsCounterexample

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.FamilySizeBound

theorem places_nonempty (D : D7) : Nonempty D.what₂.Tau ∧ Nonempty D.what₂.Word :=
  ⟨⟨D.eTau.symm 1⟩, ⟨D.u₀⟩⟩

end GlobalTheory.DataRowsCounterexample
