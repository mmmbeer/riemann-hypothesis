import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions

open Finset Module NumberField Formalism.HN

noncomputable section

namespace Formalism.L2.Indef.Tree

def addY (C2 : ℝ) (P : SlopeBoundParameters) : ℝ := C2 * P.f * P.m * P.b * Real.log P.x

section Leaves

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

end Leaves

end Formalism.L2.Indef.Tree
