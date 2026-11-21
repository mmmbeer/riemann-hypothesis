import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

noncomputable section

open NumberField GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.Published.AutFinGL.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}




def kerL (a : ℕ) (χ : HChar E) : Subgroup (GL (Fin a) (Af E)) := ((chiDet a χ).comp (finGL E a)).ker

theorem isOpen_kerL (χ : HChar E) : IsOpen (kerL a χ : Set (GL (Fin a) (Af E))) := isOpen_ker_chiDet χ

def kRep (a : ℕ) (χ : HChar E) : Representation ℂ (Kinf E a) ℂ :=
  twRep (Representation.trivial ℂ (Kinf E a) ℂ) ((chiDet a χ).comp ((infGL E a).comp Unitary.toUnits))

end GlobalTheory.Published.AutFinGL.Model

end
