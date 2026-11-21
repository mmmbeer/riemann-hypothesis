import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def LocPosC : Prop :=
  ∀ v, 0 < MX X u u' ψ v ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v ∧ 0 < jacX X v

def AlConvC : Prop :=
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1

end Formalism.L2.SG.Pf.ProdConvCut

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

end Formalism.L2.SG.Pf
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def VolOneAEC : Prop :=
  {v : PlX X | ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧ (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)}.Finite

def MXAE : Prop := {v : PlX X | MX X u u' ψ v ≠ alX X u u' v}.Finite



end Formalism.L2.SG.Pf.ProdConvCut2
end
end
