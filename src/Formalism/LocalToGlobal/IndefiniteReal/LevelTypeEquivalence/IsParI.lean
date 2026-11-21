import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsParI (T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (m : GA D T) : Prop :=
  (∃ a : Matrix (Fin r) (Fin r) (AE D),
      HMul.hMul (Formalism.L2.Theta.mt T m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a) ∧
    ∀ x : Fin T.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram).mulVec x = 0 →
      ∃ b : Fin r → AE D, (Formalism.L2.Theta.mt T m).mulVec (fun i => incA D (x i)) - (fun i => incA D (x i)) =
        (C.map (incA D)).mulVec b

end Formalism.IndefR.Eqv

end
