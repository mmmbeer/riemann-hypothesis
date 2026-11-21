import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def embI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank) : WO S T :=
  HMul.hMul (C.map (incA D)) a

def ellI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : ℂ :=
  ∫ a in 𝓕, f (embI S T C a) ∂μ

def IsPerpI (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * x = 0

end Formalism.IndefR.Eqv

end
