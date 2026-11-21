import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ContinuousCoB
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Filter

namespace Formalism.IndefR.Fin.DL



end Formalism.IndefR.Fin.DL

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction Formalism.IndefR.Fin.U1
  MeasureTheory IsDedekindDomain NumberField Topology

namespace Formalism.IndefR.Fin.DL

set_option synthInstance.maxHeartbeats 80000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cUD (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (cA D).toMonoidHom

@[simp] theorem cUD_val (x : (AE D)ˣ) : ((cUD D x : (AE D)ˣ) : AE D) = cA D (x : AE D) := rfl

def hq (D : D7) : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / cUD D

section Inv

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0)

include hδ hδ0 in
theorem cA_cA (y : AE D) : cA D (cA D y) = y := by
  rw [← pt_co δ hδ hδ0 y, cA_pt δ hδ, cA_pt δ hδ, neg_neg]

end Inv

section Coord

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

end Coord

end Formalism.IndefR.Fin.DL

namespace Formalism.IndefR.Fin

open Formalism.IndefR.Fin.DL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Formalism.IndefR.Fin

end
end
