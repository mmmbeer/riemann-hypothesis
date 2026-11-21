import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Obj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def IsSelfDual (H : HermSp M V) (Λ : Submodule M.L.O V) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set V) = ⊤ ∧ ∀ v : V, v ∈ Λ ↔ ∀ w ∈ Λ, H.h v w ∈ M.L.O

def Sig (H : HermSp M V) {r : ℕ} (t : Term V M r) (Mh : Submodule M.L.O V) : Set (Submodule M.L.O V) :=
  {Λ | IsSelfDual H Λ ∧ Λ ⊓ (ME H t).restrictScalars M.L.O = Mh}

end Obj

end PI.SelfDualHermitianLattices
