import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Mod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def toO (M : Model F E) : 𝒪[F] →+* M.L.O where
  toFun x := ⟨algebraMap F E (x : F), (M.L.O_def _).2 (isIntegral_algebraMap (x := x))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma toO_coe (M : Model F E) (x : 𝒪[F]) : ((toO M x : M.L.O) : E) = algebraMap F E (x : F) := rfl

variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

def bbMod (t : Term V M r) : Module 𝒪[F] (BB H t) := Module.compHom _ (toO M)

end Mod

end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Q

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

abbrev satQ (Λ : Submodule M.L.O V) {ι : Type} (v : ι → V) : Submodule M.L.O V :=
  Λ ⊓ (Submodule.span E (Set.range v)).restrictScalars M.L.O

end Q

def HaarIdx : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ δ : 𝒪[F], δ ≠ 0 → M.modK (algebraMap F E (δ : F)) * (Nat.card (M.L.O ⧸ Ideal.span {toO M δ}) : ℝ) ≤ 1

def ModLe : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ x ∈ M.R, M.modK x ≤ 1

def InR : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ y : 𝒪[F], algebraMap F E (y : F) ∈ M.R

end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict



end PI.NGStepBBW
end
end

section
noncomputable section

open ValuativeRel Topology

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc


end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel MeasureTheory

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict


section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem R_eq_O_of_none {M : Model F E} (h : M.split = none) : M.R = M.L.O := by
  unfold Model.R
  rw [h]






end Split

def LocOOpen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), IsOpen (L.O : Set E)




end PI.NGStepBBW
end
end
