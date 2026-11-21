import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Saturated

section FrameFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) : frame (mapLF γ (lf D F)) a = γ (F.fvec a) := by
  unfold mapLF
  rw [dif_pos hγ]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]

theorem zt_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) : (mapLF γ (lf D F)).zt = γ F.z := by
  unfold mapLF
  rw [dif_pos hγ]

theorem Xflag_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (j : ℕ) :
    Xflag (mapLF γ (lf D F)) j = (Xflag (lf D F) j).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  unfold mapLF
  rw [dif_pos hγ]
  show Submodule.span D.host.E ((fun a => γ (F.e a)) '' {i | i.1 < j}) =
    Submodule.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (Submodule.span D.host.E (F.e '' {i | i.1 < j}))
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem one_mem_NLam {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, gmap_one_sat Λ⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _
  · show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _

end FrameFix

end Formalism.L2.SG.Pf.Act
