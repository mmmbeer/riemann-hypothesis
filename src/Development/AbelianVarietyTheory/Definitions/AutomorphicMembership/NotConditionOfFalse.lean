import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCoordPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBaseStatement

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain



theorem prePin_coordPre (P : PreCh) (L : LevCh P) : PrePin (GlobalTheory.StdFrameObj.coordPre P L) :=
  fun a b h => PinsCoord.extTo_basis _ _ a b h

theorem ksCond (hR : GlobalTheory.NT.RayField) (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    V4.KsCond fun B f => ∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f := by
  refine ⟨InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := Fld.nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.T.rayField_le_and_exists_base hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

theorem baseCond_KPx (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField) (hP : GlobalTheory.Published.PrincipalIdealSt)
    (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) : BaseCond KPx :=
  baseCond_of (PP := fun P _ => PrePin P) (ksCond hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      have hO : K.Over (GlobalTheory.StdFrameObj.coordPre K.P K.Lv) :=
        ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩
      obtain ⟨f⟩ := (hfr _ hO).2
      exact ⟨_, f, hO, prePin_coordPre _ _⟩)




end GlobalTheory.Mem.Top.Bl.Model

end
