import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

theorem closed_CH (𝒞 : FamClass) : Closed 𝒞 fun _ CH => 0 < CH := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  have h : (1 : ℝ) ≤ CH := hL.2.2.1 CH (by simp [Formalism.MainNotions.FamP.cMid])
  linarith

theorem settingF_pk {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) : SettingEventually Fm := by
  obtain ⟨x0, h⟩ := J.setting_fam Fm hT
    ⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩
  exact ⟨x0, fun x hx _ i u => h x hx i u⟩

structure FamGL (𝒞 : FamClass) (C0 eL C3 crystallineComparison C22 : ℝ) : Prop where
  s59 : Closed 𝒞 fun Fm _ => ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i)
  s22 : Closed 𝒞 fun Fm _ => TaylorLogMetric.StatementFamilyConstant Fm C22
  s23 : Closed 𝒞 fun Fm _ => flipTwoThree.KudlaFamilyStatement Fm
  s24 : Closed 𝒞 fun Fm _ => StandardLattice.KudlaFamilyStatement Fm C3
  s10 : Closed 𝒞 fun Fm _ => product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison
  provedFourF : Closed 𝒞 fun Fm _ => LocalQuadraticParts.SlopeLemmaFamily Fm
  provedFiveF : Closed 𝒞 fun Fm _ => LocalQuadraticParts.SlopeLossFamily Fm eL
  hF3 : Closed 𝒞 fun Fm _ => StandardLattice.FamilyTheoremThreeAdmitted Fm
  tVol : Closed 𝒞 fun Fm _ => StandardLattice.TiesF Fm
  tOm : Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)
  tFree : Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), ThFree (Fm.D x i)
  tTh : Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22
  t7 : Closed 𝒞 fun Fm _ => flipTwoThree.admF7 Fm
  tCV : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)
  t10 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u


end Formalism.MainNotions.Pk

end
