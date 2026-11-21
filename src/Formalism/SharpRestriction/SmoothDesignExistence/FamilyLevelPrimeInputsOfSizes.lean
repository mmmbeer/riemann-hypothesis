import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLc
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLe
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLf
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLn
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSl
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaa
import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVi
import Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVq
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.Divisibility.SlopeExcess.ExcSplitOfGMod
import Formalism.SharpRestriction.SmoothDesignExistence.WithSmOfWithCh
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLw

section
noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Family

variable {eps : ℝ} (Fm : FamP eps)




def LevelPrimeItems (crystallineComparison : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), product_first_zeroth_parts.HidaSetting (Fm.D x i) u →
    product_first_zeroth_parts.Conclusion2 (Fm.D x i) u ∧ product_first_zeroth_parts.Conclusion5 (Fm.D x i) u crystallineComparison ∧ product_first_zeroth_parts.Conclusion6 (Fm.D x i) u ∧ product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u




structure ExtC (C3 crystallineComparison : ℝ) : Prop where

  linkG : LinkG Fm

  g69 : AuxBlock8.ConclusionOnFamily Fm Fm.GK Fm.Gx
  localLemmaThreeThreeTwo : CornerGLContinuity.FamilyOrdersLargePrimeBoundConstant Fm
  g32 : CornerGLContinuity.FamilyBadPrimeBound Fm
  gTauSz : CornerGLContinuity.FamilyCutSizes Fm
  gTa : CornerGLContinuity.FamilyWeightSumBound Fm
  n33 : ArithmeticCylinders.FamilyExpDeficitBound' Fm

  gl23 : flipTwoThree.ConclusionF5 Fm ∧ flipTwoThree.ConclusionF6 Fm

  gl24 : StandardLattice.FamilyPartFour Fm C3 ∧ StandardLattice.PartFiveFamilyBounds Fm

  gl10 : LevelPrimeItems Fm crystallineComparison
  nuFull : NuFullF Fm

  n56 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∃ (HW : HWOf (Fm.D x i).loc)
    (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (Cm : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F),
    DeltaInvariantLattices.aux₃ (Fm.D x i) HW F Cm ∧ DeltaInvariantLattices.ConclusionE (Fm.D x i) HW F

structure BrC : Prop where

  colVal : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)
  br25 : ∃ C0 : ℝ, ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, J.RankHyp (Fm.D x i) ∧
    ∃ Δ : ℝ, StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ (fun j ρ => wSz (Fm.D x i) (j + 1) ρ)

variable {Fm}


end Family

end Formalism.MainNotions.Pk

end
end

section
noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Family

variable {eps : ℝ} (Fm : FamP eps)

structure BrT : Prop where

  t5Tw : DIV.Ev Fm fun x hx i => J.LevelPrimeColumnOtherTuples (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

  tg : DIV.Ev Fm fun x _ i => WeightDegreeSizes.LevelPrimeNotTypePrime (Fm.D x i)

variable {Fm}


theorem servedModel_of_params {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (X : G.Inst D L) (K : G.Consts)
    (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) : WeightDegreeSizes.ServedHasModel X K := by
  intro u w hw hVV
  have hc : G.Cand D L K (D.what₂.places.resChar w) := by
    by_contra hn
    apply hVV
    unfold G.VV
    rw [if_neg (fun h => hn h.1)]
  exact gIdx_of_cand P K h3 u _ hc hw






end Family

end Formalism.MainNotions.Pk

end
end
