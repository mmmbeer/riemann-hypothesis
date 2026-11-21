import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.HermitianColumns.StarConj
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfFlags
import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime
import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfHermitian
import Formalism.LocalToGlobal.GlobalTheory.GL1.AdelicLatticeLinkFamily
import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk NumberField

structure GlobalObj (D : D7) where

  host : Formalism.L2.Host.HostTied D

  herm : Formalism.L2.Herm.FullTied D

  forms : ∀ u : D.what₂.Word, Formalism.L2.Forms.FormsTied D u

structure CurveObj (D : D7) where
  δ : ℂ
  delta_pow_twelve_eq_discr : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ
  χ : TaylorLogMetric.IdE D → ℂ
  chi : TaylorLogMetric.IsChi D χ
  e : TaylorLogMetric.FamE D
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  eL : D.what₂.LL ≃+* M
  emb : ∀ y, ((eL y : M) : ℂ) = D.what₂.embLL y
  d : D.what₂.Tau → M
  gen : ∀ τ, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {d τ}

attribute [instance] CurveObj.nf

structure GlobalObjF {eps : ℝ} (Fm : FamP eps) where
  T : ∀ x (i : Fm.Ix x), GlobalObj (Fm.D x i)
  K : ∀ x (i : Fm.Ix x), CurveObj (Fm.D x i)

structure CurveTies (D : D7) (K : CurveObj D) : Prop where
  om : ∀ τ (s : D.what₂.LL →+* ℂ), D.gx.Om τ s =
    (Real.pi * ‖conjOf K.eL s (K.d τ)‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)))⁻¹
  thOne : ∀ s : D.what₂.LL →+* ℂ, ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)) G ∧
    D.gx.thOne s ^ 2 = normSq1 (TaylorLogMetric.lamConj K.M (conjOf K.eL s) (TaylorLogMetric.lamOf D D.host.ccK K.δ)) G
  thFree : ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (c : (D.mem u).C.cls i) (c' : (D.mem u).C.cls (i + 1)),
    ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
      TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧ TaylorLogMetric.CoefIn D (K.e (D.R.N i) (D.R.N (i + 1)) L L') K.M ∧
      ∀ s : D.what₂.LL →+* ℂ,
        (D.fm u).thFree i s c c' ^ 2 = normConj D K.δ K.e K.M (conjOf K.eL s) (D.R.N i) (D.R.N (i + 1)) L L'

structure GlobalTiesF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) : Prop where
  real : ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)
  curve : ∀ x (i : Fm.Ix x), CurveTies (Fm.D x i) (O.K x i)
  extra : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.Herm.ExtraTied (O.T x i).herm (Fm.ex x hx i)

structure GlobalChoicesF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) : Prop where
  dataIn : ∀ x (i : Fm.Ix x), TaylorLogMetric.DataIn (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK (O.K x i).δ) (O.K x i).M
  kRat : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, flipTwoThree.adm7 (Fm.D x i)

structure CurveClaims (D : D7) (C : ℝ) (K : CurveObj D) : Prop where
  cl22 : Cl22 D C D.host.ccK K.δ K.χ K.e
  thPow : GL3Theta.thPow D D.host.ccK K.δ K.e

structure PendClaims (D : D7) : Prop where

  colVal : flipTwoThree.adm3 D → ∀ u, Nonempty (flipTwoThree.ColVal D u)

  UpDownIncidenceInverse : ∀ u, product_first_zeroth_parts.UpDownIncidenceInverse D u

  admT : ∀ u, product_first_zeroth_parts.admT D u

  br : ∀ u, ∃ P : product_first_zeroth_parts.Pend D u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

structure GlobalClaimsF {eps : ℝ} {Fm : FamP eps} (O : GlobalObjF Fm) (C : ℝ) : Prop where
  curve : ∀ x (i : Fm.Ix x), CurveClaims (Fm.D x i) C (O.K x i)
  pend : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, PendClaims (Fm.D x i)

def GlobalTiedF {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ O : GlobalObjF Fm, GlobalTiesF O ∧ GlobalChoicesF O ∧ GlobalClaimsF O C











theorem GlobalTiedF.kRat {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) : flipTwoThree.admF7 Fm := by
  obtain ⟨O, -, hK, -⟩ := h
  exact ⟨0, fun x _ hx i => hK.kRat x hx i⟩

theorem GlobalTiedF.colVal {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) := by
  obtain ⟨O, -, -, hC⟩ := h
  exact (hC.pend x hx i).colVal

theorem GlobalTiedF.pend {eps : ℝ} {Fm : FamP eps} {C : ℝ} (h : GlobalTiedF Fm C) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    flipTwoThree.adm7 (Fm.D x i) ∧ (flipTwoThree.adm3 (Fm.D x i) → ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) := by
  obtain ⟨O, -, hK, hC⟩ := h
  exact ⟨hK.kRat x hx i, (hC.pend x hx i).colVal⟩


end Formalism.L2.GlobalTheoryTheory

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcTop

section Part1

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.Lnk Formalism.MainNotions.Pk Formalism.L2.GlobalTheoryTheory NumberField

def RowReal (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)

def ClosedKudlaFamilyStandardLattice (𝒞 : FamClass) (C3 : ℝ) : Prop := Closed 𝒞 fun Fm _ => StandardLattice.KudlaFamilyStatement Fm C3

def WithCompatibility (𝒞 : FamClass) (C22 : ℝ) : FamClass := fun Fm => 𝒞 Fm ∧ GlobalTiedF Fm C22

end Part1

section Part2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.L2.GlobalTheoryTheory.MergeGL2

end Part2

end Formalism.L2.GlobalTheoryTheory.ConcTop

end
end
