import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NchTOfTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalHeckeDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NAllCWithLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodRowLatticesIntegralProvisionalRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevelStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingOneApplyDivThree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetric
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainLevelFamilyExtension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTrueColsRowInt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsCrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepOfHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtOfExpRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMotiveAdjointWithLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveThetaOfReadRelationStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.F0K_eq_of_kapDef : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt), DV.KapDef (w.D Z) →
    DV.KapDef (w.D Z') → F0K K.s (w.D Z) = F0K K.s (w.D Z') := by
  first | exact @GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices | exact GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices | (intros; apply GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) → ∀ v, v ∉ P.Wt → ∀ j, 1 ≤ j → j ≤ B.R.m →
      (w.D x.o.Z).what₂.Ij (w.D x.o.Z).what₂.mu0 j v = 0 ∧ (w.D x.o.Z).what₂.jw (w.D x.o.Z).what₂.mu0 j v = 0 := by
  intro K B f T w hO hF hP P x hη hW v hv j hj1 hj2
  classical
  let Zr : ReadL x.m.z.R x.m.z.F x.s.p0 x.r.Y := (x.rowsAre hη).Z
  obtain ⟨G, Y, -⟩ := GlobalTheory.PointGeometry.exists_geo (w.st x.o.Z).toD7.what₂.LL
  let Fm : ∀ k, GlobalTheory.ProvisionalDivX.MjForm (w.st x.o.Z).toD7 k := fun k =>
    ⟨mjH Zr k, jM Zr k, mjH_good Zr x.m.intersectionNumber_baseChange k, jM_basis Zr x.m.intersectionNumber_baseChange k, jM_lat Zr x.m.z.pins x.m.intersectionNumber_baseChange k,
      mjLat_sub Zr x.m.z.pins x.m.intersectionNumber_baseChange k, MjModel.jM_metric_all Zr x.m.intersectionNumber_baseChange k⟩
  let Xd : DivX (w.st x.o.Z).toD7 := GlobalTheory.provisionalDivX (w.st x.o.Z).toD7 G Y
    (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) Fm
  have hMj := mjHTie_of_eq Zr Xd rfl (HEq.refl (jM Zr))
  have hIdx : IdxDefs (w.st x.o.Z).toD7 Xd := (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Xd
  have hT := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y Zr Xd _ x.m.z.pins x.m.intersectionNumber_baseChange hMj hIdx
  have hv' : v ∉ x.m.z.W1 (F0K K.s (w.D x.o.Z)) := hW ▸ hv
  have h0 : x.r.Y.tup (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 = (w.D x.o.Z).what₂.mu0 := by
    rw [x.r.tup]; exact x.m.y.tup0
  have hIj := hT.Ij
  have hjw := hT.jw
  have hv2 := fun (i : Fin (w.st x.o.Z).toD7.R.m) (w' : HeightOneSpectrum (𝓞 (w.st x.o.Z).toD7.what₂.LL))
      (hw' : w' ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _)) =>
    not_or.1 (fun h => hv' ⟨i, w', hw', h⟩)
  have hm : (w.st x.o.Z).toD7.R.m = B.R.m := rfl
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st x.o.Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [← h0]
  have hp : (w.st x.o.Z).toD7.plEq v ∈ ({(w.st x.o.Z).toD7.plEq v, Formalism.DivisionValues.conjPl ((w.st x.o.Z).toD7.plEq v)} : Set _) :=
    Set.mem_insert _ _
  refine ⟨?_, ?_⟩
  · exact (hIj i _ v).trans (not_not.1 (hv2 i _ hp).1)
  · exact (hjw i _ v).trans (not_not.1 (not_or.1 (hv2 i _ hp).2).1)
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_zero_off_twistedPlaces : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) → ∀ v, v ∉ P.Wt → ∀ j, 1 ≤ j → j ≤ B.R.m →
      (w.D x.o.Z).what₂.Ij (w.D x.o.Z).what₂.mu0 j v = 0 ∧ (w.D x.o.Z).what₂.jw (w.D x.o.Z).what₂.mu0 j v = 0 := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.St.idx_zero_off_twisted
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P),
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  first | exact @GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | exact GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | (intros; apply GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder Matrix

namespace GlobalTheory.Mem.ColTie

section Mat

end Mat

section Gen

def StarCx {X : Fields} (σ : X.K →+* ℂ) : Prop := ∀ x, σ (star x) = starRingEnd ℂ (σ x)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev HPm : Matrix (Fin (dimP W Ch sel mu P hX)) (Fin (dimP W Ch sel mu P hX)) X.K :=
  (csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr

abbrev eP (i : Fin (dimP W Ch sel mu P hX)) : Fin (dimP W Ch sel mu P hX) → X.K := Pi.single i 1

theorem ipK_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform (HPm W Ch sel mu P hX) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level W Ch sel mu P hX, ipK_zOf]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px) (t : TupU I U)

end Fam

section TC

attribute [local instance] starE

theorem sig_starCx (B : Base) : StarCx (X := B.fields) (sig B) := fun x => B.starLL_cx x

variable {B : Base} {px : PreX B.toPre} (I : TC B px)

end TC

end GlobalTheory.Mem.ColTie
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.R3.Rw.NormTie

section
open _root_.Formalism.L2.Col
variable {Y : Fields} {Pr : Primes Y} {R : Ranks} (W : Wts Y Pr.Word R) (Ch : Chars Y Pr R.m)
  (sel : HeightOneSpectrum (𝓞 Y.F) → HeightOneSpectrum (𝓞 Y.E)) {S : Set ℕ} (mu : Tup Y.F Y.E Y.K S)
  (P : Formalism.L2.Col.LevFam Y.E Y.K R.r Pr.vGs) (hX : Y.Ok)

theorem isFormOf_zOf (y) : IsFormOf W Ch sel mu hX P (ColTie.zOf W Ch sel mu P hX y) (TieModel.frm W Ch sel mu hX P y) :=
  ⟨(ColTie.resK W Ch sel mu hX).symm (ColTie.formK W Ch sel mu P hX y), ColTie.zOf_mem W Ch sel mu P hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

end

set_option maxHeartbeats 2000000 in

theorem normAt_eq_norm_tie : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  intro X px I hX Xg tr a O _ φ s t e hcrd x
  have hs := GlobalTheory.Mem.ColTie.zOf_surjective X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX
  obtain ⟨y, rfl⟩ : ∃ y, (GlobalTheory.Mem.ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) = x := hs x
  have hF := isFormOf_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y
  obtain ⟨x', hx', hj⟩ := hcrd y
  have hx2 : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x' (TieModel.frm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y) := hx'
  have hxx := TieModel.isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hx2 hF
  subst hxx
  rw [← hj]
  have hmk := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX).2
    (InfinitePlace.mk X.B.embLL) (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)
  have hip : (Formalism.L2.Col.mtildeGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)).ip
      (Formalism.L2.Col.mtildeOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I))
      (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 =
      Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y :=
    ColTie.ipLev_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y
  have hin : inner ℂ (t.j y) (t.j y) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) :=
    t.forms.inner y y
  have hσ : ∀ z : X.B.fields.K, X.B.embLL (star z) = starRingEnd ℂ (X.B.embLL z) := ColTie.sig_starCx X.B
  have hn : ((‖t.j y‖ ^ 2 : ℝ) : ℂ) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) := by
    rw [← hin, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [LinearEquiv.refl_apply, Formalism.L2.Col.GSD.ipAt_eq_ipEmb] at hmk
  rcases InfinitePlace.embedding_mk_eq X.B.embLL with he | he
  · rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ, hip] at hmk
    have h2 := Complex.ofReal_injective (hmk.trans hn.symm)
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · have hσ' : ∀ w : X.B.fields.K, (ComplexEmbedding.conjugate X.B.embLL) (star w) =
        starRingEnd ℂ ((ComplexEmbedding.conjugate X.B.embLL) w) := by
      intro w
      simp only [ComplexEmbedding.conjugate_coe_eq, hσ]
    rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ', hip, ComplexEmbedding.conjugate_coe_eq, ← hn, Complex.conj_ofReal] at hmk
    have h2 := Complex.ofReal_injective hmk
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end GlobalTheory.Mem.R3.Rw.NormTie
end

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000 in

theorem eMt0_isometry : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  intro K B f T w hO hF hP P x hη u F G
  show inner ℂ (P.q.e.e0 u F) (P.q.e.e0 u G) = _
  have hN : ∀ m : (Df.MtHL w.I P.hX w.I.mu0).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL w.I P.hX w.I.mu0).b (Df.MtHL w.I P.hX w.I.mu0).X
      (InfinitePlace.mk B.embLL) m = ‖P.q.per.e w.I.mu0 (Df.toCx w.I P.hX w.I.mu0 m)‖ :=
    GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr w.I.mu0 (P.q.t.tA true w.I.mu0) (P.q.per.e w.I.mu0) (P.q.per.crd w.I.mu0)
  have hin : ∀ y y' : Df.MtCx w.I w.I.mu0, inner ℂ (P.q.per.e w.I.mu0 y) (P.q.per.e w.I.mu0 y') = Df.cSum w.I P.hX w.I.mu0 y y' := by
    intro y y'
    obtain ⟨-, ⟨j, hj⟩, -, hsp⟩ := GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis w.I P.hX w.I.mu0
    obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
    have hspan : Submodule.span ℂ (Set.range j) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, hj _⟩)
    exact Df.inner_eq_of_norm_sq B.embLL j hspan k hk (P.q.per.e w.I.mu0).toLinearMap (Df.cSum w.I P.hX w.I.mu0) (fun m => by
      rw [hj, LinearEquiv.coe_toLinearMap, ← hN m, GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric w.I P.hX w.I.mu0 m]) y y'
  have key : ∀ F : ((w.D x.o.Z).mem u).P.Mt,
      Df.SameForm w.I w.l u w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) F := fun F => by
    have h := P.q.per.ref u ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F))
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
    exact h
  have h1 : ∀ F : ((w.D x.o.Z).mem u).P.Mt, P.q.e.e0 u F = P.q.per.e w.I.mu0 ((P.q.per.e w.I.mu0).symm (P.q.e.e0 u F)) :=
    fun F => ((P.q.per.e w.I.mu0).apply_symm_apply _).symm
  rw [h1 F, h1 G]
  exact (hin _ _).trans (GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u w.I.mu0 F G _ _ (key F) (key G)).symm

end GlobalTheory.Mem.R3.Rw.St

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u F G, inner ℂ ((w.D x.o.Z).eMt u F) ((w.D x.o.Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.St.eMt0_isometry
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.CsumForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

theorem ipK_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform ((csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← ipK_eq_card_mul_ipLev W Ch sel mu P hX, ipK_zOf_eq]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section TC

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι)

theorem cSum_toCx (x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I))
    (x' : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x') =
      B.embLL (ipLev (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX x x') := by
  rw [Df.cSum_apply]
  unfold ipLev GSD.ip GSD.ipOf CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold Df.cTerm
  rw [map_mul, map_inv₀, map_natCast, GSD.wt_eq]
  congr 1
  exact (map_pairV_one _ _ (sig B) (fun x => B.starLL_cx x) _ _).symm

end TC

theorem cSum_toCx_rowForm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  intro X px I hX Xg tr a y x hx
  obtain ⟨F, h, hF, rfl⟩ := hx
  have e1 : ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX F =
      ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := eq_of_heq hF
  have e2 : (⟨F.1, h⟩ : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) =
      ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := by
    apply Subtype.ext
    show F.1 = ((ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)).1
    rw [← e1, LinearEquiv.symm_apply_apply]
  rw [cSum_toCx, e2]
  exact congrArg X.B.embLL (ipLev_zOf_eq (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y)

end GlobalTheory.Mem.CsumForm
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  atlas_forward_decl GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EmtTw
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 2000000

theorem inner_per_e {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (a : w.C.Tup)
    (y y' : Df.MtCx w.I a) : inner ℂ (P.q.per.e a y) (P.q.per.e a y') = Df.cSum w.I P.hX a y y' := by
  let jA := (P.q.t.tA true a).j
  have hF := (P.q.t.tA true a).forms
  let eS : (P.q.p.sA true a).A.T →ₗ[ℂ] Df.MtCx w.I a := (P.q.per.e a).symm.toLinearMap
  let j' := eS.comp jA
  have hspan : Submodule.span ℂ (Set.range j') = ⊤ := by
    have h0 : Submodule.span ℂ (Set.range jA) = ⊤ := by
      rw [← ColTie.span_single_eq]; exact hF.span
    have h1 : Set.range j' = eS '' Set.range jA := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h0, Submodule.map_top]
    exact LinearMap.range_eq_top.2 (P.q.per.e a).symm.surjective
  obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
  refine Df.inner_eq_of_norm_sq _ j' hspan k hk (P.q.per.e a).toLinearMap (Df.cSum w.I P.hX a) (fun m => ?_) y y'
  obtain ⟨x, hx, hjx⟩ := P.q.per.crd a m
  have hj' : j' m = Df.toCx w.I P.hX a x := by
    show (P.q.per.e a).symm (jA m) = _
    rw [show jA m = _ from hjx, LinearEquiv.symm_apply_apply]
  have he : (P.q.per.e a).toLinearMap (j' m) = jA m := by
    show (P.q.per.e a) ((P.q.per.e a).symm (jA m)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hL := GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr a m x hx
  have hI := hF.inner m m
  rw [he, hj', hL]
  calc ((‖jA m‖ ^ 2 : ℝ) : ℂ) = inner ℂ (jA m) (jA m) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = _ := hI

theorem eMtTw_isometry_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  intro K B f T w _ _ _ P x _ u a _ F G
  change inner ℂ (P.q.e.eT u a F) (P.q.e.eT u a G) = _
  have key : ∀ F : (TC.per w.I w.l u a).Mt, Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F)) F := fun F => by
    have h := P.q.per.tw u a ((P.q.per.e a).symm (P.q.e.eT u a F))
    rw [LinearEquiv.apply_symm_apply] at h
    exact (congrArg (Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F))) ((P.q.e.eT u a).symm_apply_apply F)).mp h
  have h1 : ∀ F : (TC.per w.I w.l u a).Mt, P.q.e.eT u a F = P.q.per.e a ((P.q.per.e a).symm (P.q.e.eT u a F)) := fun F =>
    ((P.q.per.e a).apply_symm_apply _).symm
  rw [h1 F, h1 G, inner_per_e P a, GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u a F G _ _ (key F) (key G)]

end GlobalTheory.Mem.R3.Rw.EmtTw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodForms_isometry_columnPairing_at_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.EmtTw.eMtTw_isometry_state
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.provisionalRows_furtherCompatibilities_at_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ t : RowsT K w x.o.Z P.Wt x.s.p0, t.r = x.rowsAre hη → Nonempty (RXs t) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state | exact GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state | (intros; apply GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

set_option maxHeartbeats 4000000 in

theorem exists_rowsT : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w) (x : St P), (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) → ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW := by
  refine StepW.of_all fun K B f T w hK hF hw P x hη => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have h1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ h1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.T.F0K_eq_of_kapDef K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  let t : RowsT K w x.o.Z P.Wt x.s.p0 :=
    { hX := P.hX
      r := x.rowsAre hη
      exAt := x.m.exAt
      inGeo := x.m.inGeo
      grpAt := x.fits.grpAt
      grp := x.fits.grp
      mu :=
        { inj := w.ok.xi_inj
          range := w.xi_range
          mu0 := w.l.xi0
          star := by
            show w.I.xi w.I.muStar = f.del
            rw [w.ok.xi_star, w.C_eq]
          star' := by
            show w.I.xi w.I.muStar' = f.del'
            rw [w.ok.xi_star', w.C_eq]
          tw := P.q.mu.tw
          on := P.q.mu.on
          off := P.q.mu.off
          sub := P.sub
          supp := P.supp }
      exact := hex
      untw := GlobalTheory.T.index_zero_off_twistedPlaces K B f T w hK hF hw P x hη hex
      emt0 := GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing K B f T w hK hF hw P x hη
      emt := GlobalTheory.T.periodForms_isometry_columnPairing_at_state K B f T w hK hF hw P x hη
      etaF := x.etaF
      rowInt := GlobalTheory.T.periodRowLatticesIntegral_provisionalRows K B f T w P x.o
      idx := fun Y _ => (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Y }
  exact ⟨t, GlobalTheory.T.provisionalRows_furtherCompatibilities_at_state K B f T w hK hF hw P x hη t rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3.Rw.St

end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Fin3.MvLoc

section Three

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A : DIV.FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} (R : Links.RealDat3 a.D A Ks)

def thrice : type_of% (real3 c R) := (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thriceY : type_of% (letI := alg c iK; (real3 c R).ioY) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioY :))

def thriceX : type_of% (letI := alg c iK; (real3 c R).ioX) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioX :))

theorem thriceY_eq : letI := alg c iK; (real3 c R).ioY = thriceY b c R := by
  have h1 := real_ioY c R.toRealDat
  have h2 := real_ioY b R.toRealDat
  have h3 := real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceY b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thriceX_eq : letI := alg c iK; (real3 c R).ioX = thriceX b c R := by
  have h1 := real_ioX c R.toRealDat
  have h2 := real_ioX b R.toRealDat
  have h3 := real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceX b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thrice_eq : real3 c R = thrice b c R := by
  letI := alg c iK
  exact (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (real3 c R)) (thriceY_eq b c R) (thriceX_eq b c R)) :))

theorem inertTransport_twice_heq_direct : HEq (real3 (a := b) c (iK := alg b iK) (real3 b R)) (real3 c R) :=
  (by with_unfolding_all exact ((HEq.symm (heq_of_eq (thrice_eq b c R))) :))

end Three

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

theorem coreJ_heq {k₀ : Formalism.L2.Pj.CoreJ a.D} {k : Formalism.L2.Pj.CoreJ b.D} (h : HEq k (coreJ b k₀)) : HEq (coreJ c k) (coreJ c k₀) := by
  obtain rfl : k = coreJ b k₀ := eq_of_heq h
  exact (by with_unfolding_all exact ((HEq.refl (coreJ c k₀)) :))

theorem realAdelicInertTransport_heq_of_transport (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) (k : Formalism.L2.Pj.CoreJ b.D)
    (i : Algebra k.Q.c.F b.D.what₂.LL) (hi : ∀ y : k.Q.c.F, B.embLL (algebraMap k.Q.c.F b.D.what₂.LL y) = (y : ℂ))
    (R : Links.RealDat3 b.D (famR b.st I hX (usedOf I T Wt) Xg tr) k.Q.c.F) (hXg : Xg = z₀.Xg)
    (htr : tr = z₀.tr) (hc : HEq k (coreJ b z₀.core)) (hR : HEq R (real3 b (iK := z₀.alg) z₀.R)) :
    HEq (real3 c (iK := i) R) (real3 c (iK := z₀.alg) z₀.R) := by
  subst hXg htr
  obtain rfl : k = coreJ b z₀.core := eq_of_heq hc
  have ha : i = (by with_unfolding_all exact ((alg b z₀.alg) :)) :=
    Algebra.algebra_ext _ _ fun y => (by with_unfolding_all exact ((B.embLL.injective ((hi y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))) :
      _ = (@algebraMap _ _ _ _ z₀.alg ((by with_unfolding_all exact (y :))) : B.LL)) :))
  subst ha
  have hR' : R = (by with_unfolding_all exact ((real3 b (iK := z₀.alg) z₀.R) :)) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  exact (by with_unfolding_all exact ((inertTransport_twice_heq_direct b c (iK := z₀.alg) z₀.R) :))

end Copy

section Move

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o o' : q.Over}

theorem coreP_transfer {Z Z' : w.Lt} (s : SameGrp (B := B) (C := w.C) Z Z') {z : Dat (w.st Z) w.I hX T Wt} (h : CoreP z) :
    CoreP (w := w) (Z := Z') (Dat.transfer (B := B) (C := w.C) (a := Z) (b := Z') s z) :=
  ⟨(by with_unfolding_all exact ((Mv.lawsCore_tr (a := Z) Z' h.1) :)), (by with_unfolding_all exact (h.2.1 :)), (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩

theorem copy_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) {m : Moved o} {m' : Moved o'} (hm : m.Copy)
    (e : m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z) : m'.Copy := by
  have h1 := coreJ_heq (a := Z₀) o.Z o'.Z (k₀ := z₀.core) (k := m.z.core) ((by with_unfolding_all exact (hm.core :)))
  have h2 := realAdelicInertTransport_heq_of_transport (a := Z₀) o.Z o'.Z z₀ m.z.Xg m.z.tr m.z.core m.z.alg m.z.alg_eq m.z.R m.Xg m.tr ((by with_unfolding_all exact (hm.core :))) ((by with_unfolding_all exact (hm.R :)))
  have e1 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.core) e
  have e2 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.R) e
  have h3 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).core (coreJ (a := Z₀) o'.Z z₀.core) := (by with_unfolding_all exact (h1 :))
  have h4 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).R (real3 (a := Z₀) o'.Z (iK := z₀.alg) z₀.R) := (by with_unfolding_all exact (h2 :))
  exact ⟨(by with_unfolding_all exact ((HEq.trans e1 h3) :)), (by with_unfolding_all exact ((HEq.trans e2 h4) :))⟩

theorem exists_moved_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hm : m.Coh) :
    ∃ m' : Moved o', m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := Mv.pkT_tr (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  have hW := Dat.nonzeroIndexPlaces_transferAlongSameFiniteGroup (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have b2 := HEq.trans hy.PY hm.PY
  have b3 := HEq.trans hy.PW hm.PW
  have b4 := HEq.trans a2 hm.rep
  have b5 := fun c => HEq.trans (a3 c) (hm.jE c)
  have b6 := fun c => HEq.trans (a4 c) (hm.jM c)
  have b7 := fun c => HEq.trans (a5 c) (hm.jX c)
  have b8 := HEq.trans a6 hm.eW
  have b9 := HEq.trans a7 hm.jMt
  have c1 := fun j v => (he j v).trans (m.eta j ((by with_unfolding_all exact (v :))))
  have c2 := fun F0 => (hW F0).symm.trans (m.W1 ((by with_unfolding_all exact (F0 :))))
  have c3 := fun c u => HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c u).j) hA)) (m.tA c u)
  refine ⟨{ z := Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((Dat.holds_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.intersectionNumber_baseChange) :))
            exAt := (by with_unfolding_all exact ((Dat.exAt_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.exAt) :))
            inGeo := (by with_unfolding_all exact ((Dat.inGeo_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => coreP_transfer s (m.core h)
            eta := (by with_unfolding_all exact (c1 :))
            W1 := (by with_unfolding_all exact (c2 :))
            y := (by with_unfolding_all exact ((Mv.hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := (by with_unfolding_all exact (c3 :)) }, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hm.tupT :))
  · exact (by with_unfolding_all exact (b2 :))
  · exact (by with_unfolding_all exact (b3 :))
  · exact (by with_unfolding_all exact (b4 :))
  · exact (by with_unfolding_all exact (b5 :))
  · exact (by with_unfolding_all exact (b6 :))
  · exact (by with_unfolding_all exact (b7 :))
  · exact (by with_unfolding_all exact (b8 :))
  · exact (by with_unfolding_all exact (b9 :))

end Move

theorem exists_moved_loc : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  intro K B f T w P x L
  obtain ⟨m, h1, h2⟩ := exists_moved_transfer (o := x.o) (o' := oL x L) (sameL x L) x.m x.coh
  exact ⟨m, h1, copy_transfer (o := x.o) (o' := oL x L) (sameL x L) x.copy h1, h2⟩

end GlobalTheory.HeightCounting.Fin3.MvLoc

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_movedData_state_localisations : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  atlas_forward_decl GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc
end

section
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem yRel_of_pin : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin →
      ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  intro K B f T w P x L m hz hC s r hP Y hY
  have hR := CopyRead.repOf_heq x.coh x.r x.pin hC r hP
  obtain ⟨z, intersectionNumber_baseChange, exAt, inGeo, Xg, tr, core, eta, W1, y, tup, t, tA⟩ := m
  dsimp only at hz
  subst hz
  obtain ⟨rY, rZ, rtup, rtupT, rPY, rPW, rjA, rjA0, reMt⟩ := r
  dsimp only at hY
  cases hY
  refine ⟨(by with_unfolding_all exact (hR :)), ?_, ?_⟩
  · intro i y
    have heW := hP.eW
    have hf : HEq t.lf.eW x.m.t.lf.eW := hC.eW.trans x.coh.eW.symm
    have h3 : @Eq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) :=
      @eq_of_heq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) ((by with_unfolding_all exact (hf :)))
    exact kc% ((heW i y).trans ((heq_of_eq (congrArg (fun g => g i y) h3)).trans (x.pin.eW i y).symm))
  · intro μ h i y
    have hjMt := hP.jMt
    have hf : HEq t.lf.jMt x.m.t.lf.jMt := hC.jMt.trans x.coh.jMt.symm
    have h3 : @Eq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) :=
      @eq_of_heq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) ((by with_unfolding_all exact (hf :)))
    exact (by with_unfolding_all exact (((hjMt μ h i y).trans ((heq_of_eq (congrArg (fun g => g μ i y) h3)).trans (x.pin.jMt μ h i y).symm)) :))

end GlobalTheory.HeightCounting.Fin3

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedReadings_related_localizedAdelicData : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin → ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  atlas_forward_decl GlobalTheory.HeightCounting.Fin3.yRel_of_pin
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

noncomputable section
namespace GlobalTheory.HeightCounting.Fin3

theorem listPin_datL : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (cDep : ℝ), ListSt cDep x → ListPin (DL x L) (datL x L).R.toRealDat.toLevCh cDep K.s.b := by
  intro K B f T w P x L cDep h
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (oL x L).Z G) :)), ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact (h2 :))⟩

end GlobalTheory.HeightCounting.Fin3
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricCharacterGridList_kept_localizedStage : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (cDep : ℝ), ListSt cDep x → ListPin (DL x L) (datL x L).R.toRealDat.toLevCh cDep K.s.b := by
  atlas_forward_decl GlobalTheory.HeightCounting.Fin3.listPin_datL
end

section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : LC hL x)

theorem mtIn : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
  rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt

theorem builtEx (hP : PrN) : GlobalTheory.CoefDuty.BuiltEx l.a.A l.mt.M l.c.ch l.c.tp.tup := fun big =>
  GlobalTheory.T.side_rational_hecke_data hP.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ l.b.Bs l.mt.M
    l.c.ch l.c.tp l.c.side (mtIn l) l.a.elem.star l.a.elem.int l.a.elem.split (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
    (fun v _ => by rw [l.c.psi_eq]; exact GlobalTheory.twDat_psi_valuesIn_LL B T P.coh v) l.a.omax
    (GlobalTheory.HeightCounting.blocksUnique_of_cgTrue hL hP.what₂.fin hP.what₂.gal hP.what₂.art hP.what₂.js hP.what₂.cheb _ _ l.a.cg) big

variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : AutSpec l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))

def ntW : NTrue hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtIn l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }

variable (L) in

structure AllL : Type 1 where
  a : NAllC (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → Formalism.L2.RowLocTied (withLoc L) a.gal.lp F

include Au ss in

theorem allL_nonempty (hP : PrN) (hA : ArchCmp hL) : Nonempty (AllL l L) := by
  obtain ⟨a, h1, h2, h3, h4, ⟨h5⟩, h6, h7⟩ := GlobalTheory.HeightCounting.FitAll.nAllC_withLoc hL hA.lp hA.cg _ (ntW l Sp Au ss).toNBuilt l.a.fr l.a.fr_jE
    l.a.pht l.a.elem (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) Finset.subset_union_left
  exact ⟨⟨a, h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem low_ok (D : D7) : 2 ∈ lowAll D ∧ AbsolutelyIrreducibleSpan.q0 D ∈ lowAll D ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ lowAll D ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := by
  refine ⟨by simp [lowAll, Formalism.L2.lowPr], by simp [lowAll, Formalism.L2.lowPr], fun p hp => ?_, fun p hp => ?_⟩ <;>
    simp only [lowAll, Formalism.L2.lowPr, Finset.mem_union, Finset.mem_insert] <;> tauto

variable (al : AllL l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))

theorem pqW (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) :=
  (al.exp.pl i j b k Q ψ h1 h2 hadm).trans (Prod.ext (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).1 (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).2)

def natW : NAt hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := ntW l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := fun y => (by with_unfolding_all exact (((congrArg (fun e : (Dof x).host.E →+* Qb => e ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (al.jE :)) : (kc% al.a.gal.fr.jE : (Dof x).host.E →+* Qb) = l.a.jE)).trans (l.a.frame ((by with_unfolding_all exact (y :))))) :))
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (pqW l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (pqW l al i j b k Q ψ h1 h2 hadm)) :))⟩
  jE_eq := (by with_unfolding_all exact ((heq_of_eq al.jE.symm) :))
  mt_eq := (by with_unfolding_all exact ((heq_of_eq al.mt.symm) :))
  Pq_eq := (by with_unfolding_all exact ((HEq.refl l.Pq) :))
  low := (by with_unfolding_all exact ((low_ok (Dof x)) :))
  split := hLg.2.1
  ratIn := l.rat.In
  ratIn_hL := rfl
  ratIn_eig := rfl
  ratIn_θ := rfl
  depth := l.a.depth

def natD : NAt hL (DL x L) (cfD x L) (chD L l) (tpD L l) := (by with_unfolding_all exact ((natW l Sp Au ss al hLg) :))

include l in
variable (L) in

theorem grpD : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).card :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).e0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).lvl0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).psi0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩

variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)

def frameY : Formalism.L2.RowFrame (DL x L) := Formalism.L2.Col.rowFrameOf (DL x L) _ Y.eFT

def rowD : NRow (D := DL x L) (natD l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := ysL L l
  hecke := hkHL L l
  grp := grpD l L
  rowLoc := (by with_unfolding_all exact ((al.loc ((by with_unfolding_all exact ((frameY Y) :))) ((by with_unfolding_all exact ((eq_of_heq (kc% hY.rep : HEq (repOf Y) (kc% (repOf x.r.Y) : type_of% (repOf Y)))) :)))) :))
  S_eq := (by with_unfolding_all exact ((SL_heq L l.rat) :))
  hL_eq := (by with_unfolding_all exact ((HEq.refl l.rat.In.hL) :))
  rep_eq := (by with_unfolding_all exact (hY.rep.symm :))

theorem moreD {xd : ThData (Dof x)} (hxd : XdAll xd) : Nonempty (NMore (rowD l Sp Au ss al hLg Y hY) (datL x L).geo (xdD L xd)) := by
  obtain ⟨ad, had⟩ := GlobalTheory.T.exists_motive_adjoint_with_levels L l Y hY
  obtain ⟨ser⟩ := GlobalTheory.T.series_at_of_exp_relation L l al.a.exp al.exp
  have e : (natD l Sp Au ss al hLg).all.gal.mt = mtD L l := (by with_unfolding_all exact (al.mt :))
  have H : ∃ ad' : MtAd Y (natD l Sp Au ss al hLg).all.gal.mt, ad'.PV = pvL L l := by
    rw [e]; exact ⟨ad, had⟩
  obtain ⟨ad', had'⟩ := H
  have ser' : SerAt (ysL L l) (datL x L).geo.v₀ (expD L al.a.exp) ad'.PV (cfD x L) (pqD L l) := had'.symm ▸ ser
  exact ⟨{ ad := ad'
           fi := ysL_fi L l
           hecke := GlobalTheory.T.hecke_row_of_local_all L l
           cHk := (by with_unfolding_all exact ((fun i b Q => (⟨l.b.Bs.cHk i b Q, pow_one _⟩ : ∃ u : ((Dof x).ntw.O i)ˣ, (hkH l).cHk i b 1 Q =
             algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) u)) :))
           eig := ⟨sbD L l, eigD L l, (by with_unfolding_all exact (l.b.Sb_le :)), (by with_unfolding_all exact ((HEq.refl l.rat.In.eig) :)), GlobalTheory.T.eigen_adjoint_of_read_relation L l Y hY⟩
           ser := (by with_unfolding_all exact (ser' :))
           tau := (by with_unfolding_all exact ((al.exp.tau l.b.tau) :))
           geo := geoL L l
           ok := okL L l
           th := GlobalTheory.T.motive_theta_of_read_relation L l Y hY
           xd := xdD_all L hxd
           large := (by with_unfolding_all exact (hLg :))
           labc := (by with_unfolding_all exact (l.a.labc :))
           zeta := (by with_unfolding_all exact (l.a.zeta :))
           pht := (by with_unfolding_all exact ((⟨l.a.fr, l.a.fr_jE, l.a.pht⟩ : ∃ fr : Formalism.L2.OmFrame (Dof x), fr.jE = l.a.jE ∧ PhtOn l.a.A.wd fr fun _ _ _ _ => True) :)) }⟩

def nchD : NchT w (oL x L).Z P.Wt (chD L l) where
  tp := tpD L l
  xi := (by with_unfolding_all exact (l.c.xi_eq :))
  psi := (by with_unfolding_all exact (l.c.psi_eq :))
  tie := (GlobalTheory.HeightCounting.NchAt.tie_of_true (natD l Sp Au ss al hLg).nt).1
  Q := fun v hv => ⟨(by with_unfolding_all exact (((congrFun l.c.Q_eq v).trans (GlobalTheory.HeightCounting.Up.Model.qOf_on v hv)) :)),
    (by with_unfolding_all exact ((l.c.k_eq v ((GlobalTheory.HeightCounting.Up.Model.twisted_iff x v).2 hv)) :))⟩
  chrPsi := (GlobalTheory.HeightCounting.NchAt.tie_of_true (natD l Sp Au ss al hLg).nt).2

include hY in

theorem core_at {xd : ThData (Dof x)} (hxd : XdAll xd) (t : RowsT K w (oL x L).Z P.Wt p0) (hz : HEq t.r.z (datL x L))
    (ht : HEq t.r.Y Y) : ∃ c : NCore hL t (nchD l Sp Au ss al hLg),
      Nonempty (NEb hL K B f T w (oL x L).Z P.Wt p0 t (chD L l) (nchD l Sp Au ss al hLg) (xdD L xd) c) ∧
      ∀ cDep : ℝ, ListSt cDep x → ListPin (DL x L) t.r.z.R.toRealDat.toLevCh cDep K.s.b := by
  obtain ⟨hX, ⟨z, intersectionNumber_baseChange, Y', Zr, tix⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := t
  have e : z = datL x L := eq_of_heq hz
  subst e
  have e' : Y' = Y := eq_of_heq ht
  subst e'
  obtain ⟨mo⟩ := moreD l Sp Au ss al hLg Y' hY hxd
  exact ⟨⟨natD l Sp Au ss al hLg, rowD l Sp Au ss al hLg Y' hY, (by with_unfolding_all exact (l.sel :))⟩, ⟨(mo, ⟨bkL L⟩)⟩, fun cDep h => GlobalTheory.T.toricCharacterGridList_kept_localizedStage x L cDep h⟩

omit l in
theorem read_cast {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} (e : z = z') {p : BaseLevelRowSide (w.D Z)}
    (Y₀ : Read z.R.toRealDat z.F.lv2 p) : ∃ Y₁ : Read z'.R.toRealDat z'.F.lv2 p, HEq Y₁ Y₀ := by
  subst e
  exact ⟨Y₀, HEq.rfl⟩

def RowsAt (P : Pre2 K w) : Prop := ∀ x : St P, (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) →
  ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW

omit l in
variable (x L) in

theorem rows_ex (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hD : GlobalTheory.Published.DiscreteSeriesExists) (hP : PrN) (hR : RowsAt P)
    (he : ∀ j v, 1 ≤ j → j ≤ B.R.m → etaL x L j v = P.q.eta j v) :
    ∃ (p : BaseLevelRowSide (w.D (oL x L).Z)) (t : RowsT K w (oL x L).Z P.Wt p), Nonempty (RXs t) ∧
      ∃ Y₁ : YT x L p, YRel L Y₁ ∧ HEq t.r.z (datL x L) ∧ HEq t.r.Y Y₁ := by
  obtain ⟨m, hm, hc, hco⟩ := GlobalTheory.T.exists_movedData_state_localisations x L
  obtain ⟨s, r, hpin⟩ := GlobalTheory.T.exists_reading_of_rowLiftFamily_movedData B f T w P.Z₀ P.hX P.Wt P.z P.q (oL x L)
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hW hD hP.hc hP.decay (w.D (oL x L).Z)) (fitsL L) m
  obtain ⟨t, rx, -, hz, hy, -⟩ := hR ⟨oL x L, fitsL L, x.G_eq, x.etaF, bkL L, m, hc, hco, s, r, hpin⟩ he
  obtain ⟨Y₁, h1⟩ := read_cast hm r.Y
  exact ⟨s.p0, t, rx, Y₁, GlobalTheory.T.normalisedReadings_related_localizedAdelicData x L m hm hco s r hpin Y₁ h1, hz.trans (heq_of_eq hm), hy.trans h1.symm⟩

theorem lv3_of_third (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hD : GlobalTheory.Published.DiscreteSeriesExists) (hP : PrN) (hA : ArchCmp hL)
    (hR : RowsAt P)
    (hE : GlobalTheory.CoefDuty.BuiltEx l.a.A l.mt.M l.c.ch l.c.tp.tup → GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v)
    (hX : ∃ xd : ThData (Dof x), XdAll xd) (S : SExt) (Γ : GeoP) (N : NExt hL)
    (hN : ∀ Z p t nch n xd c, NEb hL K B f T w Z P.Wt p t nch n xd c →
      (∀ cDep : ℝ, ListSt cDep x → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b) →
      Nonempty (N K B f T w Z P.Wt p t nch n xd c)) :
    ∃ (Z : w.Lt) (v : Lv3 (prmR N S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch := by
  have hB := builtEx l hP
  obtain ⟨big, hbig⟩ := hE hB
  obtain ⟨L, hL'⟩ := hB big
  obtain ⟨hLg, he⟩ := hbig L hL'
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hL'
  obtain ⟨al⟩ := allL_nonempty l Sp Au ss hP hA
  obtain ⟨xd, hxd⟩ := hX
  obtain ⟨p, t, ⟨rx⟩, Y₁, hY₁, hz, ht⟩ := rows_ex x L hW hD hP hR fun j v h1 h2 => he j v h1 h2 v HEq.rfl
  obtain ⟨c, ⟨ne⟩, hp⟩ := core_at l Sp Au ss al hLg Y₁ hY₁ hxd t hz ht
  obtain ⟨nn⟩ := hN _ p t _ _ _ c ne hp
  have hg : GIs2 K w x.o.G := x.G_eq ▸ P.g
  exact ⟨(oL x L).Z,
    { g := hg, coh := P.coh, Wt := P.Wt, p0 := p, what₂ := t, rx := rx, nch := chD L l, n := nchD l Sp Au ss al hLg, xd := xdD L xd
      chiT := fun k v => TypesTrue.chiT_gen (fitsL L).grp k v, nx := ⟨c, nn⟩ }, rfl, keptL L l⟩

omit l in

theorem rowsAt_start : StepW Start fun K _ _ _ w => ∀ P : Pre2 K w, RowsAt P :=
  Step.trans GlobalTheory.Mem.R3.Rw.St.exists_rowsT (Step.of_all fun _ _ _ _ _ _ _ H w hs P => H w ⟨hs.1, ⟨P⟩⟩ P)

omit l in

theorem sFin : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → PrN →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → SEta hL → SXd hL → SFin hL ∧ ∀ cDep : ℝ, SFinl hL cDep := by
  intro hW hD hP hL hA hE hX
  have h := rowsAt_start.and (StepW.and hE hX)
  refine ⟨h.trans (StepW.of_all ?_), fun cDep => h.trans (StepW.of_all ?_)⟩
  · intro K B f T w _ _ H P x l S Γ
    exact lv3_of_third l hW hD hP hA (H.1 P) (H.2.1 P x l) (H.2.2 P x ⟨l.toStrictHenselianAcyclic.toLI, l.b.toSeriesState⟩) S Γ (NEb hL)
      fun _ _ _ _ _ _ _ a _ => ⟨a⟩
  · intro K B f T w _ _ H P x l S Γ hp
    exact lv3_of_third l hW hD hP hA (H.1 P) (H.2.1 P x l) (H.2.2 P x ⟨l.toStrictHenselianAcyclic.toLI, l.b.toSeriesState⟩) S Γ (NEl hL cDep)
      fun _ _ _ _ _ _ _ a b => ⟨(a, ⟨b cDep hp⟩)⟩

end GlobalTheory.HeightCounting.Fin3

end
end
