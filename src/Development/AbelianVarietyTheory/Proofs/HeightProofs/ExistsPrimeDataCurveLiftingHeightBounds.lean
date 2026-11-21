import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCusp
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PhiFDEqZeroAtLastIndex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.ProdInLatPf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NotGoodConj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupBddAndSupREqSupN
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LawBddDataOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RamOverZRealPos
import Formalism.LocalToGlobal.ProjectiveLattices.NumericalH1Condition
import Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotOverAndTriv
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftFrShFin
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictCompInt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNormStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwiseStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChartStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LengthsAtPrimesLeFunctionFieldDataOfCurve
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrdersAuxiliaryFormAtPrimesEqFunctionField
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FrameNormRestrictedDensity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCBaseValAtCx
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChosenFormsRestrictBasisFunctionField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalityDefiniteLiftIndex
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRealisationPrimeDataCurveLiftingStatement

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem iInf_le_of_combBound {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hjm : D.R.m ≤ j)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨y, hy⟩ := pt_realise h j hj la y0
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hy]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  have h1 := (hX la y).2 hjm
  rw [hd] at h1
  exact h1

theorem combAlg_of_tiedW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (c Gc Prw : ℝ), G.TiedW S Gc Prw → CombBound G S c nus → (j < D.R.m → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ)))) ∧ (j = D.R.m → ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) := by
  intro D T h j hj ka wL wF S nus G c Gc Prw hW hX
  exact ⟨fun hjm => combAlg_of_combBound h j hj hjm G S c nus hW.1 hX,
    fun hjm => iInf_le_of_combBound h j hj hjm.ge G S c nus hW.1 hX⟩

end GlobalTheory.RunJoin
end
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin.NoPoint

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem subsingleton_sections_of_no_leadingTerm (G : GlobalFamilyData X ka wL wF) (hd : G.del = 0) (la : HeightOneSpectrum (𝓞 B.KO))
    (hB : InBasis G la) : Subsingleton (SectionSheafQuotient X la G.w wF) := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have h := hB.2
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact (Submodule.subsingleton_iff (Kp X la G.N)).1 (subsingleton_of_bot_eq_top h)

theorem heights_of_del_zero (G : GlobalFamilyData X ka wL wF) (Q : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have hI : ∀ la, (Q la).Ila = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    unfold LocalPointData.Ila
    exact Module.length_eq_zero
  have hN : ∀ la, (Q la).Net = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    haveI : Subsingleton (OsK X la G.w) := (hC la).2.2.1.subsingleton
    haveI : IsEmpty (PtsG G la) := ⟨fun ζ => ζ.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    unfold LocalPointData.Net
    exact finsum_of_isEmpty _
  have hd' : (G.del : ℝ) = 0 := by rw [hd]; exact Nat.cast_zero
  refine ⟨fun la => by simp [hI la], by simp [hI, summable_zero], by simp [hI, hd'],
    fun _ => ⟨by simp [hN, summable_zero], by simp [hN, hd']⟩⟩

theorem inBasis_xplus (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : InBasis G la) : InBasis (gd2Xplus G E hM) la := h

theorem heights_xplus_of_del_zero (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E)
    (Q : ∀ la, LocalPointData (gd2Xplus G E hM) la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet :=
  heights_of_del_zero (gd2Xplus G E hM) Q Gc PH Prw Pet hd (fun la => inBasis_xplus G E hM la (hB la)) hC

end Abstract

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem heights_no_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (Q : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la) (Gc PH Prw Pet : ℝ), G.del = 0 → (∀ la, InBasis G la) → (∀ la, (Q la).InCurve) → Heights Q Gc PH Prw Pet :=
  fun _ _ h j hj _ _ _ _ _ _ _ _ _ _ _ _ _ G Q Gc PH Prw Pet hd hB hC =>
    heights_xplus_of_del_zero G (extAll h j hj) (intAtExt_extAll h j hj) Q Gc PH Prw Pet hd hB hC

end GlobalTheory.RunJoin.NoPoint
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData

theorem runOK_of_pageOK {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    GlobalTheory.EtaAn.RunOK D.host.E D.R.r (DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + DF wL))) D.R.m := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have htie : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hsupp : EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW
      ⟨(((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO), 1, 1, 1⟩ wL := by
    refine ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩
    have e : σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO) =
        (((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : ℂ) := by
      rw [← map_natCast σ]
      exact congrArg σ (map_natCast (algebraMap (𝓞 B.KO) B.KO) _)
    change _ ≤ Real.log ‖σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO)‖
    rw [e, Complex.norm_natCast, Nat.cast_pow, Real.log_pow, ← Nat.cast_mul]
    have h1 : 0 ≤ Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h1]
  exact (GlobalTheory.RunParametersAtRecord.run_at_record D _ _ j X _ _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp htie hP.page hsupp).1

theorem small_rows {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    0 ≤ large₂.sc.L ∧ 0 ≤ Zb D large₂ ∧ 0 ≤ cc D large₂ C2 A2 7 wL ∧ OPO large₂ B ∧ 1 ≤ WeightFamilies.PPv D large₂ 200000 2 ∧
      1 ≤ 200000 * zBase large₂ ^ 2 := by
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  obtain ⟨hA, hS, -, -, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, hd⟩ := hS
  have hC : 0 ≤ C2 := by have := hd.1; rw [hP.tie.1] at this; linarith
  have hrd : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
  have hL : 0 ≤ large₂.sc.L := by
    by_contra hn
    have h1 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) := by positivity
    have h2 := mul_nonpos_of_nonneg_of_nonpos h1 (not_le.1 hn).le
    unfold zBase at hZ1
    linarith
  refine ⟨hL, le_trans zero_le_one hZ1, ?_, hO, ?_, by nlinarith⟩
  · unfold cc WeightFamilies.RRv WeightFamilies.PPv
    have := Real.rpow_nonneg hrd 7
    have := Real.rpow_nonneg (le_trans zero_le_one hZ1) A2
    positivity
  · unfold WeightFamilies.PPv
    have := Real.one_le_rpow hZ1 (by norm_num : (0 : ℝ) ≤ 2)
    linarith

theorem auxiliaryCuspFormConstant_monotone (D : D7) (j : ℕ) {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') : PI4 D j a b ≤ PI4 D j a' b' := by
  unfold PI4
  have : 2 * b / (WeightFamilies.dimY D j : ℝ) ≤ 2 * b' / (WeightFamilies.dimY D j : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  linarith

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_primeData_heights_of
    (hIndef : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet)
    (hDef : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet)
    (hData : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → 0 < wL.n → (j < D.R.m → (recPlus h j hj).NonZeroComp _ G.et) → ∀ (Gc Prw : ℝ) (Tn : ℕ), ∃ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InLiftC S Gc Prw Tn)) :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (T.Q.Xo j) T.Q.c → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus CL hAlg hP hC hCL hLam G hGen hEta hTh hBas hdel hComb
  obtain ⟨hG, hT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨g0, hcur⟩ := GlobalTheory.T.page_hypotheses_at_cusp D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  have hinj := GlobalTheory.Reg.genValInj_record D T h j hj hG
  have hspl := GlobalTheory.Reg.compSplit_record D T h j hj hG
  have hbirA := fun ka wL wF G => (GlobalTheory.Reg.birSt_of_ratios_trdeg D T h j hj hG ka wL wF G).2
  have hbir := hbirA _ _ _ _ hcur.2.1
  obtain ⟨hL, hZ, hc0, hO, hPet, hP16⟩ := small_rows hP
  obtain ⟨hW, hN, hlogN, -, hlow⟩ := hGen
  obtain ⟨-, h3, hn, hn0, hDF, h2, hPO, -, hcg, -⟩ := GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N 1 hj hP hCL hN one_pos hlogN (by
      rw [Nat.cast_one, Real.log_one]; positivity)
  obtain ⟨y, hw, hc, ht, hl⟩ := hData D T h j hj hG (hT hG) ka wL wF
    (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 hcur hinj hspl hbir hbirA hn0
    (fun hjm => (hEta hjm).2.1.2) (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn
  refine ⟨_, hc, ht, hl, ?_⟩
  rcases Nat.eq_zero_or_pos G.del with hd0 | hd0
  · exact GlobalTheory.RunJoin.NoPoint.heights_no_point D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S G _ _ _ _ _ hd0 hBas hc
  have hlc := (GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N G.del hj hP hCL hN hd0 hlogN hdel).1
  have hlN : Real.log G.N + 1 / 2 ≤ prwR large₂ * (wL.size - 1) := by
    have := hW.2.2.1
    unfold prwR
    linarith
  have hW' : G.TiedW S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) :=
    ⟨hW.1, hW.2.1, by linarith, hW.2.2.2⟩
  obtain ⟨-, -, -, hH1, hH2, -, hH4, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, PLam, lNc, hPL, hlNc, hI1, w2, hw2, t2, ht2, hnz2, hs2⟩ := hH4
  have hPI : PI4 D j PLam lNc ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) :=
    (auxiliaryCuspFormConstant_monotone D j hPL hlNc).trans (le_max_right _ _)
  have hsz : (0 : ℝ) ≤ wL.size := by linarith
  have hdm : (0 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := Nat.cast_nonneg _
  have hs2' : ∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤
      max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) * (WeightFamilies.dimY D j : ℝ) * wL.size := fun σ =>
    (hs2 σ).trans (by gcongr)
  have hth' : ∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF := fun i => hH2.2.1 (hTh i).1
  have hO2 : Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ PO D large₂ := by
    have hd : (0 : ℝ) < |(NumberField.discr T.Q.c.F : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero T.Q.c.F)
    rw [Real.log_rpow hd, one_div, inv_mul_eq_div]
    exact hO.2
  have hprw : 1 ≤ prwR large₂ := by unfold prwR; linarith
  obtain ⟨hA1, hA2⟩ := GlobalTheory.RunJoin.combAlg_of_tiedW D T h j hj ka wL wF S nus G _ _ _ hW hComb
  rcases lt_or_eq_of_le hj.2 with hjm | hjm
  · obtain ⟨hi, hec, -, hes, hea, hem⟩ := hEta hjm
    obtain ⟨w1, hw1, t1, ht1, hnz1, hs1⟩ := hI1 hjm
    refine hIndef D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (cc D large₂ C2 A2 7 wL) (thR wL) w1 t1
      (hn ▸ hw1) ht1 hnz1 (fun σ => (hs1 σ).trans (by gcongr)) hi hem hec.2 hes hc0 hcg (hA1 hjm) hlow hea
  · refine hDef D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (hA2 hjm) ?_
    intro σ hσ k x hx
    have h1 := hlow σ hσ k x hx
    have h2 : I2.phiFD ((T.U j σ).X k) (thR wL) x = 0 :=
      GlobalTheory.phiFD_eq_zero_at_last_index D T h j hj hjm _ _ _ (runOK_of_pageOK hP) σ hσ k x hx
    rw [h2, mul_zero, add_zero] at h1
    exact h1

end GlobalTheory.RunPrimeData
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.HeightTop.Ties

section

open ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.Height.OrderTieGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ordTieOn_of_valued {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (hl : LiesTotal Xo c (trivialClassCondition Xo c) PY lies)
    (hv : ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v →
      ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) →
      ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))),
        (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧
        ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧
          (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) :
    OrdTieOn h δ (trivialClassCondition Xo c) PY lies := by
  intro Z v la hd ho
  obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inl ⟨la, ho⟩)
  obtain ⟨hpos, hres⟩ := restrict_eq hd ho
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  have he0 : 0 < e := by omega
  have hO : OverLa la T.V (ψ.comp (algebraMap c.F (Om Z))) e := by
    refine ⟨he0, fun a => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [vV, vLa]
    · have := (hψ _ ((map_ne_zero (algebraMap c.F (Om Z))).2 ha)).trans (hres a ha)
      rw [he] at this
      exact_mod_cast this
  obtain ⟨η, hη⟩ := hl la T _ e hO y trivial
  refine ⟨PtV.mk la hO y trivial η hη, fun a n f hf h0 => ?_, fun a n f hf h0 _ => ?_⟩
  · change _ = _ * nval T.V e (evI y f)
    rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0, he, ← EReal.coe_mul,
      EReal.coe_eq_coe_iff]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    push_cast
    field_simp
  · change nval T.V e (evI y f) = ⊤
    rw [(hy a n f hf).1.2 h0, nval_zero]

end

theorem exists_unit_of_vV_eq_zero (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  obtain ⟨z, hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x := by
    obtain ⟨z, hz | hz⟩ := ValuationRing.isInteger_or_isInteger T.V x |>.elim
      (fun ⟨z, hz⟩ => (⟨z, Or.inl hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x ∨ algebraMap T.V T.Fr z = x⁻¹))
      (fun ⟨z, hz⟩ => ⟨z, Or.inr hz⟩)
    · exact ⟨z, hz⟩
    · have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
        rw [hz, map_inv₀]
        change (valV T.V x)⁻¹ = 1
        rw [h1, inv_one]
      have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
      have hu : IsUnit z := by
        by_contra hn
        exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
      obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      rw [map_units_inv, hz, inv_inv]
  have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
    rw [hz]; exact h1
  have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
  have hu : IsUnit z := by
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hz⟩

theorem exists_frameShift_ordTies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ (∀ (PY : HeightOneSpectrum (𝓞 c.F) → Type) (lies : ∀ la (T' : CDVR) (ι : c.F →+* T'.Fr), IntFr Xo c T' ι → PY la → Prop), LiesTotal Xo c (trivialClassCondition Xo c) PY lies → OrdTieOn h δ (trivialClassCondition Xo c) PY lies ∧ OrdTie h δ (trivialClassCondition Xo c) PY lies) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c hpq hgood hA _ h
  obtain ⟨δ, hv, hfin⟩ := exists_frameShift_frShFin E H Dw l Xo c hpq hgood hA h
  have hQZ : OrdTieQZ h δ := by
    intro Z v hd ht
    obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inr ht)
    have htriv : trivCls Xo c T _ y := by
      intro a ha
      have ha' : algebraMap c.F (Om Z) a ≠ 0 := (map_ne_zero _).2 ha
      refine exists_unit_of_vV_eq_zero T ((map_ne_zero _).2 ha) ?_
      have := (hψ _ ha').trans (ht a ha)
      exact_mod_cast this
    refine ⟨⟨T, _, y, htriv⟩, fun a n f hf h0 => ?_, fun a n f hf h0 => ?_⟩
    · change _ = nval T.V 1 (evI y f)
      rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0]
      simp
    · change nval T.V 1 (evI y f) = ⊤
      rw [(hy a n f hf).1.2 h0, nval_zero]
  refine ⟨δ, fun Z v hd ht => ?_, hQZ, fun PY lies hl => ?_, fun d hD => hfin d hD⟩
  · obtain ⟨q, hq, -⟩ := hQZ Z v hd ht
    exact ⟨q, hq⟩
  · have hOn := ordTieOn_of_valued hl hv
    exact ⟨hOn, hOn.ordTie⟩

theorem ordTies_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ [Fintype (Comp (Q.Xo j) Q.c)] (h : GenFrEx (Q.Xo j) Q.c), KapFG (Q.Xo j) Q.c ∧ (∃ d, KapTrdeg (Q.Xo j) Q.c d ∧ d + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j) ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) ∧ CompNe (Q.Xo j) Q.c ∧ ∃ δ : ∀ Z : Comp (Q.Xo j) Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Q.Dw j) → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ OrdTieOn h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ OrdTie h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data Q.c.F (Comp (Q.Xo j) Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro D Q hP j hj _ h
  obtain ⟨hgood, hA, -, -, -, -, hrk⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hP
  obtain ⟨hr, hr1, hdim⟩ := hrk j hj
  have h1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := hr ▸ hr1
  obtain ⟨hfg, htr⟩ := kap_fg_trdeg _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c
  obtain ⟨δ, hq, hqz, hon, hfin⟩ := exists_frameShift_ordTies _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1 hgood hA h
  have hl : LiesTotal (Q.Xo j) Q.c (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) := by
    unfold LiesTotal
    intros
    exact ⟨(), trivial⟩
  obtain ⟨ho, ht⟩ := hon _ _ hl
  exact ⟨hfg, ⟨_, htr, hdim⟩, hdim ▸ fnTrdeg_of _ _ _ htr,
    (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1).1, δ, hq, hqz, ho, ht, hfin⟩

end GlobalTheory.HeightTop.Ties
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.HeightTop.Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem evR_of_frMap (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c g z = φ (evR Xo c g y) := by
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [evR_eq_map_of_test_point hL hg q χ y₀ y hy₀,
    evR_eq_map_of_test_point hL hg q (φ.comp χ) y₀ z (frMap_trans _ _ _ χ φ _ _ _ hy₀ hyz)]
  rfl

theorem isFractionRing_chart {h : GenFrEx Xo c} (C : FChart h) : IsFractionRing C.R (Om C.Z) := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := C.frac x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
    change x = a / b
    rw [eq_div_iff hb0, e]⟩

theorem le_of_generic {h : GenFrEx Xo c} (C : FChart h) (σ : c.F →+* ℂ) (F : (C.R →ₐ[c.F] CAt σ) → ℝ)
    (hF : @Continuous _ _ (TopologicalSpace.induced (fun x (a : C.R) => Formalism.L2.PjFree.toC (x a)) inferInstance) _ F)
    (M : ℝ) (hM : ∀ (x : C.R →ₐ[c.F] CAt σ) (P : Om C.Z →+* ℂ), P ∈ T0.PT (Ω := Om C.Z) σ →
      (∀ a, Formalism.L2.PjFree.toC (x a) = P a) → F x ≤ M) (ψ : C.R →ₐ[c.F] CAt σ) : F ψ ≤ M := by
  letI : TopologicalSpace (C.R →ₐ[c.F] CAt σ) :=
    TopologicalSpace.induced (fun x (a : C.R) => Formalism.L2.PjFree.toC (x a)) inferInstance
  have hcl : IsClosed {x | F x ≤ M} := isClosed_le hF continuous_const
  refine hcl.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
  rw [nhds_induced, Filter.mem_comap] at ht
  obtain ⟨s, hs, hst⟩ := ht
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, u, hu, hIu⟩ := hs
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ a ∈ I, Metric.ball (Formalism.L2.PjFree.toC (ψ a)) ε ⊆ u a := by
    rw [Filter.eventually_all_finset]
    intro a _
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 (hu a)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (Metric.ball_subset_ball hε.2.le).trans hb
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  haveI := C.sm
  haveI := isFractionRing_chart C
  let φ : C.R →+* ℂ := ψ.toRingHom
  have hφ : φ.comp (algebraMap c.F C.R) = σ := RingHom.ext fun k => ψ.commutes k
  obtain ⟨P, hP, hPε⟩ := GlobalTheory.generic_points_dense GlobalTheory.exists_algIndep_tuple_near c.F C.R (Om C.Z) σ φ hφ I ε hε0
  let x : C.R →ₐ[c.F] CAt σ :=
    { (P.comp (algebraMap C.R (Om C.Z)) : C.R →+* ℂ) with
      commutes' := fun k => RingHom.congr_fun hP k }
  refine ⟨x, hst (hIu fun a ha => hε a ha ?_), hM x P hP fun a => rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hPε a ha

section Pin

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r}
  (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) {xR : ℝ}
  {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ} (hx : 0 < xR) (hfn : FnPin U xR fn)
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}

abbrev pn (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (g : Rul Xo c) (y : FrPt Xo c (CAt σ)) : ℝ :=
  ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) g y

include hU hx hfn

theorem pn_frBor_good (hd : Dom a n) (hg : g ∈ sec Xo c a n) {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') : pn fn σ a n g y' = pn fn σ a n g y := by
  obtain ⟨k, x, s, hs⟩ := (hU σ hσ).2.2.1 y
  have hs' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).2.1 _ _ _ _ _ hs hb
  have T := (GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn).2.1 σ hσ k x
  exact (T _ _ hs' a n hd g hg).trans (T _ _ hs a n hd g hg).symm

theorem pn_frBor (hd : Dom a n) (hg : g ∈ sec Xo c a n) {σ : c.F →+* ℂ}
    {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') : pn fn σ a n g y' = pn fn σ a n g y := by
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact pn_frBor_good hU hx hfn hd hg hσ hb
  · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    have hL := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
    obtain ⟨z, hz⟩ := hL.bc _ _ (conjAlg σ) y
    obtain ⟨z', hz'⟩ := hL.bc _ _ (conjAlg σ) y'
    have T := (GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn).2.2 σ
    exact ((T _ _ hz' a n g hg).symm.trans
      (pn_frBor_good hU hx hfn hd hg hσ' (frBor_of_frMap _ hb hz hz'))).trans (T _ _ hz a n g hg)

theorem pn_generic (hd : Dom a n) (hg : g ∈ sec Xo c a n) {h : GenFrEx Xo c}
    {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))} (hyP : ∀ Z, CBase h Z (yP Z))
    (C : FChart h) {σ : c.F →+* ℂ} (x : C.R →ₐ[c.F] CAt σ) (P : Om C.Z →+* ℂ) (hP : P ∈ T0.PT (Ω := Om C.Z) σ)
    (hxP : ∀ b, Formalism.L2.PjFree.toC (x b) = P b) {z : FrPt Xo c (CAt σ)} (hz : FrMap x C.y z) :
    pn fn σ a n g z = nrmC fn (yP C.Z) (wtZ a n) (valC h a n g C.Z) P := by
  obtain rfl : sgOf P = σ := hP
  have hL := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
  obtain ⟨w, hw⟩ := hL.bc _ _ (PAlg P) C.yg
  have h1 := frMap_trans _ _ _ _ _ _ _ _ C.gen hw
  obtain rfl : x = (PAlg P).comp C.R.val := AlgHom.ext hxP
  obtain rfl : z = w := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz h1
  rw [(GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise E H Dw l Xo c r U hU xR fn hx hfn h yP hyP).2.2 C.Z P a n g hg]
  exact pn_frBor hU hx hfn hd hg (frBor_of_frMap _ C.bor (hyP C.Z P) hw)

theorem pn_continuous (hg : g ∈ sec Xo c a n) {h : GenFrEx Xo c} (C : FChart h) {σ : c.F →+* ℂ}
    (y : (C.R →ₐ[c.F] CAt σ) → FrPt Xo c (CAt σ)) (hy : ∀ x, FrMap x C.y (y x)) :
    @Continuous _ _ (TopologicalSpace.induced (fun x (b : C.R) => Formalism.L2.PjFree.toC (x b)) inferInstance) _
      fun x => pn fn σ a n g (y x) := by
  letI : TopologicalSpace (C.R →ₐ[c.F] CAt σ) :=
    TopologicalSpace.induced (fun x (b : C.R) => Formalism.L2.PjFree.toC (x b)) inferInstance
  haveI := C.sm
  have hL := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
  have hc : ∀ b : C.R, Continuous fun x : C.R →ₐ[c.F] CAt σ => Formalism.L2.PjFree.toC (x b) := fun b =>
    (continuous_apply b).comp
      (continuous_induced_dom (f := fun (x : C.R →ₐ[c.F] CAt σ) (b : C.R) => Formalism.L2.PjFree.toC (x b)))
  have hf : ∀ i, Continuous fun x => |fn σ (y x) i| := fun i =>
    continuousOn_univ.1 (GlobalTheory.T.frameNorms_continuousOn_smoothChart E H Dw l Xo c r U hU xR fn hx hfn σ C.R C.y _ Set.univ (fun x => x) y
      (fun b => (hc b).continuousOn) (fun x _ => hy x) i)
  have hne := (GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn).1
  have e : (fun x => pn fn σ a n g (y x)) =
      fun x => ‖Formalism.L2.PjFree.toC (x (evR Xo c g C.y))‖ * ∏ i, |fn σ (y x) i|⁻¹ ^ ex Dw a n i := by
    funext x
    rw [← evR_of_frMap hL hg x (hy x)]
    rfl
  rw [e]
  exact (hc _).norm.mul (continuous_finsetProd _ fun i _ =>
    ((hf i).inv₀ fun x => abs_ne_zero.2 (hne _ _ _)).pow _)

end Pin

theorem supC_le_iSup_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → ∀ a n, Dom a n → ∀ (Z : Comp Xo c), ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g = evC h Z f → (∀ Z', Z' ≠ Z → evC h Z' g = 0) → ∀ σ : c.F →+* ℂ, BddAbove (Set.range fun P : T0.PT (Ω := Om Z) σ => nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P) ∧ Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n g ≤ ⨆ P : T0.PT (Ω := Om Z) σ, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn h yP hyP a n hd Z f hf g hg hgf hg0 σ
  have hgs := Formalism.L2.PjFree.cusp_le_sec Xo c U a n hg
  obtain ⟨hB, hS⟩ := GlobalTheory.T.pointwiseNorm_bddAbove_iSup_eq_cuspForm_supNorm E H Dw l Xo c r U hU xR fn hx hfn a n hd g hg
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  have hv : valC h a n f Z = valC h a n g Z := by unfold valC; rw [hgf]
  rw [hv, ← hS σ]
  have hbdd : BddAbove (Set.range fun P : T0.PT (Ω := Om Z) σ => nrmC fn (yP Z) (wtZ a n) (valC h a n g Z) P) := by
    refine ⟨supR Xo c fn σ a n g, ?_⟩
    rintro _ ⟨⟨P, hP⟩, rfl⟩
    obtain rfl : sgOf P = σ := hP
    dsimp only
    rw [(GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise E H Dw l Xo c r U hU xR fn hx hfn h yP hyP).2.2 Z P a n g hgs]
    exact le_ciSup (hB (sgOf P)) (yP Z P)
  have hnn : 0 ≤ ⨆ P : T0.PT (Ω := Om Z) σ, nrmC fn (yP Z) (wtZ a n) (valC h a n g Z) P :=
    Real.iSup_nonneg fun P => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _)
  refine ⟨hbdd, Real.iSup_le (fun y => ?_) hnn⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  change pn fn σ a n g y ≤ _
  rw [pn_frBor hU hx hfn hd hgs hb]
  by_cases hZ : C.Z = Z
  · subst hZ
    choose w hw using fun x : C.R →ₐ[c.F] CAt σ => hL.bc _ _ x C.y
    obtain rfl : z = w ψ := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz (hw ψ)
    refine le_of_generic C σ (fun x => pn fn σ a n g (w x)) (pn_continuous hU hx hfn hgs C w hw) _
      (fun x P hP hxP => ?_) ψ
    rw [pn_generic hU hx hfn hd hgs hyP C x P hP hxP (hw x)]
    exact le_ciSup hbdd ⟨P, hP⟩
  · have h1 : evR Xo c g C.yg = 0 := by
      rw [hL.wt a n g hgs _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      have := hg0 C.Z hZ
      unfold evC at this
      rw [this, mul_zero]
    have h2 : evR Xo c g C.y = 0 := by
      rw [evR_of_frMap hL hgs C.R.val C.gen] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c g z = 0 := by rw [evR_of_frMap hL hgs ψ hz, h2, map_zero]
    have h4 : pn fn σ a n g z = 0 := by
      change cabs (evR Xo c g z) * _ = 0
      rw [h3]
      exact mul_eq_zero_of_left (norm_zero (E := ℂ)) _
    rw [h4]
    exact hnn

end GlobalTheory.HeightTop.Generic

namespace GlobalTheory.HeightTop.Generic

open Formalism.BasicNotions Formalism.MainNotions

theorem supPTGe_of_fnPin : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))), (∀ Z, CBase hG Z (yP Z)) → ∀ ka : WeightFamilies.Wt D j, SupPTGe h j hG fn yP ka := by
  intro D T h j hj fn hfn hG yP hyP ka Z F hF hev
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ => h.unf j hj σ hσ
  have hFc : F.1 ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) T.Q.c (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
      (wtA ka) ka.n := cutR_le T.C j ka F.2
  obtain ⟨g, hg, h1, h0, hI⟩ := GlobalTheory.Reg.exists_cusp_restrict_comp_int _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU hG Z (wtA ka) ka.n F.1 hFc
  have hg' : g ∈ cutR T.C j ka := by
    rw [cutR_eq T.C hj]; exact hg
  have hx : 0 < xiR D := (GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.1
  refine ⟨⟨g, hg'⟩, ?_, ?_, fun sg => ?_⟩
  · intro la v hv
    have hFv := hF la v hv
    obtain ⟨⟨q, Tc, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
    change 0 ≤ nval Tc.V e (evI y g)
    change 0 ≤ nval Tc.V e (evI y F.1) at hFv
    rcases hI Tc io y with h2 | h2
    · rw [h2]; exact hFv
    · rw [h2, nval_zero]; exact le_top
  · intro h2
    have h3 : g = 0 := congrArg Subtype.val h2
    apply hev
    change evC hG Z F.1 = 0
    rw [← h1, h3, evC_zero]
  · have h4 := (GlobalTheory.HeightTop.Generic.supC_le_iSup_generic _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU (xiR D) fn hx hfn hG yP hyP (wtA ka) ka.n (dom_wtA ka) Z
      F.1 hFc g hg h1 h0 sg).2
    change cutN T.C T.Ns j ka sg ⟨g, hg'⟩ ≤ _
    unfold cutN
    rw [if_pos hj]
    exact h4

theorem exists_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR)
    (hfn : GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) xR fn)
    (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) :
    ∃ (k : (U (goodOf c σ)).Comp) (x : ((U (goodOf c σ)).X k).dom), ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n,
      Formalism.L2.Pj.ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y =
        recNrm (U (goodOf c σ)) xR a n f k x.1 := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm E H Dw l Xo c r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hU xR fn hx hfn
  have hg := goodEmb_goodOf c σ
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    rw [e]
    obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
    exact ⟨k, x, fun a n hd f hf => h2 σ hσ k x t y ht a n hd f hf⟩
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    rw [e] at hg ⊢
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _
      (conjAlg σ) y
    obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 y'
    exact ⟨k, x, fun a n hd f hf => (h3 σ y y' hy' a n f hf).symm.trans (h2 _ hg k x t y' ht a n hd f hf)⟩

theorem nrmTieU_of_fnPin (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j)
    (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ)
    (hfn : GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P)))
    (hyP : ∀ Z, CBase hG Z (yP Z)) (N : ℕ) (wR : Fin (N + 1) → T.R j) (uL : WtR D.host.E) (etR : T.R j)
    (uet : WtR D.host.E) (hL : Dom uL.1 uL.2) (he : Dom uet.1 uet.2)
    (hw : ∀ k, wR k ∈ sec (T.Q.Xo j) T.Q.c uL.1 uL.2) (het : etR ∈ sec (T.Q.Xo j) T.Q.c uet.1 uet.2) :
    NrmTieU hG fn yP (T.U j) (xiR D) wR uL etR uet := by
  intro Z P
  have hx : 0 < xiR D := (GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.1
  have hU := h.unf j hj
  have h3 := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ (T.Q.Xo j) T.Q.c _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU (xiR D) fn hx hfn hG yP hyP).2.2
  obtain ⟨k, x, hkx⟩ := exists_frame (T.U j) hU (xiR D) fn hx hfn (sgOf P) (yP Z P)
  have key : ∀ a n, Dom a n → ∀ F ∈ sec (T.Q.Xo j) T.Q.c a n,
      nrmC fn (yP Z) (wtZ a n) (valC hG a n F Z) P = recNrm (T.U j (goodOf T.Q.c (sgOf P))) (xiR D) a n F k x.1 :=
    fun a n hd F hF => (h3 Z P a n F hF).trans (hkx a n hd F hF)
  exact ⟨goodOf T.Q.c (sgOf P), goodEmb_goodOf _ _, k, x.1, x.2, fun i => key _ _ hL _ (hw i), (key _ _ he _ het).le⟩

end GlobalTheory.HeightTop.Generic
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LowerBoundCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

variable {D : D7} {T : Core D}

theorem conjEmb_invol {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem wtA_conj_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h =>
    GlobalTheory.LeafCompare.tauEmb_ne_conj Q hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (GlobalTheory.LeafCompare.tauEmb_inj (by
        rw [← conjEmb_invol (DV.tauEmb D t'), ← h, conjEmb_invol]))
    simp [h1, this]
  · simp

theorem wt_ext (Q : Par D) (hp : Q.PinHost) {j : ℕ} {w w' : WeightFamilies.Wt D j} (hA : wtA w = wtA w') (hn : w.n = w'.n) :
    w = w' := by
  have hP : w.aP = w'.aP := by
    funext t i
    have := congrFun hA (DV.tauEmb D t, i.1)
    rw [GlobalTheory.LeafCompare.wtA_tau Q hp, GlobalTheory.LeafCompare.wtA_tau Q hp] at this
    simpa [ext0, i.2] using this
  have hM : w.aM = w'.aM := by
    funext t i
    have := congrFun hA (conjEmb (DV.tauEmb D t), i.1)
    rw [wtA_conj_tau Q hp, wtA_conj_tau Q hp] at this
    simpa [ext0, i.2] using this
  cases w
  cases w'
  simp only at hP hM hn
  subst hP hM hn
  rfl

theorem wtA_wsmul_apply {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (WeightAlgebra.wsmul k w) x = k * wtA w x := by
  have h0 : ∀ {p : ℕ} (f : Fin p → ℕ) (i : ℕ), ext0 (fun s => k * f s) i = k * ext0 f i := by
    intro p f i
    unfold ext0
    split_ifs <;> simp
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wsmul k w).aP t) x.2 = k * ext0 (w.aP t) x.2 := h0 _ _
  have h2 : ext0 ((WeightAlgebra.wsmul k w).aM t) x.2 = k * ext0 (w.aM t) x.2 := h0 _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]

theorem eq_wsmul_iff (h : LawsCore T) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (n : ℕ) :
    wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n ↔ ka = WeightAlgebra.wsmul n wL := by
  constructor
  · intro H
    refine wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
    · have : (wtA ka x : ℤ) = n • (wtA wL x : ℤ) := congrFun (congrArg Prod.fst H) x
      rw [nsmul_eq_mul] at this
      rw [wtA_wsmul_apply]
      exact_mod_cast this
    · have : (ka.n : ℤ) = n • (wL.n : ℤ) := congrArg Prod.snd H
      rw [nsmul_eq_mul] at this
      show ka.n = n * wL.n
      exact_mod_cast this
  · rintro rfl
    refine Prod.ext (funext fun x => ?_) ?_
    · simp only [wtZ, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, wtA_wsmul_apply]
      push_cast
      rfl
    · simp only [wtZ, Prod.smul_snd, nsmul_eq_mul]
      show ((n * wL.n : ℕ) : ℤ) = _
      push_cast
      rfl

def DensityWith (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) (R : Comp (T.Q.Xo j) T.Q.c → T.R j → T.R j → Prop) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (F : (recB h).Cusp j ka), F ∈ (recB h).Mlat j ka → evC hG Z (F : T.R j) ≠ 0 →
    ∃ F' ∈ (recB h).Mlat j ka, F' ≠ 0 ∧ R Z (F : T.R j) (F' : T.R j) ∧
      ∀ σ : T.Q.c.F →+* ℂ, (recB h).supN j ka σ F' ≤ genSup hG fn yP ka (F : T.R j) Z σ

section Density

variable (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
  (ka : WeightFamilies.Wt D j)

theorem DensityWith.mono {R R' : Comp (T.Q.Xo j) T.Q.c → T.R j → T.R j → Prop}
    (hR : ∀ Z f f', R Z f f' → R' Z f f') (H : DensityWith h j hG fn yP ka R) : DensityWith h j hG fn yP ka R' := by
  intro Z F hF hZ
  obtain ⟨F', h1, h2, h3, h4⟩ := H Z F hF hZ
  exact ⟨F', h1, h2, hR _ _ _ h3, h4⟩




end Density

section Separate

variable {j : ℕ}

def rescale (fn : FrameNorms T j) (a : T.Q.c.F) : FrameNorms T j := fun σ y i =>
  match i with
  | none => fn σ y none / ‖σ a‖
  | some u => fn σ y (some u)







end Separate



end GlobalTheory.LowerBoundCompare
end
end

section
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.T0 (meanK PT)

namespace GlobalTheory.HeightTop

theorem nonempty_place (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem meanK_le_const {K : Type} [Field K] [NumberField K] {F : (K →+* ℂ) → ℝ} {b : ℝ} (h : ∀ sg, F sg ≤ b) :
    meanK F ≤ b := by
  unfold meanK
  have hn : (0 : ℝ) < Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
  rw [div_le_iff₀ hn]
  calc ∑ sg, F sg ≤ ∑ _sg : K →+* ℂ, b := Finset.sum_le_sum fun sg _ => h sg
    _ = b * Fintype.card (K →+* ℂ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

section Weights

variable {D : D7} {j : ℕ}

theorem extendByZero_add_eq_mul_of_forall {p : ℕ} {f g k : Fin p → ℕ} {m : ℕ} (h : ∀ i, f i + g i = m * k i) (i : ℕ) :
    ext0 f i + ext0 g i = m * ext0 k i := by
  unfold ext0; split_ifs
  · exact h _
  · simp

theorem wtA_add_eq {a b w : WeightFamilies.Wt D j} {m : ℕ} (hP : ∀ τ i, a.aP τ i + b.aP τ i = m * w.aP τ i)
    (hM : ∀ τ i, a.aM τ i + b.aM τ i = m * w.aM τ i) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA a x + wtA b x = m * wtA w x := by
  simp only [wtA, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := extendByZero_add_eq_mul_of_forall (hP t) x.2
  have h2 := extendByZero_add_eq_mul_of_forall (hM t) x.2
  split_ifs <;> simp only [mul_add, mul_zero, add_zero, zero_add] <;> omega

theorem wtA_wscalar (n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp [wtA, wscalar, ext0]

theorem wtZ_wEt (i : ℕ) :
    wtZ (wtA (wEt D j i)) (wEt D j i).n = (i * WeightAlgebra.g0 D) • wtZ (E := D.host.E) 0 1 := by
  refine Prod.ext (funext fun x => ?_) ?_
  · simp [wtZ, wEt, wtA_wscalar]
  · show ((WeightAlgebra.g0 D * i : ℕ) : ℤ) = (i * WeightAlgebra.g0 D) • ((1 : ℕ) : ℤ)
    rw [nsmul_eq_mul]; push_cast; ring

theorem weightSumVector_firstGeneratorWeight {wL w1 : WeightFamilies.Wt D j} (h : IsDoubledWeightWithShift wL w1 wL.n) :
    wtZ (wtA w1) w1.n = (2 : ℕ) • (wtZ (wtA wL) wL.n - wtZ (E := D.host.E) 0 1) := by
  refine Prod.ext (funext fun x => ?_) ?_
  · have := wtA_add_eq (a := w1) (b := wscalar D j 0 ⟨0, rfl⟩) (w := wL) (m := 2)
      (fun τ i => by simpa [wscalar] using h.2.1 τ i) (fun τ i => by simpa [wscalar] using h.2.2 τ i) x
    rw [wtA_wscalar 0 ⟨0, rfl⟩ x, add_zero] at this
    show (wtA w1 x : ℤ) = (2 : ℕ) • ((wtA wL x : ℤ) - ((0 : ℕ) : ℤ))
    rw [this, nsmul_eq_mul]; push_cast; ring
  · have := h.1
    show (w1.n : ℤ) = (2 : ℕ) • ((wL.n : ℤ) - ((1 : ℕ) : ℤ))
    rw [nsmul_eq_mul]; push_cast; omega

theorem weightSumVector_secondGeneratorWeight_definite {wL wF w2 : WeightFamilies.Wt D j} (h : IsG2 wL wF w2) :
    wtZ (wtA w2) w2.n = (WeightFamilies.dimY D j + 4 : ℕ) • wtZ (wtA wL) wL.n - wtZ (wtA wF) wF.n := by
  refine Prod.ext (funext fun x => ?_) ?_
  · have := wtA_add_eq h.2.1 h.2.2 x
    show (wtA w2 x : ℤ) = (WeightFamilies.dimY D j + 4 : ℕ) • (wtA wL x : ℤ) - (wtA wF x : ℤ)
    rw [nsmul_eq_mul, eq_sub_iff_add_eq]; exact_mod_cast this
  · have := h.1
    show (w2.n : ℤ) = (WeightFamilies.dimY D j + 4 : ℕ) • (wL.n : ℤ) - (wF.n : ℤ)
    rw [nsmul_eq_mul, eq_sub_iff_add_eq]; exact_mod_cast this

end Weights

section Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

theorem nzAt_of_nonZeroComp (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  intro Z h0
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  obtain ⟨H, hH⟩ := (recPlus h j hj).inc_mul u wL F g
  have hH0 : H = 0 := by
    refine hV _ H fun Z' => ?_
    have e := congrArg (formsEvR j hG hT Z') hH
    erw [map_mul, formsEvR_inc h j hj hG hT Z' u F, formsEvR_inc h j hj hG hT Z' wL g,
      formsEvR_inc h j hj hG hT Z' _ H] at e
    rw [← e]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [e2 Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have hg := hF wL g hH
  apply hk
  rw [← e1, hg]
  exact evC_zero hG Z

theorem log_iSup_le [Fintype (Comp (T.Q.Xo j) T.Q.c)] (hV : GenValInjSt h j hG)
    {fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ}
    {yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))}
    (hfn : FnNe (T.Q.Xo j) T.Q.c fn) (hPT : PTNe (T.Q.Xo j) T.Q.c) (hcx : ValAtCx hG yP)
    {w : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (hB : SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧
      ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F) (σ : T.Q.c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp (T.Q.Xo j) T.Q.c, PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) (wtZ (wtA w) w.n) (valC hG (wtA w) w.n F.1 p.1) p.2) ≤
      Real.log ((recB h.toLawsCore).supN j w σ F) := by
  by_cases hN : NZSome hG F.1
  · rw [← hB.2 σ]
    exact log_supN_le hfn hPT hcx (cusp_le_sec _ _ (T.U j) _ _ (cutR_le T.C j w F.2)) hB.1 hN σ
  · have hz : ∀ Z, evC hG Z F.1 = 0 := fun Z => by
      by_contra h0
      exact hN ⟨Z, h0⟩
    have hF : F = 0 := hV w F hz
    have e1 : (recB h.toLawsCore).supN j w σ F = 0 := ((recB h.toLawsCore).supN_eq_zero _ _ _ _).2 hF
    have e2 : ∀ p : (Σ Z : Comp (T.Q.Xo j) T.Q.c, PT (Ω := Om Z) σ),
        nrmC fn (yP p.1) (wtZ (wtA w) w.n) (valC hG (wtA w) w.n F.1 p.1) p.2 = 0 := fun p => by
      unfold valC
      rw [nrmC_single, hz, map_zero, norm_zero, zero_mul]
    rw [e1]
    simp only [e2, Real.iSup_const_zero, le_refl]

end Rec

section Integral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ord_nonneg_of_regP {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hreg : regular₂ Xo c U) {h : GenFrEx Xo c}
    {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    (hT : OrdTie h δ (trivialClassCondition Xo c) (fun _ => Unit) (fun _ _ _ _ _ => True)) (hTQ : OrdTieQ h δ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdom : Dom a n) {F : Rul Xo c} (hFC : F ∈ cusp Xo c U a n) (hF : IntAlg F)
    [Fintype (Comp Xo c)]
    {d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)}
    {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)} (hA : d.admitted Z v) (hne : evC h Z F ≠ 0) :
    0 ≤ ordC (δ Z v) v (wtZ a n) (valC h a n F Z) := by
  have hFs := cusp_le_sec Xo c U a n hFC
  have key : (0 : EReal) ≤ (((ordC (δ Z v) v (wtZ a n) (valC h a n F Z) : ℤ) : ℝ) : EReal) := by
    obtain ⟨hd, ⟨la, ho, -⟩ | ⟨ht, -⟩⟩ := hA
    · obtain ⟨y, hy⟩ := hT Z v la hd ho
      rw [hy a n F hFs hne]
      exact mul_nonneg (by exact_mod_cast ramIdx_nonneg ho)
        (hreg.int hdom hFC hF la _ (vAtV_mem_valSet (fun _ _ _ h => h) y))
    · obtain ⟨q, hq⟩ := hTQ Z v hd ht
      rw [hq a n F hFs hne]
      have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
        refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
        obtain ⟨u, hu⟩ := q.triv a ha
        rw [← hu]
        exact extVal_unit_zero q.T u
      exact (hreg.1.1 ⟨(a, n), hdom⟩ ⟨F, hFC⟩ fun la y => hF la y.1 y.2).2 ⟨_, hqT⟩
  exact_mod_cast key

end Integral

theorem heights_indefinite :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hV hC hB y hw hcur htie hjm hac hD3 hn0 hIB large₂ Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL nus w2 t2 hTW hTT hthM hG2 ht2M ht2N ht2S hH1 hPN hLAM hLC hsz hDF hrw hnK hrd p1 p2 p3 p4 p5 p6 p7 p8 p9 hPH c th w1 t1 hG1 ht1M ht1N ht1S hi hetM hetN hetS hc0 hcg hcomb hI2 harch
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 T.Q.c.F)) := nonempty_place _
  have hgt : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hx : 0 < xiR D := (GlobalTheory.PinNum.xiR_pos_le_one D T.Q h.pins.1).1
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ => h.unf j hj σ hσ
  obtain ⟨hkfg, ⟨d0, hd0, hd0'⟩, htr, hne, δ, hTQ, hTQZ, hTOn, hT, hFr⟩ := Ties.ordTies_of_pins D T.Q h.pins j hj hG
  have hreg := h.reg j hj
  obtain ⟨fn, hpin, hfn⟩ := GlobalTheory.FrameNorm.Existence.exists_pinned _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r _ hU (xiR D) hx
  obtain ⟨yP, hyP, hcx, -⟩ := GlobalTheory.Reg.exists_cBase_valAtCx _ _ _ _ (T.Q.Xo j) T.Q.c
    (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1 hG
  have hconj := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r _ hU (xiR D) fn hx hpin
    hG yP hyP).1
  have hsup := (GlobalTheory.FrameNorm.RecSup.supBdd_and_supR_eq_supN D T h j hj fn hpin).2.1
  have hfg := fnFG_of _ _ hkfg
  have hPT := ptNe_of_fnFG hfg
  have hdim : WeightFamilies.dimY D j = (T.Q.Dw j).dim + Nat.card (FlagVar (T.Q.Dw j)) := by
    obtain ⟨Z⟩ := hne
    have e := (hd0 Z).symm.trans ((GlobalTheory.Reg.kap_fg_trdeg _ _ _ _ (T.Q.Xo j) T.Q.c).2 Z)
    have e' : d0 = (T.Q.Dw j).dim := by exact_mod_cast e
    rw [← hd0', e']
  choose k0 hk0 hk0' using hH.2.1.2
  obtain ⟨N, hN⟩ : ∃ N, N + 1 = G.N := by
    obtain ⟨Z⟩ := hne
    exact ⟨G.N - 1, by have := (k0 Z).2; omega⟩
  let eN : Fin (N + 1) ≃ Fin G.N := finCongr hN
  let wR : Fin (N + 1) → T.R j := fun k => (G.w (eN k)).1
  let jc : Comp (T.Q.Xo j) T.Q.c → Fin (N + 1) := fun Z => eN.symm (k0 Z)
  let wsize : WTZ D.host.E → ℝ := fun g => if g = wtZ (wtA wL) wL.n then wL.size else wF.size
  have hsL : wsize (wtZ (wtA wL) wL.n) = wL.size := if_pos rfl
  have hsF : wsize (wtZ (wtA wF) wF.n) = wF.size := by
    by_cases e : wtZ (wtA wF) wF.n = wtZ (wtA wL) wL.n
    · have e1 : wF = wL := by
        refine GlobalTheory.LowerBoundCompare.wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
        · have : (wtA wF x : ℤ) = wtA wL x := congrFun (congrArg Prod.fst e) x
          exact_mod_cast this
        · have : (wF.n : ℤ) = wL.n := congrArg Prod.snd e
          exact_mod_cast this
      rw [e, hsL, e1]
    · exact if_neg e
  have hwb : ∀ Z, evC hG Z (wR (jc Z)) ≠ 0 := fun Z => by
    simp only [wR, jc, Equiv.apply_symm_apply]
    exact hk0 Z
  have hcu : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F.1 ∈ T.cuspA j (wtA w) w.n :=
    fun w F => cutR_le T.C j w F.2
  have hse : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    fun w F => cusp_le_sec _ _ (T.U j) _ _ (hcu w F)
  have hin : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), F ∈ (recB h.toLawsCore).Mlat j w → IntAlg F.1 :=
    fun w F hF => hF
  have hetZ := nzAt_of_nonZeroComp h j hj hG hV hC G hH.2.1 _ hetN
  have h1Z := nzAt_of_nonZeroComp h j hj hG hV hC G hH.2.1 _ ht1N
  have h2Z := nzAt_of_nonZeroComp h j hj hG hV hC G hH.2.1 _ ht2N
  have huet := wtZ_wEt (D := D) (j := j) G.iet
  have hu1 := weightSumVector_firstGeneratorWeight hG1
  have hu2 := weightSumVector_secondGeneratorWeight_definite hG2
  have hnz : NoCommonZero (T.Q.Xo j) T.Q.c wR := by
    intro k _ _ _ z
    obtain ⟨i, hi⟩ := hH.2.1.1 k z
    exact ⟨eN.symm i, by simpa only [wR, Equiv.apply_symm_apply] using hi⟩
  have hcomb' : CombAlg (T.Q.Xo j) T.Q.c wR G.et.1 nus (c / (2 * (G.iet : ℝ))) := by
    intro la v hv
    have e : (⨅ k, v (wR k)) = ⨅ k, v (G.w k).1 := eN.iInf_comp (g := fun k => v (G.w k).1)
    rw [e]
    exact hcomb la v hv
  obtain ⟨hnu, hnu'⟩ := GlobalTheory.numerical_h_one_of_weighted_bound D T h j hj large₂ wL nus hH1
  have hg0 : 1 ≤ WeightAlgebra.g0 D := by
    have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.dimPos_fr D).2
    unfold WeightAlgebra.g0
    omega
  let d := dataOf hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
  have hwe : ∀ k, d.w (eN.symm k) = valC hG (wtA wL) wL.n (G.w k).1 := fun k => by
    show valC hG (wtA wL) wL.n (G.w (eN (eN.symm k))).1 = _
    rw [Equiv.apply_symm_apply]
  have ha1 : A1Bigness d := GlobalTheory.BigRec.independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G d eN.symm rfl hwe (fun Z => valC_ne_zero (hwb Z))
    (fun Z => ⟨k0 Z, hk0 Z, hk0' Z⟩)
  obtain ⟨eD, heD⟩ := GlobalTheory.SectionBasis.chosenForms_restrict_basis_functionField D T h j hj hG ka wL wF G S g0 (Classical.arbitrary _) d eN.symm rfl hwe
    (fun Z => valC_ne_zero (hwb Z)) hH (hIB _)
  have ha4 : A4Selection d eD := heD eD (fun _ => rfl) rfl
  have hdel : d.del = G.del := by simpa using Fintype.card_congr eD
  have hdel1 : 1 ≤ d.del := by
    obtain ⟨e, -, -, h3⟩ := ha4
    obtain ⟨q, hq, p, hp⟩ := h3 (fun _ => 1)
    obtain ⟨Z⟩ := hne
    by_contra h0
    have : IsEmpty (Fin d.del) := ⟨fun i => by have := i.2; omega⟩
    have h4 := hp Z
    rw [mul_one, Finset.univ_eq_empty, Finset.sum_empty] at h4
    exact hq Z h4
  have hn96 : d.n96 = 8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊) := by
    rw [← hdel, ← hN]; rfl
  have hn1 : 1 ≤ d.n96 := by
    have : 0 < d.del := hdel1
    show 0 < 8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊)
    positivity
  rw [← hn96] at hLAM hLC
  obtain ⟨-, -, hDF', hST⟩ := GlobalTheory.Reg.kap_divFin_stLoc_dataOf _ _ _ _ (T.Q.Xo j) T.Q.c hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (by omega) hdim hwb ha1
  have hbdd : LawBdd d := GlobalTheory.Reg.LawBddPf.lawBdd_dataOf _ _ _ _ (T.Q.Xo j) T.Q.c hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    hcx (fun k => ⟨hse _ _, (hsup _ _).1⟩) (fun k => ⟨hse _ _, (hsup _ _).1⟩) ⟨hse _ G.et, (hsup _ G.et).1⟩
    ⟨hse _ _, (hsup _ _).1⟩ ⟨hse _ _, (hsup _ _).1⟩ huet hu1 hu2
  have ha2 : A2RegularityOrders d := by
    refine ⟨fun Z v hA x hx hx0 => ?_, fun Z v hA x hx hx0 => ?_, fun Z v hA => ?_, fun Z v hA => ?_,
      fun Z v hA => ?_⟩
    · obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG hG hx
      exact ord_nonneg_of_regP hreg hT hTQ (dom_wtA wL)
        (mem_of_mem_span_int _ (Set.range_subset_iff.2 fun k => hcu _ (G.w (eN k))) hF)
        (intAlg_span (Set.forall_mem_range.2 fun k => hin _ _ (hTW.2.1 (eN k))) hF) hA (evC_ne_zero_of_valC hx0)
    · obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG hG hx
      exact ord_nonneg_of_regP hreg hT hTQ (dom_wtA wF)
        (mem_of_mem_span_int _ (Set.range_subset_iff.2 fun k => hcu _ (G.th' k)) hF)
        (intAlg_span (Set.forall_mem_range.2 fun k => hin _ _ (hthM k)) hF) hA (evC_ne_zero_of_valC hx0)
    · have h0 := ord_nonneg_of_regP hreg hT hTQ (dom_wtA (wEt D j G.iet)) (hcu _ G.et) (hin _ _ hetM) hA (hetZ Z)
      rw [huet] at h0
      exact h0
    · have h0 := ord_nonneg_of_regP hreg hT hTQ (dom_wtA w1) (hcu _ t1) (hin _ _ ht1M) hA (h1Z Z)
      rw [hu1] at h0
      exact h0
    · have h0 := ord_nonneg_of_regP hreg hT hTQ (dom_wtA w2) (hcu _ t2) (hin _ _ ht2M) hA (h2Z Z)
      rw [hu2] at h0
      exact h0
  have ha3 : LawA3' d := lawA3'_dataOf hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 hDF' (hFr d hDF')
  have ha13 : A13Measurable d := lawA13_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (nrmContOff_of hG fn yP _ _ _ _ _ hST
      (GlobalTheory.T.frameNorms_continuous_along_embedding_families _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r _ hU (xiR D) fn hx hpin hG yP hyP).1 hfn htr hfg hwb)
  have hnum : NumOK d := by
    have hg0' : (1 : ℝ) ≤ WeightAlgebra.g0 D := by exact_mod_cast hg0
    refine ⟨hD3, hi, hg0, hc0, ?_, hcg, ?_, ?_, ?_, hnK, hrd, p1, le_rfl, le_rfl, p2, le_rfl, p3, p4, p5, p6, p7,
      p8, p9⟩
    · show c ≤ 1
      nlinarith
    · show 1 ≤ wsize (wtZ (wtA wL) wL.n)
      rw [hsL]; exact hsz
    · show (WeightAlgebra.DF wL : ℝ) ≤ wsize (wtZ (wtA wL) wL.n)
      rw [hsL]; exact hDF
    · show Real.log (N + 1 : ℕ) + 1 / 2 ≤ Prw * (wsize (wtZ (wtA wL) wL.n) - 1)
      rw [hsL, hN]; exact hrw
  have iH1 : d.FinitePlaceHyp := height_H1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (T.U j) hreg (dom_wtA wL) (dom_wtA (wEt D j G.iet)) (fun k => hcu _ _) (hcu _ G.et) hnz hetZ hwb huet hc0
    (by rw [hnu']; exact hcomb') _ _ _ hTOn (by
      show NumericalH1Condition _ _ PN' (wsize (wtZ (wtA wL) wL.n))
      rw [hsL]
      exact ⟨hnu.1, hnu.2.1, hnu.2.2.trans (mul_le_mul_of_nonneg_right hPN (by linarith))⟩)
  have iF1d : d.TrivialPlaceHyp := height_F1_of_data hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    (T.U j) hreg hTQZ (dom_wtA wL) (dom_wtA (wEt D j G.iet)) (fun k => hcu _ _) (hcu _ G.et) hnz hetZ huet hc0
    nus hcomb'
  have hkaZ : wtZ (wtA (wsmul d.n96 wL)) (wsmul d.n96 wL).n = d.n96 • wtZ (wtA wL) wL.n :=
    (GlobalTheory.LowerBoundCompare.eq_wsmul_iff h.toLawsCore _ wL _).2 rfl
  have iLAM : d.HtLAM := htLAM_of h.toLawsCore j hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    large₂ CL AL (wsmul d.n96 wL) hgt hkaZ hLAM
    (prodInLat_of_wtZ h.toLawsCore j hj wR wL _ _ (fun k => ⟨G.w (eN k), hTW.2.1 _, rfl⟩) hn1 hkaZ)
    (Generic.supPTGe_of_fnPin D T.toCore h.toLawsCore j hj fn hpin hG yP hyP _) (by
      show LamConst j large₂ CL AL _ PP0' d.n96 (wsize (wtZ (wtA wL) wL.n))
      rw [hsL]; exact hLC)
  have hlog := fun (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) (σ : T.Q.c.F →+* ℂ) =>
    log_iSup_le h j hG hV hfn hPT hcx F (hsup w F) σ
  have iSup' : d.HtSup := by
    refine ⟨?_, fun k => ?_, ?_, ?_⟩
    · show _ ≤ Gc * wsize (wtZ (wtA wL) wL.n)
      rw [hsL]
      refine (meanK_mono' fun σ => ?_).trans hTW.2.2.2.2
      exact ciSup_le fun k => (hlog _ (G.w (eN k)) σ).trans (hTW.2.2.2.1 σ _)
    · show _ ≤ Gc * wsize (wtZ (wtA wF) wF.n)
      rw [hsF]
      exact (meanK_mono' fun σ => hlog _ (G.th' k) σ).trans (hTT k).2
    · show _ ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wsize (wtZ (wtA wL) wL.n)
      rw [hsL]
      refine meanK_le_const fun σ => le_trans ?_ (ht1S σ)
      have h1 := hlog _ t1 σ
      rw [hu1] at h1
      exact h1
    · show _ ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wsize (wtZ (wtA wL) wL.n)
      rw [hsL]
      refine meanK_le_const fun σ => le_trans ?_ (ht2S σ)
      have h1 := hlog _ t2 σ
      rw [hu2] at h1
      exact h1
  have iet : d.HeightIntegralEstimateTrivialPlace := by
    refine htI2et_of_pt d fun σ => le_trans ?_ (hetS σ)
    have h1 := hlog (wEt D j G.iet) G.et σ
    rw [huet] at h1
    exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
  have ibe : d.HeightIntegralBoundEstimate := by
    have h3 := Generic.nrmTieU_of_fnPin D T.toCore h.toLawsCore j hj fn hpin hG yP hyP
    refine htI2be_of hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0 (T.U j) (xiR D) th hi hc0 hfn hetZ huet
      (h3 N wR _ _ _ (dom_wtA wL) (dom_wtA (wEt D j G.iet)) (fun k => hse _ _) (hse _ G.et)) ?_
      (fun σ hσ k x hx => harch σ hσ k x hx)
    intro σ hσ k x hx
    have e : ∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (wR k') k x ^ 2 =
        ∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2 :=
      eN.sum_comp (fun k' => recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)
    have h1 := hI2 σ hσ k x hx
    rw [← e] at h1
    exact h1
  let hd : d.AxH (fun Z => AG Z) := axHOf hG δ fn yP (WeightFamilies.dimY D j) N 0 G.iet (WeightAlgebra.g0 D) c (wtA wL, wL.n) (wtA wF, wF.n) (wtA wL, wL.n) (0, 1) (wtA (wEt D j G.iet), (wEt D j G.iet).n) (wtA w1, w1.n) (wtA w2, w2.n) wR jc G.del (fun i => (G.th' i).1) 0 Fin.elim0 (wtA wL, wL.n) 0 Fin.elim0 ∅ G.et.1 t1.1 t2.1 (nuOf T.Q.c fun la => nus la / (ramOverZ la : ℝ)) (fun _ _ _ => 0) wsize (WeightAlgebra.DF wL : ℝ) PN' 1 1 PP0' 1 Gc PI4' Pet tableLineDegreeFive tableLineDegreeTwo Prw POb 0 0
    hne hfg htr hac hwb hetZ h1Z h2Z huet hu1 hu2 hfn hconj hbdd ha1 ha2 ha3 eD ha4 hnum ha13
  have hsel : hd.sel = eD := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hnum
    rfl
  have hs := d.genericSection_of_axioms hd
  have hcon := d.heights hd hs iH1 iF1d iLAM iSup' iet ibe
  refine Formalism.MainNotions.Gaps.HeightData.heights_of_htConcl G _ Gc PH Prw Pet
    (htConcl_toHtData_of (B := recB h.toLawsCore) d hd hs G _ Gc PH Prw Pet rfl hdel rfl rfl hsL rfl hPH.symm rfl rfl
      ?_ ?_ ?_ hcon)
  · rw [← eD.sum_comp]
    refine Finset.sum_le_sum fun k _ => ?_
    show meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) ≤ _
    rw [hsel]
    exact meanK_mono' fun σ => hlog _ (G.th' (eD k)) σ
  · exact GlobalTheory.T.lengths_at_primes_le_functionField_data_of_curve D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie δ hT d hd hs eN rfl
      (fun _ _ => rfl) rfl rfl (fun _ => rfl) eD (fun k => by rw [hsel]; rfl) Gc PH Prw Pet
  · exact GlobalTheory.T.orders_auxiliary_form_at_primes_eq_functionField D T h j hj hG ka wL wF G S g0 hH hV hC hB y hw hcur htie hjm δ hT d hd hs eN rfl
      (fun _ _ => rfl) rfl rfl (fun _ => rfl) rfl huet.symm Gc PH Prw Pet

end GlobalTheory.HeightTop
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightInequalities_indefinite_liftIndex : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (T.Q.Xo j) T.Q.c → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  atlas_forward_decl GlobalTheory.HeightTop.heights_indefinite
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_primeData_heights : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (T.Q.Xo j) T.Q.c → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) :=
  exists_primeData_heights_of GlobalTheory.T.heightInequalities_indefinite_liftIndex GlobalTheory.T.heightInequality_definite_liftIndex GlobalTheory.T.exists_realisationPrimeData_curve_lifting

end GlobalTheory.RunPrimeData
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeData_curve_lifting_heightBounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (T.Q.Xo j) T.Q.c → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  atlas_forward_decl GlobalTheory.RunPrimeData.exists_primeData_heights
end
