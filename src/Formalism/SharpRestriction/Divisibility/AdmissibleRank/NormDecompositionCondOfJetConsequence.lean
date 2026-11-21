import Mathlib
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutKapD
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.LogDiscriminantLeSquareSizeFamily
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutDivD
import Formalism.SharpRestriction.Divisibility.ChainOperators.RankInputBounds
import Formalism.SharpRestriction.Divisibility.ChainOperators.GeometricGenericity
import Formalism.SharpRestriction.Divisibility.IsotypicCorollary
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

section
namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section WeightAlgebra

variable {D : D7}


end WeightAlgebra

section P08F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : Formalism.MainNotions.DIV.Align.PrinLevF Fm) (BF : WeightFamilies.ProvF Fm)
  (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WeightAlgebra.Prov (Fm.D x i) (BF x hx i) (PF x hx i))

end P08F

section BoundaryLocalData

variable (D : D7) (X : ModuliIntegralCharts.Prov D)

end BoundaryLocalData

section IntegralModelsLocalData

variable (D : D7) (XD : DivX D) (X : IntegralModelsLocalData.Prov D XD)

end IntegralModelsLocalData

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section Fam66x

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : Formalism.MainNotions.DIV.Align.PrinLevF Fm) (XF : IntegralModelsLocalData.ProvF Fm)

end Fam66x

section Base

variable {D : D7}

end Base

end Formalism.MainNotions.DIV
end

section
noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section P18rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)















theorem division_admissible_of_inputs (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ)
    (h8 : ThetaNormsAndLinks.Conclusion₂ D L X H C2 A2 CR CT CRd) (h66 : ModuliIntegralCharts.LinkConditions D X.P6) (h08 : WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT)
    (a7 : LiftErrorLocal.adm7 D X) (a8 : LiftErrorLocal.adm8 D X) (a9 : LiftErrorLocal.adm9 D X) (a12 : LiftErrorLocal.adm12 D) :
    LiftErrorLocal.admitted D L X H C2 A2 CR CT CRd := by
  obtain ⟨p1, p2, p3b, p5, p6, p6b, -, p10, p11, -⟩ := h8
  exact ⟨p1, p2, h66, p3b, h08, p5, p6, p6b, a7, a8, a9, p10, p11, a12⟩



end P18rec

section PDV08rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : ThetaNormsAndLinks.Loc8 X)






def ThetaNormLinkHypotheses (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  ThetaNormsAndLinks.admissible_unitary_of_inputs D X Z ∧ ThetaNormsAndLinks.SandwichExists D X ∧ ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd ∧ ThetaNormsAndLinks.MirabolicIndexCond D ∧
    (ThetaNormsAndLinks.admR D nch ∧ ThetaNormsAndLinks.admG2 D ∧ ThetaNormsAndLinks.BadRowShareBound D L nch ∧ ThetaNormsAndLinks.EqualGoodMultiplicities D nch ∧ ThetaNormsAndLinks.SupLatticeGroupStable D) ∧ ThetaNormsAndLinks.SupSpansPsiPart D ∧
    (ThetaNormsAndLinks.AdditiveCharacterIntegrality D X ∧ ThetaNormsAndLinks.ScalingIntegrality D X ∧ ThetaNormsAndLinks.CrudeIntegrality D X ∧ ThetaNormsAndLinks.ThetaLevelPrimeIntegrality D X) ∧
    (ThetaNormsAndLinks.admT4 D X ∧ ThetaNormsAndLinks.NormDecompositionCond D X Z ∧ ThetaNormsAndLinks.ThetaKGroupStable D X Z ∧ ThetaNormsAndLinks.ThetaKEquivariantData D X Z ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D X) ∧
    (ThetaNormsAndLinks.RunColumnChoices D X ∧ ThetaNormsAndLinks.ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ ThetaNormsAndLinks.FurtherSizeConditions D L X H C2 A2 CR ∧ ThetaNormsAndLinks.GlobalScalarBounds D L X H ∧
      ThetaNormsAndLinks.RegularityOffTypePrimes D L X H)


theorem inputs_admissible_of (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) (hM : WeightFamilies.adm1 X.B)
    (hB : WeightFamilies.TransferenceTheoremCond) (lv : ThetaNormLinkHypotheses D L X Z H C2 A2 CR CT CRd) : ThetaNormsAndLinks.admitted D L X Z H C2 A2 CR CT CRd := by
  obtain ⟨aI, aQ, aRk, aG, ⟨aR, aG2, aBad, aTR, aGst⟩, aSp, aS, ⟨aT4, aNN, aK, aD, aW⟩, aRun⟩ := lv
  exact ⟨aI, aQ, hB, aRk, aG, ⟨aR, aG2, aBad, aTR, CutDivD.projector_statement_of_stability D aGst, aGst⟩, aSp, aS, ⟨hM, aT4, aNN, aK, aD, aW⟩, aRun⟩

end PDV08rec


section P18parts

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def UnitClauseAtBaseTuple : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) ∅ 1 ≤ LiftErrorLocal.twistV0Submodule D nch w j b ∧
    (D.what₂.Ij D.what₂.muStar j (LiftErrorLocal.plS nch w b) : ℝ) ≤ (D.what₂.places.ramIdx (LiftErrorLocal.plS nch w b) : ℝ) * X.IsgBase w j b

def TwistedIndexBound (D : D7) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, TwistedAt D w →
  (D.what₂.jw (D.what₂.muTw w) j w : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

theorem unit_clause_admissible_of_parts (hb : UnitClauseAtBaseTuple X) (hU : ∀ w, TwistedAt D w → PDVN.UAt X w) (hjw : TwistedIndexBound D) : LiftErrorLocal.adm7 D X :=
  fun i0 w hw j hj => ⟨hb i0 w hw j hj, fun ht => ⟨hU w ht j hj, hjw i0 w hw j hj ht⟩⟩

theorem twist_admissible_of_good_twists' (h : TwGoodAt D nch X.I) : LiftErrorLocal.adm8 D X := fun _ w _ hw => h w hw

end P18parts

structure Trip (D : D7) where
  B : WeightFamilies.Prov D
  P : ModuliIntegralCharts.Prov D
  W : WeightAlgebra.Prov D B P

def tripOf {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : Trip D := ⟨X.B, X.P6, X.W⟩

section Fam

variable {eps : ℝ} (Fm : FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)

theorem theorem_zero_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR : ℝ)
    (h : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
      (fun x hx i => (XF x hx i).W) H C2h A2 CR) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) (XF x hx i) H C2h A2 CR (Fm.Ct + 1) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h0 i => h x hx h0 i⟩

theorem jet_admissible_family_of
    (h : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.adm3 (Fm.D x i) (XF x hx i) := h

theorem division_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ)
    (h8 : ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd)
    (h66 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6)
    (h08 : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
      (fun x hx i => (XF x hx i).W) H C2h A2 CR)
    (unit_twist_local_clauses_family : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.adm7 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm8 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm12 (Fm.D x i)) :
    LiftErrorLocal.AdmF Fm XF H C2h A2 CR CRd := by
  obtain ⟨xa, h8⟩ := h8
  obtain ⟨xb, h08⟩ := theorem_zero_admissible_family_of Fm XF H C2h A2 CR h08
  obtain ⟨xc, unit_twist_local_clauses_family⟩ := unit_twist_local_clauses_family
  refine ⟨max xa (max xb xc), fun x hx h0 i => ?_⟩
  have ha : xa ≤ x := le_trans (le_max_left _ _) h0
  have hb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have hc : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨a7, a8, a9, a12⟩ := unit_twist_local_clauses_family x hx hc i
  exact division_admissible_of_inputs _ _ _ H C2h A2 CR _ CRd (h8 x hx ha i) (jet_admissible_family_of Fm XF h66 x hx i) (h08 x hx hb i) a7 a8 a9 a12

variable (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))

theorem inputs_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ)
    (hM : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)) (hB : WeightFamilies.TransferenceTheoremCond)
    (lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd) :
    ThetaNormsAndLinks.AdmF Fm XF ZF H C2h A2 CR CRd := by
  obtain ⟨x0, lv⟩ := lv
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have h1 : WeightFamilies.adm1 (XF x hx i).B := hM x hx i
  exact inputs_admissible_of _ _ _ _ H C2h A2 CR _ CRd h1 hB (lv x hx h0 i)

end Fam

section ChainF

variable {eps : ℝ} (Fm : FamP eps)

theorem chain_sup_lattice_family (T : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Trip (Fm.D x i)) (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass)
    (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) (Ch Ah Cq Aq C2h A2 CR CH : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (ob : ∀ x hx i, Ob (Fm.L x i) (T x hx i).B)
    (o8 : ∀ x hx i, O8 (Fm.L x i) (T x hx i).B (T x hx i).P (T x hx i).W)
    (a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, WeightAlgebra.adm1 (T x hx i).B ∧
      WeightAlgebra.adm2 (Fm.L x i) (T x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧ WeightAlgebra.adm3 (Fm.L x i) (T x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (T x hx i).W H.CA H.C1 H.A1 K.CW K.AW)
    (b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (T x hx i).B)) (b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (T x hx i).B))
    (bB : WeightFamilies.TransferenceTheoremCond) (bC : WeightFamilies.ChowlaSelbergFamily Fm) :
    WeightAlgebra.ConclusionF1 Fm (fun x hx i => (T x hx i).B) (fun x hx i => (T x hx i).P) (fun x hx i => (T x hx i).W) H C2h A2 CR := by
  obtain ⟨x0, a14⟩ := a14
  obtain ⟨⟨x1, p1⟩, p2, ⟨x3, p3⟩⟩ := s08b (fun x hx i => (T x hx i).B) ob
    ⟨b1, ⟨x0, fun x hr hx i => (a14 x hr hx i).2.1.2⟩, b3, bB, bC⟩
  refine s08 (fun x hx i => (T x hx i).B) (fun x hx i => (T x hx i).P) (fun x hx i => (T x hx i).W) o8
    ⟨max x0 (max x1 x3), fun x hr hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨a1, a2, a3, a4⟩ := a14 x hr hx0 i
  exact ⟨a1, a2, a3, a4, p1 x hr hx1 i, p2 x hr i, p3 x hr hx3 i⟩

variable (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))
  (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P6))

structure LvG (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (C2h A2 CR CRd : ℝ) : Prop where
  ob : ∀ x hx i, Ob (Fm.L x i) (XF x hx i).B
  o8 : ∀ x hx i, O8 (Fm.L x i) (XF x hx i).B (XF x hx i).P6 (XF x hx i).W
  o18 : ∀ x hx i, O18 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)
  a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      WeightAlgebra.adm2 (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧
      WeightAlgebra.adm3 (Fm.L x i) (XF x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CW K.AW
  b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)
  b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (XF x hx i).B)
  bB : WeightFamilies.TransferenceTheoremCond
  bC : WeightFamilies.ChowlaSelbergFamily Fm
  a66 : BoundaryLocalData.AdmFx Fm (fun x hx i => (XF x hx i).P6) YF
  lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd
  a79 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      UnitClauseAtBaseTuple (XF x hx i) ∧ TwistedIndexBound (Fm.D x i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i)
  aU : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ∀ w, TwistedAt (Fm.D x i) w → PDVN.UAt (XF x hx i) w
  aTG : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (XF x hx i).I
  a12 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, N.LocsCoverTw (Fm.D x i)

theorem LvG.unit_twist_local_clauses_family {Ob : WeightFamilies.ObjClass} {O8 : WeightAlgebra.ObjClass} {O18 : LiftErrorLocal.ObjClass} {K : WeightAlgebra.KAdm} {H : WeightAlgebra.KHyp} {C2h A2 CR CRd : ℝ}
    (lv : LvG Fm XF ZF YF Ob O8 O18 K H C2h A2 CR CRd) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.adm7 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm8 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm12 (Fm.D x i) := by
  obtain ⟨a, h1⟩ := lv.a79
  obtain ⟨b, h2⟩ := lv.aU
  obtain ⟨c, h3⟩ := lv.aTG
  obtain ⟨d, h4⟩ := lv.a12
  refine ⟨max (max a b) (max c d), fun x hx h0 i => ?_⟩
  have ha : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h0
  have hb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h0
  have hc : c ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have hd : d ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨b7, j7, h9⟩ := h1 x hx ha i
  exact ⟨unit_clause_admissible_of_parts _ b7 (h2 x hx hb i) j7, twist_admissible_of_good_twists' _ (h3 x hx hc i), h9, h4 x hx hd i⟩

theorem chainGF (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (Ch Ah Cq Aq C2h A2 CR ka CRd C1 C2 C3 CA CD CH : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (s66b : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (XF x hx i).P6) YF ka)
    (sIn : ThetaNormsAndLinks.AdmF Fm XF ZF H C2h A2 CR CRd → ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd)
    (s18 : LiftErrorLocal.KudlaFamilyStatement O18 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH)
    (lv : LvG Fm XF ZF YF Ob O8 O18 K H C2h A2 CR CRd) :
    WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
                  (fun x hx i => (XF x hx i).W) H C2h A2 CR ∧
      ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd ∧ LiftErrorLocal.OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD := by
  have p08 := chain_sup_lattice_family Fm (fun x hx i => tripOf (XF x hx i)) Ob O8 K H Ch Ah Cq Aq C2h A2 CR CH s08b s08 lv.ob lv.o8 (lv.a14.imp fun _ h x hx h0 i => ⟨lv.b1 x hx i, h x hx h0 i⟩) lv.b1
    lv.b3 lv.bB lv.bC
  have p66 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6 :=
    fun x hx i => (s66b lv.a66 x hx i).2.2.2.2
  have pIn := sIn (inputs_admissible_family_of Fm XF ZF H C2h A2 CR CRd lv.b1 lv.bB lv.lv)
  exact ⟨p08, pIn, s18 XF lv.o18 (division_admissible_family_of Fm XF H C2h A2 CR CRd pIn p66 p08 lv.unit_twist_local_clauses_family)⟩



end ChainF

section ON

variable {D : D7} {CH : NChoice D} {Xd : DivX D}





def ONIn (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 CA : ℝ) : Prop :=
  (WeightAlgebra.Conclusion1 L O.X.W H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D O.X CRd ∧ ThetaNormsAndLinks.RunConditions D L O.X H C2 A2 CR CT CRd) ∧
  (WeightAlgebra.Conclusion1 L O.X'.W H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D O.X' CRd ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D O.X' ∧ ThetaNormsAndLinks.RunConditions D L O.X' H C2 A2 CR CT CRd) ∧
  (LiftErrorLocal.ConjugationNormInvariance D L O.X CA ∧ ThetaNormsAndLinks.LinkConditions D O.X) ∧
  (ThetaNormsAndLinks.AtEveryPlace D O.X ∧ ThetaNormsAndLinks.LinkLatticesEveryPlace D O.X') ∧
  (CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6)

def ONLv (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (C6 Cd Cs : ℝ) : Prop :=
  L.FDef ∧ PDVN.unitBoundAtTwistedPlaces O ∧ PDVN.DepthFromContent L O C6 Cd ∧ PDVN.TypePrimeSizeConds L O Cs ∧ PDVN.TwistedPlacesCover D



end ON

section ONF

variable {eps : ℝ} (Fm : FamP eps) (OF : PDVN.ONObjF Fm)



end ONF

section ONchain

variable {eps : ℝ} (Fm : FamP eps)


variable (OF : PDVN.ONObjF Fm)


end ONchain

section ONstmts

variable {eps : ℝ} (Fm : FamP eps) (OF : PDVN.ONObjF Fm)


end ONstmts

end Formalism.MainNotions.DIV

end
end

section
noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

namespace Conj

open Formalism.BasicNotions.DV NumberField IsDedekindDomain

theorem valuation_conj (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    (D.plEq (D.what₂.places.conj w)).valuation D.what₂.LL x = (D.plEq w).valuation D.what₂.LL (star x) := by
  by_cases hx : x = 0
  · subst hx; rw [star_zero, map_zero, map_zero]
  have hs : star x ≠ 0 := by rwa [ne_eq, star_eq_zero]
  have h := D.conj_val w x
  rw [D.val_eq _ x hx, D.val_eq w (star x) hs] at h
  have h1 : vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by exact_mod_cast h
  unfold vAdd at h1
  have h2 := neg_inj.mp h1
  have n1 : (D.plEq (D.what₂.places.conj w)).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have n2 : (D.plEq w).valuation D.what₂.LL (star x) ≠ 0 := (Valuation.ne_zero_iff _).mpr hs
  rw [← WithZero.exp_log n1, h2, WithZero.exp_log n2]

theorem plEq_conj (D : D7) (w : D.what₂.places.Pl) :
    (D.plEq (D.what₂.places.conj w)).asIdeal = (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL) := by
  have hmem : ∀ x : 𝓞 D.what₂.LL, x ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL x ∈ (D.plEq w).asIdeal := by
    intro x
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL), valuation_conj]
    rfl
  apply le_antisymm
  · intro x hx
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.what₂.LL) ((hmem x).1 hx)
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO] at this
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, hmem, Formalism.DivisionValues.ValuationRepresentative.cO_cO]
    exact hy

theorem logWeight_conj (D : D7) (w : D.what₂.places.Pl) : SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w := by
  unfold SizeData₂.lwP lw
  rw [plEq_conj, Formalism.DivisionValues.ValuationRepresentative.absNorm_map_ringEquiv]

end Conj

section C2

open Formalism.BasicNotions.DV

variable {D : D7}

theorem Dpm_eq_fockDeg {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    LiftErrorLocal.Dpm D j = fockDeg D j := by
  unfold LiftErrorLocal.Dpm fockDeg
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e1 : ∀ a, |D.what₂.kaBig j τ a| = D.what₂.kaBig j τ a := fun a => by
    rw [← X.ka_big j h1 h2 τ a]; exact abs_of_nonneg (Int.natCast_nonneg _)
  have e2 : ∀ a, |D.what₂.kaSmall j τ a| = -D.what₂.kaSmall j τ a := fun a => by
    have h := X.ka_small j h1 h2 τ (Fin.rev a)
    rw [Fin.rev_rev] at h
    have h0 : D.what₂.kaSmall j τ a ≤ 0 := by
      have := Int.natCast_nonneg ((X.run j).ka.aM τ (Fin.rev a)); omega
    exact abs_of_nonpos h0
  simp only [e1, e2, Finset.sum_neg_distrib]
  ring

theorem normDecompositionCond_of_jetConsequence (L : SizeData₂ D) (EX : ErrX D) (C1 C2 C3 : ℝ) (h : LiftErrorLocal.JetConsequence D L EX C1 C2 C3)
    (hl : ∀ w : D.what₂.places.Pl, SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w) : WeightDegreeSizes.NormDecompositionCond D EX := by
  intro i u j hj S hS0
  have hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = D.host.g i := hS0
  have h2 := h.2.1 i
  set a : D.what₂.places.Pl → ℝ := fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) with ha
  have hac : ∀ w, a (D.what₂.places.conj w) = a w := fun w => by
    simp only [ha]; rw [hl w, PDVN.ramIdx_conj]
  have hmem : ∀ w, w ∈ S → D.what₂.places.conj w ∈ S := fun w hw => by
    rw [hS] at hw ⊢; rw [resChar_conj]; exact hw
  have hre : ∑ w ∈ S, a w * vNN EX i u j w = ∑ w ∈ S, a w * vNN EX i u j (D.what₂.places.conj w) := by
    refine Finset.sum_bij (fun w _ => D.what₂.places.conj w) (fun w hw => hmem w hw) ?_ ?_ ?_
    · intro w _ w' _ hww
      have := congrArg D.what₂.places.conj hww
      rwa [D.what₂.places.conj_conj, D.what₂.places.conj_conj] at this
    · intro w hw
      exact ⟨D.what₂.places.conj w, hmem w hw, D.what₂.places.conj_conj w⟩
    · intro w _
      rw [hac, D.what₂.places.conj_conj]
  have hsum : ∑ w ∈ S, SizeData₂.sz w (vNN EX i u j w) =
      ∑ w ∈ S, a w * (vNN EX i u j w + vNN EX i u j (D.what₂.places.conj w)) := by
    have e : ∀ w, SizeData₂.sz w (vNN EX i u j w) = a w * vNN EX i u j w + a w * vNN EX i u j w := fun w => by
      simp only [ha, SizeData₂.sz]; ring
    rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h3 : ∑ w ∈ S, a w * (vNN EX i u j w + vNN EX i u j (D.what₂.places.conj w)) =
      ∑ w ∈ S, a w * LiftErrorLocal.Dpi D u j :=
    Finset.sum_congr rfl fun w hw => by rw [h2 w ((hS w).1 hw) u j hj]
  have hm : ∑ w ∈ S, a w = Real.log (D.host.g i : ℝ) := factEtaMean D (D.host.g i) (D.host.g_prime i) S hS
  rw [hsum, h3, ← Finset.sum_mul, hm]
  unfold LiftErrorLocal.Dpi
  ring

end C2

section C2deg

open Formalism.BasicNotions.DV

variable {D : D7}

theorem deg_core {A B W f S0 S1 kN kT T b1 P Q : ℝ} (hA : |A| ≤ W + f * (P * S1) + T * (P * b1))
    (hB : |B| ≤ Q * f * (S0 + (kN + kT))) (hW : 0 ≤ W) (hf : 0 ≤ f) (hS0 : 0 ≤ S0) (hS : S0 ≤ S1) (hkN : 0 ≤ kN)
    (hkT : kT ≤ kN) (hT : 0 ≤ T) (hb : 0 ≤ b1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    |A - B| ≤ 2 * W + (P + 2 * Q) * (f * (S1 + kN) + T * b1) := by
  obtain ⟨a1, a2⟩ := abs_le.1 hA
  obtain ⟨c1, c2⟩ := abs_le.1 hB
  have h2 : Q * f * (S0 + (kN + kT)) ≤ Q * f * (S1 + 2 * kN) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hQ hf)
  have h5 : 0 ≤ Q * f * S1 := mul_nonneg (mul_nonneg hQ hf) (hS0.trans hS)
  have h3 : 0 ≤ P * (f * kN) := mul_nonneg hP (mul_nonneg hf hkN)
  have h4 : 0 ≤ Q * (T * b1) := mul_nonneg hQ (mul_nonneg hT hb)
  rw [abs_le]
  constructor <;> nlinarith

theorem degree_count_bound {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (L : SizeData₂ D) (EX : ErrX D) (C1 C2 C3 CD : ℝ)
    (hC : LiftErrorLocal.JetConsequence D L EX C1 C2 C3) (hD : LiftErrorLocal.ThetaAdjointPositiveScalar D L CD) (hk : KapDef D)
    (hw : ∀ j τ, 0 ≤ wj D j τ) (hSc : 0 ≤ L.Sc) (hη : 0 ≤ L.etaSz) (hb : 0 ≤ L.sc.b' / L.sc.x) :
    WeightDegreeSizes.DegreeCountBound D L (max C3 0 + 2 * max CD 0) := by
  classical
  intro u j hj
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
  obtain ⟨ha, hb', -⟩ := hC.2.2.2 u j hj
  have hd := hD hk j hj
  rw [← Dpm_eq_fockDeg X j hj'.1 hj'.2]
  have split : ∀ g : D.what₂.Tau → ℝ, ∑ τ, g τ =
      ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), g τ + ∑ t : D.host.TT, g (WeightDegreeSizes.tauOfTop D t) := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => WeightDegreeSizes.NotTop D τ) g]
    congr 1
    convert WeightDegreeSizes.sum_top D g
  set S1 : ℝ := (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz with hS1
  set b1 : ℝ := L.sc.b' / L.sc.x with hb1
  set P : ℝ := max C3 0 with hP
  have hP0 : 0 ≤ P := le_max_right _ _
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have hmη : 0 ≤ (D.R.m : ℝ) * L.etaSz := mul_nonneg (Nat.cast_nonneg _) hη
  have hS0 : 0 ≤ (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hSc) hmη
  have hS01 : (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz ≤ S1 := by
    have : (D.R.m : ℝ) * L.etaSz ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) hmη]
    simp only [hS1]; linarith
  have hS1n : 0 ≤ S1 := le_trans hS0 hS01
  have hW : 0 ≤ ∑ τ, wj D j τ := Finset.sum_nonneg fun τ _ => hw j τ

  have hA : |(∑ τ, (nuAbs D u j τ - ((D.R.k : ℝ) - 1) * wj D j τ)) - WeightDegreeSizes.sumA L| ≤
      (∑ τ, wj D j τ) + (D.R.f : ℝ) * (P * S1) + (D.host.TT.card : ℝ) * (P * b1) := by
    have e : (∑ τ, (nuAbs D u j τ - ((D.R.k : ℝ) - 1) * wj D j τ)) - WeightDegreeSizes.sumA L =
        ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), ((nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ) + wj D j τ) +
          ∑ t : D.host.TT, (nuAbs D u j (WeightDegreeSizes.tauOfTop D t) -
            ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j (WeightDegreeSizes.tauOfTop D t))) := by
      rw [split, WeightDegreeSizes.sumA, add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun τ _ => by ring
      · exact Finset.sum_congr rfl fun t _ => by ring
    have b1' : |∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ),
        ((nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ) + wj D j τ)| ≤
        ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), (P * S1 + wj D j τ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ hτ => ?_)
      have hn : WeightDegreeSizes.NotTop D τ := (Finset.mem_filter.1 hτ).2
      have h1 : |nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ| ≤ C3 * S1 :=
        ha τ fun t ht => WeightDegreeSizes.not_notTop (D := D) (τ := τ) (t := t) ht hn
      have h2 : C3 * S1 ≤ P * S1 := mul_le_mul_of_nonneg_right (le_max_left _ _) hS1n
      obtain ⟨l1, l2⟩ := abs_le.1 h1
      have h0 := hw j τ
      rw [abs_le]
      constructor <;> linarith
    have b2' : |∑ t : D.host.TT, (nuAbs D u j (WeightDegreeSizes.tauOfTop D t) -
        ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j (WeightDegreeSizes.tauOfTop D t)))| ≤
        ∑ _t : D.host.TT, (P * S1 + P * b1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      have h1 : |nuAbs D u j (WeightDegreeSizes.tauOfTop D t) -
          ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j (WeightDegreeSizes.tauOfTop D t))| ≤ C3 * (S1 + b1) :=
        hb' (WeightDegreeSizes.tauOfTop D t) t (WeightDegreeSizes.isTopAt_tauOfTop D t)
      have h2 : C3 * (S1 + b1) ≤ P * (S1 + b1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hS1n hb)
      linarith
    have c1 : ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), (P * S1 + wj D j τ) +
        ∑ _t : D.host.TT, (P * S1 + P * b1) ≤
        (∑ τ, wj D j τ) + (D.R.f : ℝ) * (P * S1) + (D.host.TT.card : ℝ) * (P * b1) := by
      have s1 : ∑ _τ : D.what₂.Tau, P * S1 = ∑ _τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), P * S1 +
          ∑ _t : D.host.TT, P * S1 := split fun _ => P * S1
      rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at s1
      have s2 : ∑ τ ∈ Finset.univ.filter (fun τ => WeightDegreeSizes.NotTop D τ), wj D j τ ≤ ∑ τ, wj D j τ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun τ _ _ => hw j τ
      have s3 : ∑ _t : D.host.TT, P * b1 = (D.host.TT.card : ℝ) * (P * b1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, s3]
      linarith
    rw [e]
    obtain ⟨l1, l2⟩ := abs_le.1 b1'
    obtain ⟨l3, l4⟩ := abs_le.1 b2'
    rw [abs_le]
    constructor <;> linarith
  have hkN : 0 ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := mul_nonneg (Nat.cast_nonneg _) (by unfold Formalism.MainNotions.G.Nm; exact Nat.cast_nonneg _)
  have hkt : 0 ≤ (D.R.k : ℝ) * D.R.t := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htN : (D.R.k : ℝ) * D.R.t ≤ (D.R.k : ℝ) * Formalism.MainNotions.G.Nm D := by
    have h0 : D.R.t ≤ D.R.N D.R.m := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.N
      nlinarith
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold Formalism.MainNotions.G.Nm
    exact_mod_cast h0
  have hB : |(LiftErrorLocal.Dpm D j : ℝ) - ∑ τ, ((D.R.k : ℝ) - 1) * wj D j τ| ≤
      max CD 0 * D.R.f * (((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz) +
        ((D.R.k : ℝ) * Formalism.MainNotions.G.Nm D + (D.R.k : ℝ) * D.R.t)) := by
    refine hd.trans ?_
    have : CD * (D.R.f : ℝ) ≤ max CD 0 * D.R.f := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    have e : (D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.k : ℝ) * ((D.R.N D.R.m : ℝ) + D.R.t) =
        ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz) + ((D.R.k : ℝ) * Formalism.MainNotions.G.Nm D + (D.R.k : ℝ) * D.R.t) := by
      unfold Formalism.MainNotions.G.Nm; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this (add_nonneg hS0 (add_nonneg hkN hkt))
  have key := deg_core hA hB hW (Nat.cast_nonneg _) hS0 hS01 hkN htN (Nat.cast_nonneg _) hb hP0 (le_max_right CD 0)
  have e1 : (∑ τ, nuAbs D u j τ) - (LiftErrorLocal.Dpm D j : ℝ) - WeightDegreeSizes.sumA L =
      ((∑ τ, (nuAbs D u j τ - ((D.R.k : ℝ) - 1) * wj D j τ)) - WeightDegreeSizes.sumA L) -
        ((LiftErrorLocal.Dpm D j : ℝ) - ∑ τ, ((D.R.k : ℝ) - 1) * wj D j τ) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e1]
  refine key.trans (le_of_eq ?_)
  unfold WeightDegreeSizes.errG
  simp only [hS1, hb1]
  ring

end C2deg

section secondOrderBound

variable {eps : ℝ} (Fm : FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)

include XF in

theorem degree_weight_family_of_constant_D (C1 C2 C3 CD : ℝ)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3 ∧ LiftErrorLocal.ThetaAdjointPositiveScalar (Fm.D x i) (Fm.L x i) CD)
    (hs : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, ∀ j τ, 0 ≤ wj (Fm.D x i) j τ)
    (rest : ∃ Cg CT CG Cd CI x0 : ℝ, 0 ≤ Cg ∧ ∀ x, x0 ≤ x → ∀ i : Fm.Ix x,
      WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err (max C3 0 + 2 * max CD 0) Cg ∧
      WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) CT ∧ WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) CG ∧
      WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) Cd ∧ WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err CI) :
    ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.adm11 (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨xa, h⟩ := h
  obtain ⟨xb, hs⟩ := hs
  obtain ⟨Cg, CT, CG, Cd, CI, xc, hCg, rest⟩ := rest
  refine WeightDegreeSizes.secondComplement_family_of_inputs Fm ⟨max C3 0 + 2 * max CD 0, Cg, CT, CG, Cd, CI, max xa (max xb xc), hCg, fun x hx hx1 i => ?_⟩
  have ha : xa ≤ x := le_trans (le_max_left _ _) hx
  have hb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨pC, pD⟩ := h x hx1 ha i
  obtain ⟨r2, r3, r4, r5, r6⟩ := rest x hc' i
  exact ⟨fun u i' h => (Fm.D x i).T_ne_g u i' h.symm, normDecompositionCond_of_jetConsequence _ _ C1 C2 C3 pC (Conj.logWeight_conj _),
    degree_count_bound (XF x hx1 i) _ _ C1 C2 C3 CD pC pD (Fm.ex x hx1 i).kap_def (hs x hb i) (Fm.L x i).Sc_pos.le
      (Fm.L x i).etaSz_pos.le (div_nonneg (Fm.L x i).sc.b'_pos.le (Fm.L x i).sc.x_pos.le), r2, r3, r4, r5, r6⟩

noncomputable abbrev weightDegreeConstant : ℝ := CutKapD.kappa_degree_bound_holds.choose

include XF in

theorem degree_weight_family_of_constant (C1 C2 C3 : ℝ)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3)
    (hs : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, ∀ j τ, 0 ≤ wj (Fm.D x i) j τ)
    (rest : ∃ Cg CT CG Cd CI x0 : ℝ, 0 ≤ Cg ∧ ∀ x, x0 ≤ x → ∀ i : Fm.Ix x,
      WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err (max C3 0 + 2 * max weightDegreeConstant 0) Cg ∧
      WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) CT ∧ WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) CG ∧
      WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) Cd ∧ WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err CI) :
    ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, LocalQuadraticParts.adm11 (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x0, h⟩ := h
  exact degree_weight_family_of_constant_D Fm XF C1 C2 C3 weightDegreeConstant
    ⟨x0, fun x hx h0 i => ⟨h x hx h0 i, CutKapD.kappa_degree_bound_holds.choose_spec (Fm.D x i) (Fm.L x i)⟩⟩ hs rest

end secondOrderBound

end Formalism.MainNotions.DIV

end
end
