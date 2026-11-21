import Mathlib
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopRowSF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMassStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundsUniformLargeGapFamilies
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPow
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBesselStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap

section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_count_primitive_sublattices_over_genus : ∀ c₀ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), c₀ ≤ Cl → UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  first | exact @GlobalTheory.Mass.PrimMeanRow.main | exact GlobalTheory.Mass.PrimMeanRow.main | (intros; apply GlobalTheory.Mass.PrimMeanRow.main <;> assumption)
end

section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_primitive_corank_one_sublattices_bound : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  first | exact @GlobalTheory.Mass.PrimMeanCorankOne.main | exact GlobalTheory.Mass.PrimMeanCorankOne.main | (intros; apply GlobalTheory.Mass.PrimMeanCorankOne.main <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.RowCounts

theorem uniform_counts : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
    (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u',
      VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  intro hM Cg cb Cu cT CT C0 A
  obtain ⟨C1a, hC1⟩ := GlobalTheory.T.mean_count_primitive_sublattices_over_genus 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT C0 A 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT C0 A
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT C0 A
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT C0 A
  refine ⟨c3, cH, cS, c4, 1, fun eps Fm _ hl => ⟨fun C hC => ⟨0, fun x _ i u u' => ?_⟩,
    ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩⟩⟩
  · exact hC3 C hC _ _ u u' _ _ hl (GlobalTheory.T.rows_raw_mass_and_genus_mass _ u)
      (hC1 _ (le_max_left _ _) _ _ u u' _ _ Cg cb Cu cT CT C0 A hl)
  · exact hHH _ _ u u' _ _ hl
  · exact hSW _ _ u u' _ _ hl
      (GlobalTheory.T.mean_primitive_corank_one_sublattices_bound _ _ u u' _ _ Cg cb Cu cT CT C0 A (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u' _ _ hl

end GlobalTheory.RowCounts
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCounts_uniform_constants_families : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  atlas_forward_decl GlobalTheory.RowCounts.uniform_counts
end

section
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU

set_option linter.unusedVariables false

namespace GlobalTheory.RowsFive

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)
  (Cg cb Cu cT CT C0 A : ℝ)

theorem rowsND_of (h10a : VanishingOnXAndXPlus.FamilyRowsExist Fm) (h6 : VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0) (h7 : VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0)
    (h8 : VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A) (h10b : VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0) (hT : rows_TiesF Fm C1 X Y) (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ c0ND CT A C0 U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C := by
  intro C hC
  simp only [c0ND] at hC
  have h14 := Formalism.MainNotions.BridgeLemma.family_word_theorem_a Fm
  set c3 := U.c3 with hc3def
  have LocalHeightDeterminant := hU.1
  set cH := U.cH with hcHdef
  obtain ⟨x27, H27⟩ := hU.2.1
  set cV := U.cV with hcVdef
  obtain ⟨xV, HV⟩ := hU.2.2.1
  set c : ℝ := max (max c3 1) (max (|cH| + 2) (|cV| + 2)) with hcdef
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨hCh, _, HA⟩ := hU.2.2.2.2.2 (9 * c + 3)
  set Ca := U.CaF (9 * c + 3) with hCadef
  set C2 := U.secondOrderBound (9 * c + 3) with hC2def
  set Ch := U.ChF (9 * c + 3) with hChdef
  obtain ⟨xA, HAx⟩ := HA 1 one_pos
  obtain ⟨x6, H6⟩ := h6 1 one_pos
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm |C2|
  refine ownEv_intro Fm (max (max (max x20 x27) (max xV xA)) (max (max x6 x8) (max x10 xk)))
    fun x hx _ i hx1 u u' hH => ?_
  have g20 : x20 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have g27 : x27 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have gV : xV ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have gA : xA ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have g6 : x6 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g8 : x8 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g10 : x10 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have gk : xk ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hc0 : 0 ≤ c := by linarith
  have hcC : c ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by
    have := le_trans (le_max_right _ _) hC
    nlinarith
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ (Fm.D x i).R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast rows_f_pos (Fm.D x i)
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have hkm : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have ha2 : |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 ≤ (Fm.D x i).R.k := by
    refine le_trans ?_ (Hk x gk i)
    have e1 : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : ((Fm.D x i).R.m : ℝ) ^ 5 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have h5 : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ))) (by linarith : 0 ≤ (Fm.L x i).sc.L - 1)]
    calc |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 ≤ |C2| * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L) :=
          mul_le_mul_of_nonneg_left (e1.trans e2) (abs_nonneg _)
      _ = |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * (Fm.D x i).R.k) + 4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k +
    4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 + 12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg (Fm.D x i) hc0 (Fm.D x i).R.k
    positivity
  have hqb := rows_q_bound (m := (Fm.D x i).R.m) (k := (Fm.D x i).R.k) (r := (Fm.D x i).R.rS) (c := c)
    (cf := cF (Fm.D x i).R.f) (a2 := |C2| * ((Fm.D x i).R.m : ℝ) ^ 2) (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : (((Fm.D x i).R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * (Fm.D x i).R.k * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps (Y x hx1 i u u') (sC' Fm) (sCl Fm) Cg cb Cu cT CT C0 A c (9 * c + 3) Ca C2 Ch 1 1
      ⌈(((Fm.D x i).R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := H20x x g20 i u u'
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) (H27 x g27 i u u')
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) (HV x gV i hx1 u u')
      hDEC := (HAx x gA i).2.2.2.2.2.2.2
      ha := h10a x i
      hb := H10 x g10 i
      hp := (HAx x gA i).2.2.1
      hpp := (HAx x gA i).2.2.2.2.2.1
      h6 := H6 x g6 i
      hδ := zero_le_one
      hThA := h14 x i u u'
      hT := (hT x hx1 i u u').1
      hG0 := (hT x hx1 i u u').2.1
      hE := (hT x hx1 i u u').2.2
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos (Y x hx1 i u u') hH.1 (H8 x g8 i u u' hH)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsND_record _ hyp le_rfl hcC hC1 hCsq ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * a)
  have h2 : C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 ≤ |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * (((Fm.D x i).R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = (((Fm.D x i).R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

theorem rowsDeg_of (h10a : VanishingOnXAndXPlus.FamilyRowsExist Fm) (h6 : VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0) (h7 : VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0)
    (h8 : VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A) (h10b : VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0) (hT : rows_TiesF Fm C1 X Y) (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ degenerateConstant CT U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsDeg (X x hx i) (Y x hx i u u') C := by
  intro C hC
  simp only [degenerateConstant] at hC
  have h14 := Formalism.MainNotions.BridgeLemma.family_word_theorem_a Fm
  set c3 := U.c3 with hc3def
  have LocalHeightDeterminant := hU.1
  set cH := U.cH with hcHdef
  obtain ⟨x27, H27⟩ := hU.2.1
  set cV := U.cV with hcVdef
  obtain ⟨xV, HV⟩ := hU.2.2.1
  set cK := max (max 1 CT) (|cH| + 2) with hcKdef
  have HK := Formalism.L2.SG.RowsU.rowsKBU Fm C1 X Y Cg cb Cu cT CT C0 A U hU
  set c : ℝ := max (max (max c3 cK) 1) (max (|cH| + 2) (|cV| + 2)) with hcdef
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have k5 : cK ≤ c := by rw [hcdef]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨xK, HKx⟩ := HK c k5
  obtain ⟨hCh, _, HA⟩ := hU.2.2.2.2.2 (9 * c + 3)
  set Ca := U.CaF (9 * c + 3) with hCadef
  set C2 := U.secondOrderBound (9 * c + 3) with hC2def
  set Ch := U.ChF (9 * c + 3) with hChdef
  obtain ⟨xA, HAx⟩ := HA 1 one_pos
  obtain ⟨x6, H6⟩ := h6 1 one_pos
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm (3 * |C2|)
  refine ownEv_intro Fm (max (max (max (max x20 xK) x27) (max xV xA)) (max (max x6 x8) (max x10 xk)))
    fun x hx _ i hx1 u u' hH => ?_
  have g20 : x20 ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
    (le_max_left _ _)) hx
  have gK : xK ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
    (le_max_left _ _)) hx
  have g27 : x27 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have gV : xV ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have gA : xA ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have g6 : x6 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g8 : x8 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have g10 : x10 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have gk : xk ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hc0 : 0 ≤ c := by linarith
  have hcC : c ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
    nlinarith
  have hC2 : 2 * C2 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCa : |Ca| ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ (Fm.D x i).R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast rows_f_pos (Fm.D x i)
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have hkm : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have ha2 : |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2 ≤ (Fm.D x i).R.k := by
    refine le_trans ?_ (Hk x gk i)
    have e1 : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : ((Fm.D x i).R.m : ℝ) ^ 4 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : ((Fm.D x i).R.m : ℝ) ^ 5 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have h5 : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ))) (by linarith : 0 ≤ (Fm.L x i).sc.L - 1)]
    have hab := abs_nonneg C2
    calc |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2
        = |C2| * (((Fm.D x i).R.m : ℝ) ^ 2 + 2 * ((Fm.D x i).R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = 3 * |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * (Fm.D x i).R.k) + 4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k +
    4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + (|C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2) / 2 +
    12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg (Fm.D x i) hc0 (Fm.D x i).R.k
    positivity
  have hqb := rows_q_bound (m := (Fm.D x i).R.m) (k := (Fm.D x i).R.k) (r := (Fm.D x i).R.rS) (c := c)
    (cf := cF (Fm.D x i).R.f) (a2 := |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2)
    (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : (((Fm.D x i).R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * (Fm.D x i).R.k * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps (Y x hx1 i u u') (sC' Fm) (sCl Fm) Cg cb Cu cT CT C0 A c (9 * c + 3) Ca C2 Ch 1 1
      ⌈(((Fm.D x i).R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := H20x x g20 i u u'
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) (H27 x g27 i u u')
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) (HV x gV i hx1 u u')
      hDEC := (HAx x gA i).2.2.2.2.2.2.2
      ha := h10a x i
      hb := H10 x g10 i
      hp := (HAx x gA i).2.2.1
      hpp := (HAx x gA i).2.2.2.2.2.1
      h6 := H6 x g6 i
      hδ := zero_le_one
      hThA := h14 x i u u'
      hT := (hT x hx1 i u u').1
      hG0 := (hT x hx1 i u u').2.1
      hE := (hT x hx1 i u u').2.2
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos (Y x hx1 i u u') hH.1 (H8 x g8 i u u' hH)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsDeg_record _ hyp (HKx x gK i hx1 u u' hH) k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * a)
  have h2 : (C2 * ((Fm.D x i).R.m : ℝ) ^ 2 + C2 * ((Fm.D x i).R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * ((Fm.D x i).R.m : ℝ) ^ 2 + |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * (((Fm.D x i).R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = (((Fm.D x i).R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

theorem rowsOne_of (h10a : VanishingOnXAndXPlus.FamilyRowsExist Fm) (h6 : VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0) (h7 : VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0)
    (h8 : VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A) (h10b : VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0) (hT : rows_TiesF Fm C1 X Y)
    (hTI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u'))
    (hBL : ∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') (U : UC)
    (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ C ≥ corankOneConstant CT A C0 Fm.CGam U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsOne (X x hx i) (Y x hx i u u') C := by
  intro C hC
  simp only [corankOneConstant] at hC
  have h14 := Formalism.MainNotions.BridgeLemma.family_word_theorem_a Fm
  set c3 := U.c3 with hc3def
  have LocalHeightDeterminant := hU.1
  set cH := U.cH with hcHdef
  obtain ⟨x27, H27⟩ := hU.2.1
  set cV := U.cV with hcVdef
  obtain ⟨xV, HV⟩ := hU.2.2.1
  set cS := U.cS with hcSdef
  obtain ⟨x4, H4⟩ := hU.2.2.2.1
  set c4 := U.c4 with hc4def
  obtain ⟨x21, H21⟩ := hU.2.2.2.2.1
  set c : ℝ := max (max c3 1) (max (max (|cH| + 2) (|cV| + 2)) (max (|cS| + 2) (|c4| + 2))) with hcdef
  have k1 : c3 ≤ c := by rw [hcdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have k2 : 1 ≤ c := by rw [hcdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have k3 : |cH| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).1 (le_max_right _ _)
  have k4 : |cV| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.1 (le_max_right _ _)
  have k5 : |cS| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.2.1 (le_max_right _ _)
  have k6 : |c4| + 2 ≤ c := by rw [hcdef]; exact le_trans (le_max_four _ _ _ _).2.2.2 (le_max_right _ _)
  obtain ⟨x20, H20x⟩ := LocalHeightDeterminant c k1
  obtain ⟨hCh, hCa, HA⟩ := hU.2.2.2.2.2 (9 * c + 3)
  set Ca := U.CaF (9 * c + 3) with hCadef
  set C2 := U.secondOrderBound (9 * c + 3) with hC2def
  set Ch := U.ChF (9 * c + 3) with hChdef
  obtain ⟨xA, HAx⟩ := HA (1 / 4) (by norm_num)
  obtain ⟨x6, H6⟩ := h6 (1 / 2) (by norm_num)
  obtain ⟨x7, H7⟩ := h7
  obtain ⟨x8, H8⟩ := h8
  obtain ⟨x10, H10⟩ := h10b
  obtain ⟨xk, _, Hk⟩ := ev_kLow Fm |C2|
  obtain ⟨xc, _, Hc⟩ := ev_k Fm ((max Ca 1) ^ 3)
  clear hc3def hcHdef hcVdef hcSdef hc4def hCadef hC2def hChdef hU
  refine ownEv_intro Fm (max (max (max (max x20 x27) (max xV xA)) (max (max x6 x8) (max x10 xk)))
    (max (max x4 x21) (max x7 xc))) fun x hx _ i hx1 u u' hH => ?_
  have hM1 : max (max x20 x27) (max xV xA) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hM2 : max (max x6 x8) (max x10 xk) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hM3 : max (max x4 x21) (max x7 xc) ≤ x := le_trans (le_max_right _ _) hx
  have g20 : x20 ≤ x := le_trans (le_max_four _ _ _ _).1 hM1
  have g27 : x27 ≤ x := le_trans (le_max_four _ _ _ _).2.1 hM1
  have gV : xV ≤ x := le_trans (le_max_four _ _ _ _).2.2.1 hM1
  have gA : xA ≤ x := le_trans (le_max_four _ _ _ _).2.2.2 hM1
  have g6 : x6 ≤ x := le_trans (le_max_four _ _ _ _).1 hM2
  have g8 : x8 ≤ x := le_trans (le_max_four _ _ _ _).2.1 hM2
  have g10 : x10 ≤ x := le_trans (le_max_four _ _ _ _).2.2.1 hM2
  have gk : xk ≤ x := le_trans (le_max_four _ _ _ _).2.2.2 hM2
  have g4 : x4 ≤ x := le_trans (le_max_four _ _ _ _).1 hM3
  have g21 : x21 ≤ x := le_trans (le_max_four _ _ _ _).2.1 hM3
  have g7 : x7 ≤ x := le_trans (le_max_four _ _ _ _).2.2.1 hM3
  have gc : xc ≤ x := le_trans (le_max_four _ _ _ _).2.2.2 hM3
  have hc0 : 0 ≤ c := by linarith
  have q1 : 4 * Real.sqrt A ≤ C := le_trans (le_max_four _ _ _ _).1 hC
  have q2 : 2 * Real.sqrt (2 * C0) * c ≤ C := le_trans (le_max_four _ _ _ _).2.1 hC
  have q3 : Fm.CGam + C2 ≤ C := le_trans (le_max_four _ _ _ _).2.2.1 hC
  have q4 : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C := le_trans (le_max_four _ _ _ _).2.2.2 hC
  have hCsq : 4 + 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) ≤ C ^ 2 := by
    have h0 : 0 ≤ 2 * (c ^ 2 + 2 * max (Ch - c) 0) * (c + 1) := by
      have := le_max_right (Ch - c) 0
      positivity
    nlinarith
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ (Fm.D x i).R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast rows_f_pos (Fm.D x i)
  have hL1 := d_one_le_L (Fm.D x i) (Fm.L x i)
  have hkm : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have ha5 : |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 ≤ (Fm.D x i).R.k := by
    refine le_trans ?_ (Hk x gk i)
    have e2 : ((Fm.D x i).R.m : ℝ) ^ 5 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have h5 : 0 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ ((Fm.D x i).R.f : ℝ))) (by linarith : 0 ≤ (Fm.L x i).sc.L - 1)]
    calc |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 ≤ |C2| * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L) :=
          mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
      _ = |C2| * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 12 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 +
    |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 + 12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hqb := decay_length_sufficient (m := (Fm.D x i).R.m) (k := (Fm.D x i).R.k) (r := (Fm.D x i).R.rS) (c := c) (B := |C2|)
    (rows_m_cast _) hr0 hkm hc0 (abs_nonneg _) ha5
  have hqb' : (((Fm.D x i).R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * (Fm.D x i).R.k * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    rw [hadef]; exact hqb
  have hra0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps (Y x hx1 i u u') (sC' Fm) (sCl Fm) Cg cb Cu cT CT C0 A c (9 * c + 3) Ca C2 Ch (1 / 2) (1 / 4)
      ⌈(((Fm.D x i).R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := H20x x g20 i u u'
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) (H27 x g27 i u u')
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) (HV x gV i hx1 u u')
      hDEC := (HAx x gA i).2.2.2.2.2.2.2
      ha := h10a x i
      hb := H10 x g10 i
      hp := (HAx x gA i).2.2.1
      hpp := (HAx x gA i).2.2.2.2.2.1
      h6 := H6 x g6 i
      hδ := by norm_num
      hThA := h14 x i u u'
      hT := (hT x hx1 i u u').1
      hG0 := (hT x hx1 i u u').2.1
      hE := (hT x hx1 i u u').2.2
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos (Y x hx1 i u u') hH.1 (H8 x g8 i u u' hH)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine corank_one_bound_of_injective_terms _ hyp (switch_bound_mono_constant k5 (H4 x g4 i u u')) (partner_count_bound_mono_constant k6 (H21 x g21 i u u'))
    (hTI x hx1 i u u') (hBL x i u u') (H7 x g7 i) le_rfl (by norm_num) le_rfl hCa (Hc x gc i) ?_ q1 q2
    (by rw [Fm.CGam_eq]; exact q3) hCsq
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * a)
  have h2 : C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 ≤ |C2| * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  have h3 : |C2 * ((Fm.D x i).R.m : ℝ) ^ 4| = |C2| * ((Fm.D x i).R.m : ℝ) ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) ^ 4)]
  calc _ ≤ a * (((Fm.D x i).R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef, h3]; linarith
    _ = (((Fm.D x i).R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end Fam

theorem rows_three_bounds : ∀ (eps : ℝ) (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1) (Cg cb Cu cT CT C0 A : ℝ), VanishingOnXAndXPlus.FamilyRowsExist Fm → VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A → VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 → rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → ∀ U : UC, UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U → ∀ C ≥ c0U CT A C0 Fm.CGam U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  intro eps Fm C1 X Y Cg cb Cu cT CT C0 A h10a h6 h7 h8 h10b hT hTI hBL U hU C hC
  have g1 := rowsND_of Fm C1 X Y Cg cb Cu cT CT C0 A h10a h6 h7 h8 h10b hT U hU C ((le_max_left _ _).trans hC)
  have g2 := rowsDeg_of Fm C1 X Y Cg cb Cu cT CT C0 A h10a h6 h7 h8 h10b hT U hU C
    (((le_max_left _ _).trans (le_max_right _ _)).trans hC)
  have g3 := rowsOne_of Fm C1 X Y Cg cb Cu cT CT C0 A h10a h6 h7 h8 h10b hT hTI hBL U hU C
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC)
  exact (g1.and (g2.and g3)).mono fun C' Cl x i h hx u u' hH => ⟨h.1 hx u u' hH, h.2.1 hx u u' hH, h.2.2 hx u u' hH⟩

end GlobalTheory.RowsFive
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_family_satisfies_row_estimates : ∀ (eps : ℝ) (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1) (Cg cb Cu cT CT C0 A : ℝ), VanishingOnXAndXPlus.FamilyRowsExist Fm → VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A → VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 → rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → ∀ U : UC, UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U → ∀ C ≥ c0U CT A C0 Fm.CGam U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  atlas_forward_decl GlobalTheory.RowsFive.rows_three_bounds
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevelGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CritLevel

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem tcrit_low_of_dsig (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 40 ≤ Cl) (hT : Ties D) (hb' : Real.sqrt large₂.sc.b ≤ large₂.sc.b')
    (hx : large₂.sc.x ≤ D.R.k) : UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := fun τ =>
    Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH.1 hCL τ
  exact tcrit_low D large₂ C' Cl Cg cb Cu cT CT C0 hCl hVV hb' hx hH

theorem along_family :
    Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hDs eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := GlobalTheory.MassAtRecord.massRatio_at_record
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low_of_dsig hDs _ _ _ _ _ _ _ _ _ _ hCl (Fm.ties x i) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

end GlobalTheory.CritLevelGap
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU

noncomputable section

namespace GlobalTheory.LoopRowBoundsGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 cV CGam : ℝ, ∃ C₀ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), Fm.CGam = CGam → thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) ∧ ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1), rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A cV) → ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  intro hSMR hH hBp Cg cb Cu cT CT C0 A C1 cV CGam
  obtain ⟨c3, cH, cS, c4, thr1, HC⟩ := GlobalTheory.T.rowCounts_uniform_constants_families hSMR Cg cb Cu cT CT C0 A
  obtain ⟨Ca, C2, Ch, thr2, hCa, hCh, HA⟩ := GlobalTheory.T.amplitude_bounds_uniform_large_gap_families hSMR hH hBp Cg cb Cu cT CT C0 A C1
  let U : UC := ⟨c3, cH, cV, cS, c4, fun _ => Ca, fun _ => C2, fun _ => Ch⟩
  refine ⟨c0U CT A C0 CGam U, max 40 (max thr1 thr2), fun eps Fm hG hs hl hR => ?_⟩
  have hs1 : thr1 ≤ sC' Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hl1 : thr1 ≤ sCl Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hs2 : thr2 ≤ sC' Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hl2 : thr2 ≤ sCl Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have h40 : 40 ≤ sCl Fm := (le_max_left _ _).trans hl
  have h3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm := fun x _ i u => GlobalTheory.T.rows_raw_mass_and_genus_mass (Fm.D x i) u
  obtain ⟨a10a, a6, a7, a8, a10b, hform⟩ :=
    GlobalTheory.CritLevelGap.along_family hH.2.2.2 eps Fm Cg cb Cu cT CT C0 A h40 hR h3
  refine ⟨hform, fun X Y hT hTI hBL hVol C hC => ?_⟩
  obtain ⟨LocalHeightDeterminant, H27, H4, H21⟩ := HC eps Fm hs1 hl1
  have hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U :=
    ⟨LocalHeightDeterminant, H27, hVol, H4, H21, fun Cpr => ⟨hCh, hCa, fun δ hδ => HA eps Fm hs2 hl2 hR Cpr δ hδ⟩⟩
  exact GlobalTheory.T.admissible_family_satisfies_row_estimates eps Fm C1 X Y Cg cb Cu cT CT C0 A a10a a6 a7 a8 a10b hT hTI hBL U hU C (by rw [hG]; exact hC)

end GlobalTheory.LoopRowBoundsGap
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.loopRowBounds_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 cV CGam : ℝ, ∃ C₀ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), Fm.CGam = CGam → thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) ∧ ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1), rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A cV) → ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  atlas_forward_decl GlobalTheory.LoopRowBoundsGap.rows_along_family
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn

noncomputable section

namespace GlobalTheory.LoopRowsCloseGap

section PartB

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.LoopLoc

variable {D : D7}

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem wuBessel_ofW {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (C : Choice X θ) : WuBessel C :=
  Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def loopLocDatOfW (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (hT : Formalism.BasicNotions.dsigTie D)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) {large₂ : SizeData₂ D} {C1 : ℝ}
    (hwin : normWin D large₂ C1 θ) (u u' : D.what₂.Word) : Formalism.L2.SG.LoopTieOf.LoopLocDat D large₂ u u' C1 where
  θ := θ
  θ_win := hwin
  W τ := locW C u u' τ
  goodW τ := goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ)
    (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)
  A τ := locS (wuBessel_ofW hG hBW C) u u' τ
  goodS τ := goodS_of (wuBessel_ofW hG hBW C) u u' τ
    (Formalism.L2.SG.Pf.goodSRest_all hG hT (wuBessel_ofW hG hBW C) u u' τ)
  deg_eq τ := deg_eq (wuBessel_ofW hG hBW C) u u' τ

end PartB

section Sel

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn Formalism.L2.SG.LoopsTies Formalism.L2.SG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {𝒞 : FamClass} (sel : SSel 𝒞)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def BGW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (C1f : List ℝ → ℝ) (hC1 : ∀ l, 0 ≤ C1f l) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (_ : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut) :=
  fun Fm hc x hx i u u' => loopLocDatOfW
    (gap_of hc (hyR (selG sel) yFG hx) i) (Fm.ties x i).dsig_tie hBW
    (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
    (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) (hC1 _)) u u'

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

def MGW (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hBW : Formalism.L2.SG.LocWSOf.BesselOfW)
    (hRM : RMeasExAll) (hJF : JFactNAll) (hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula) :
    ∀ {eps : ℝ} (Fm : FamP eps) (hc : CG 𝒞 Fm) x (hx : (Fm.raise (yR (selG sel) yFG Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR (selG sel) yFG (hyFG sel hFX hWu) Fm hc x hx i) u u' ((fun _ => 1) Fm.cOut)
        (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u') :=
  fun Fm hc x hx i u u' =>
    LoopTerm.loopTermOfN (wOf ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X)
      (((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).hI
        (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (hvOfW _ _ _ _ (hyFG sel hFX hWu Fm hc x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
      (Fm.L x i) 1 (CX ((selG sel Fm hc).2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X u)
      (wuBessel_ofW (gap_of hc (hyR (selG sel) yFG hx) i) hBW _) u u'
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)
      (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW
      (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodS
      (hRM _ _ _ _ _ _ u u' (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one) Fm hc x hx i u u').goodW)
      (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u') (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u')
      (hJF _ _ _ _ _ _ _ u u' (gap_of hc (hyR (selG sel) yFG hx) i))
      (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos _ u u')
      (Formalism.L2.SG.Pf.LoopBCovN.covWinN_sizes hCF _ (Fm.L x i) (Fm.sizes x (raise_lt hx) i) (by norm_num) u u')
      (Formalism.L2.SG.Pf.LoopBTheta.normWin_one (Fm.L x i) zero_le_one)

end Sel

open Formalism.L2.SG.LoopsTies

theorem sC'_mem_cLast {eps : ℝ} (Fm : FamP eps) : sC' Fm ∈ Fm.cLast := by
  unfold FamP.cLast sC'; simp

theorem le_sCl_of {eps : ℝ} (Fm : FamP eps) {t : ℝ} (h : ∀ c ∈ Fm.cLast, t ≤ c) : t ≤ sCl Fm := by
  unfold sCl
  refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
    (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))

theorem loop_rows_closed_gap : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → BpJoin.ThmBpDS →
    Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (𝒞 : FamClass) (sel : SSel 𝒞),
    (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) → LoopRowS 3 𝒞 sel := by
  intro hH hBW hBp hWu hRF 𝒞 sel hT hRk
  have hGap := Formalism.L2.SG.GapClosed.gapEv_closed_of 𝒞 hT
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨hH.1.1.1⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecInf := ⟨hH.1.1.2.1⟩
  have hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC := Formalism.L2.SG.Pf.finXC_of hWu hRF
  have hRM : RMeasExAll := GlobalTheory.RMeasAll.rMeasEx_all
  have hJF : JFactNAll := GlobalTheory.T.localBesselJFactor_all_words_of_gap
  have hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := Formalism.MainStatements.RowRest.covariance_formula
  choose C₀F thrF hR using GlobalTheory.T.loopRowBounds_along_family_largeGaps Formalism.HermitianLattices.Ext.L3.siegelMassRatio hH hBp
  choose cVF hcV using GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow
  have hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 →
        ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨e, he, H⟩ := hRk
    refine ⟨e, he, fun eps h1 h2 => ?_⟩
    obtain ⟨K, hK⟩ := H eps h1 h2
    let K4 : Formalism.MainNotions.TransportedAlt := ⟨0, fun _ => 0, fun _ => 0,
      fun l => thrF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 0 1 0 (l.getD 17 0)⟩
    refine ⟨K.sup K4, fun Fm CH hc hL => ?_⟩
    obtain ⟨hL1, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
    have hthr : ∀ c ∈ Fm.cLast, thrF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 0 1 0 Fm.CGam ≤ c := by
      intro c hc0
      have h := hL4.2.2.2 c hc0
      simp only [K4] at h
      rwa [constant_list_cylinder, constant_list_trace, constant_list_gamma] at h
    exact (hR _ _ _ _ _ _ _ _ _ _ eps Fm rfl (hthr _ (sC'_mem_cLast Fm)) (le_sCl_of Fm hthr)
      (hK Fm CH hc hL1)).1
  refine loopRowS_of_sub sel 3 hGap ?_
  let C₀f : (List ℝ → ℝ) → List ℝ → ℝ := fun aF l =>
    C₀F (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16)) 1
      (cVF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16))) (l.getD 17 0)
  refine loopRowS_of_raised 3 (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) C₀f
    (YtR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF)) ?_ (closed_sub (fun _ h => h.1) hForm)
  intro aF
  obtain ⟨e, he, H⟩ := closed_sub (𝒞' := CG 𝒞) (fun _ h => h.1) hRk
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  let K4 : Formalism.MainNotions.TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l =>
    max (thrF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16)) 1
      (cVF (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) 3 (aF (l.take 16))) (l.getD 17 0)) 1⟩
  refine ⟨K.sup K4, fun Fm CH hc hL hc' C hC => ?_⟩
  obtain ⟨hL1, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  have hthr : ∀ c ∈ Fm.cLast, max (thrF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) 1
      (cVF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut)) Fm.CGam) 1 ≤ c := by
    intro c hc0
    have h := hL4.2.2.2 c hc0
    simp only [K4] at h
    rwa [constant_list_cylinder, constant_list_trace, cOut_take, constant_list_gamma] at h
  have hC' : C₀F (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) 1
      (cVF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut)) Fm.CGam ≤ C := by
    simp only [C₀f] at hC
    rwa [constant_list_cylinder, constant_list_trace, cOut_take, constant_list_gamma] at hC
  have hCl1 : 1 ≤ sCl Fm := le_sCl_of Fm fun c hc => (le_max_right _ _).trans (hthr c hc)
  refine (hR (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) 1
      (cVF (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut)) Fm.CGam eps
      (Fm.raise (yR (selG sel) yFG Fm hc')) rfl
      ((le_max_left _ _).trans (hthr _ (sC'_mem_cLast Fm)))
      (le_sCl_of Fm fun c hc => (le_max_left _ _).trans (hthr c hc)) (hK Fm CH hc hL1)).2
    (AtR (selG sel) yFG (hyFG sel hFX hWu) Fm hc')
    (YtR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF) Fm hc')
    (tiesR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF) Fm hc').1
    (tiesR (selG sel) yFG (hyFG sel hFX hWu) (fun _ => 1) (BGW sel hBW (fun _ => 1) (fun _ => zero_le_one))
      (MGW sel hFX hWu hBW hRM hJF hCF) Fm hc').2
    (fun x i => _root_.beta_l_unique (Fm.D x i)) ?_ C hC'
  refine ⟨0, fun x _ i hx u u' hH t hG hr => ?_⟩
  exact hcV (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 (aF Fm.cOut) (Fm.D x i)
    ((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X
    ((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).Y
    (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1
    (((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).hI
      (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).1)
    (wOf ((selG sel Fm hc').2 x (raise_lt hx) (h0R (selG sel) yFG hx) i).X)
    (hOf _ _ _ _)
    (aOfW _ _ _ _ (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
    (hvOfW _ _ _ _ (hyFG sel hFX hWu Fm hc' x (raise_lt hx) (h0R (selG sel) yFG hx) (hyR (selG sel) yFG hx) i).2)
    (Fm.L x i) u u' _ _ hCl1 hH t hG hr

end GlobalTheory.LoopRowsCloseGap

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.loopRows_of_large_gap_discreteSeries : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → BpJoin.ThmBpDS → Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (𝒞 : FamClass) (sel : SSel 𝒞), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) → LoopRowS 3 𝒞 sel := by
  atlas_forward_decl GlobalTheory.LoopRowsCloseGap.loop_rows_closed_gap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn

namespace GlobalTheory.LoopRowsByName

theorem loopRows_of_rowsFinDim :
    Formalism.L2.SG.RowsDef.RowsFinDim → (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), Formalism.L2.TSel 𝒞 →
      ∀ sel : SSel 𝒞, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → LoopRowS 3 𝒞 sel := by
  intro hFin hUT 𝒞 hT sel hTu
  exact GlobalTheory.T.loopRows_of_large_gap_discreteSeries (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2 GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional
    GlobalTheory.wuDecayOfGap hFin 𝒞 sel hTu (GlobalTheory.ranks_and_frame_of_tied_class hUT 𝒞 hT).1

end GlobalTheory.LoopRowsByName
end
