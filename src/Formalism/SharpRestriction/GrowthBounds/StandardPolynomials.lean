import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KapCore
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankOnDigitsCast
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockFG
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseThresholdRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFFinal
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestAssumptionsOfThreeInterfaces
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestTCore
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColTop
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColumnPolynomialCovectorZero

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem closed_extendedAllConclusions {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

theorem dimYAt_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : DimYAt :=
  dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)




def Open : Prop := RestPairLift

theorem stmtEExt_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY := dimYAt_of_adm hA
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hK2 : LeadingRowsBeyondThreshold := top_rows_bound_holds
  have hB : BlockRankAt := blockRankAt
  have hK4 : KeptBlocksBeyondThreshold := kept_blocks_holds
  have hL1 : PartnersToFactors := partners_to_factors_holds
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB hK2
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of hK2))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU hK4
  closed_extendedAllConclusions hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) hL1 (restLift_of (restLiftVec_of hPL))


end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem witt_identification_of_admitted {D : Formalism.BasicNotions.D7} (hA : admitted D) : WittIdent :=
  hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem restForm (D : Formalism.BasicNotions.D7) : RestForm :=
  restForm_of_oplus (Formalism.MainNotions.G.GLWeightTheory.lemma_five_two_first_holds D) restOPlus

theorem stmtEExt_of_rawTail1 {D : Formalism.BasicNotions.D7} (h : admitted D → RestRawTail1) : ExtendedClosedForm D :=
  stmtEExt_of fun hA => paired_lifts_of_identity (witt_identification_of_admitted hA) (h hA) (restForm D)

def RawTailReduction : Prop := RestAsmRT

theorem stmtEExt_of_15c {D : Formalism.BasicNotions.D7} (h : admitted D → RawTailReduction) : ExtendedClosedForm D :=
  stmtEExt_of_rawTail1 fun hA => restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res))) (h hA)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def GrowthBoundInterfaceConditions : Prop := RestCols ∧ RestPre ∧ RestTCore

theorem extendedClosedForm_of_interfaceConditions {D : Formalism.BasicNotions.D7} (h : admitted D → GrowthBoundInterfaceConditions) : ExtendedClosedForm D := stmtEExt_of_15c fun hA => rest_assumptions_of_three_interfaces hA (h hA).1 (h hA).2.1 (h hA).2.2

theorem growthBoundInterfaceConditions : GrowthBoundInterfaceConditions := ⟨restCols, restPre, restTCore⟩


theorem extendedClosedForm (D : Formalism.BasicNotions.D7) : ExtendedClosedForm D := extendedClosedForm_of_interfaceConditions fun _ => growthBoundInterfaceConditions

end Formalism.MainNotions.ColumnSystems.Pf
end
end
