import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelValueIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairValueIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelCommonModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerRest
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinvertdiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullback
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinright
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPlainValueIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFurtherTermIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivFibreVariety
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagVertSymmIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrict
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFrameOfFullFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.TrivFlagKills
import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagInd
import BuildAid.ForwardExisting
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff

section
namespace GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.JoinPullbackAlt.Statement := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  obtain ⟨EB, hEB⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E).1 K' ι' z
  obtain ⟨E'B, hE'B⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E').1 K' ι' z
  exact ⟨EB, E'B, hEB, hE'B,
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hEB hE'B).2.1 hE⟩

end GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt
end

section
namespace GlobalTheory.CompanionTheory.Heights

theorem join_vertical_divisor_statement : GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.Statement :=
  PositivityTheory.Xgn.t_s_joinvertdiv

end GlobalTheory.CompanionTheory.Heights
end

section
namespace GlobalTheory.CompanionTheory.CommAlg

theorem joinTwoModels : GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof

end GlobalTheory.CompanionTheory.CommAlg
end

section
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof)
    (GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft.proof GlobalTheory.T.pair_number_pullback
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.BirationalJoin.proof)

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_join_left : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main
end

section
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback GlobalTheory.T.pair_number_pullback

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main
end

section
section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement :=
  FlagPlainValueIndependence.proof GlobalTheory.T.flag_independence FlagPairCharacterisation.proof VerticalDivisorSupportFibre.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_plain_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue.main
end

section
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V) (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ), IsFlagFrame y B w b → IsFlagFrame y B v u → ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → ∀ Y : List (K → ℤ), Y.length + c = e → ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList b μ ++ Y) = ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList u μ ++ Y) := by
  first | exact @PositivityTheory.HtPt.Pflag.field_flag_indep | exact PositivityTheory.HtPt.Pflag.field_flag_indep
end

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_intNumL_classList_eq_of_isSymmetric : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle F (segreVec y) N V) (w v : Module.Basis (Fin N) Ω V) (b u : Fin N → K → ℤ), IsFlagFrame y B w b → IsFlagFrame y B v u → ∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → ∀ Y : List (K → ℤ), Y.length + c = e → ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList b μ ++ Y) = ∑ μ ∈ G.support, G.coeff μ * intNumL F (pointIdeal F y) (classList u μ ++ Y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.sum_intNumL_classList_eq_of_isSymmetric
end

section
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

theorem polyNum_eq_sum {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (V : Ideal (MRing ι F)) (e : ℕ)
    (hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V e) {N : ℕ} (d : Fin N → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (c n : ℕ) (Y : Fin n → K → ℤ) (hG : G.IsHomogeneous c)
    (hcn : c + n = e) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I V e (Fin.append d Y)
                              (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
      ∑ μ ∈ G.support, G.coeff μ * intNumL F V (classList d μ ++ List.ofFn Y) := by
  rw [SegreFlagIndep.prod_X_natAdd, SegreFlagIndep.polyNum_mul_monomial, SegreFlagIndep.monoList_ones]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  have hdeg : α.degree = c := by
    have := hG (mem_support_iff.mp hα)
    rwa [Finsupp.degree_eq_weight_one]
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList d α ++ List.ofFn Y).length = e := by
    rw [List.length_append, SegreFlagIndep.length_monoList, hdeg, List.length_ofFn, hcn]
  rw [SegreFlagIndep.listNum, dif_pos hlen,
    Numbers.agree FieldNumbers.IntNumUnique.full (IntNumPoint.proof FieldNumbers.IntNumBase.full)
      FieldNumbers.IntNumBase.full I hI V e _ hV,
    BundleExamples.intNum_get_cast F V _ e hlen]
  refine FlagTypings.intNumL_perm F V (List.Perm.append_right _ ?_)
  rw [BundleExamples.monoList_eq]
  exact FlagTypings.monoList_perm d α

theorem segreFlagIndep (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι := by
  classical
  intro x e hV N E _ _ B fl₁ fl₂ I hI G hG c n Y hGc hcn
  obtain ⟨w, hw⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₁
  obtain ⟨v, hv⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₂
  rw [polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn, polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn]
  have hI' := VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι (pointIdeal F x)
  have hP : IsMultiProjPrime (pointIdeal F x) := ⟨hV.1.1, hI'.1 hV.1.2.1, hV.1.2.2⟩
  exact GlobalTheory.T.sum_intNumL_classList_eq_of_isSymmetric F Ω K ι x e hP hV.2 N E B w v _ _ hw hv c G hG hGc (List.ofFn Y)
    (by rw [List.length_ofFn]; omega)

end GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem flag_further_term_independent :
    GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagVerticalSymmetric.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagRestriction.proof
      FurtherIndep.segreFlagIndep)

end GlobalTheory.CompanionTheory.Ar.Num
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_further_term_independent_statement : GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.flag_further_term_independent
end

section
section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagModelValue

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem main : FlagModelValueIndependence.Statement :=
  FlagModelValueIndependence.proof
    (FlagPairValueIndependence.proof GlobalTheory.T.flag_plain_value_independent GlobalTheory.T.flag_further_term_independent_statement)
    (FlagModelCommonModel.proof GlobalTheory.CompanionTheory.CommAlg.joinTwoModels GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt.main
      GlobalTheory.CompanionTheory.Heights.join_vertical_divisor_statement GlobalTheory.T.flag_model_join_left GlobalTheory.T.flag_model_join_right)

end GlobalTheory.CompanionTheory.CommAlg.FlagModelValue
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_value_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelValueIndependence.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main
end
