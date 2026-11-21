import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringGramMatrixOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMeasureReductionBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsDeepCoveringLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepGoodReductionStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDegreeMultiplicative
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStatementOfKnownTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightLowerBoundGeneral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelLowerBoundOfComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundOfAllEstimatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundOfAllEstimates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLowDefectBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingOfCoveringDescent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDescentMapsCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringRankOfDescentSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankGrowthBoundSmallScale
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMinGenusBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatAtOfSplitCovering
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatValStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringCutOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringBadLocusOfDescentSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLambdaInvariantBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRationalOfLocalTraces

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.AnchorRd
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.AnchorRd
namespace GlobalTheory.CovTop
theorem anchor_holds_alt : _root_.GlobalTheory.CovTop.AnchorCondition := by
  refine Closed.imp (Closed.and _root_.GlobalTheory.CovTop.WtShape.wtN_z (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1)) ?_
  rintro eps Fm CH - ⟨⟨C1, -, hW⟩, ⟨A, -, hH⟩⟩
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hW hH
  exact ⟨100, by norm_num, x0, fun x hx hle ι p hp i =>
    AnchorRd.anchorAt_of p i (Fm.params x hx ι) ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩
end GlobalTheory.CovTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchor_bound : _root_.GlobalTheory.CovTop.AnchorCondition := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.anchor_holds_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.DeepExist
theorem exists_deep_covering_level_alt (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : _root_.GlobalTheory.CovTop.DeepExistence := by
  refine Closed.imp (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi => ?_⟩
  have hN := h x hx hle ι p hp i
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_good_cover_over_sized_field hP.p8 (Fm.D x ι) p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) ⟨by omega, i.isLt⟩ hN.split
    hN.cop (expL (Fm.L x ι).sc.L)
  refine ⟨Y, (goodCov_iff p i Y).2 (hY.mono (size_le hN ?_))⟩
  exact RecTied.core_size_le p hp.2 (by linarith [hN.big.2.1])
end GlobalTheory.CovTop.DeepExist
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_deepEx_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepExistence := by
  first | exact @_root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt | exact _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt | (intros; apply _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop.FromComp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem u_low_of_cover_hyps (h1 : _root_.GlobalTheory.CovTop.DeepGoodness) (h2 : _root_.GlobalTheory.CovTop.SizeCondition) (h3 : _root_.GlobalTheory.CovTop.CoverDegree) (h4 : _root_.GlobalTheory.CovTop.ShareCondition) (h5 : _root_.GlobalTheory.CovTop.HeightCondition) (h6 : _root_.GlobalTheory.CovTop.CoverHeightSum) (h7 : _root_.GlobalTheory.CovTop.SumBoundCondition) : _root_.GlobalTheory.CovTop.UniformLowerBound := by
  refine Closed.imp (Closed.and h1 (Closed.and h2 (Closed.and h3 (Closed.and h4 (Closed.and h5 (Closed.and h6 h7)))))) ?_
  rintro _ Fm _ _ ⟨⟨_, -, a1⟩, ⟨A, -, a2⟩, ⟨_, -, a3⟩, ⟨_, -, a4⟩, ⟨C1, hC1, a5⟩, ⟨C2, hC2, a6⟩, ⟨_, -, a7⟩⟩
  refine ⟨2 * (3 * C1 + C2 + 4), by positivity, ?_⟩
  obtain ⟨x0, h⟩ := a1.and (a2.and (a3.and (a4.and (a5.and (a6.and a7)))))
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h x hx hle ι p hp
  exact atPoint p i Y _ A C1 C2 hi (b1 i hi Y hY) (b2 i) (b3 i hi Y hY) (b4 i hi Y hY) (b5 i hi Y hY) (b6 i hi Y hY)
    (b7 i hi Y hY)
end GlobalTheory.CovTop.FromComp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_lower_bound_of_sums' : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.HeightCondition → _root_.GlobalTheory.CovTop.CoverHeightSum → _root_.GlobalTheory.CovTop.SumBoundCondition → _root_.GlobalTheory.CovTop.UniformLowerBound := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions
namespace GlobalTheory.CovTop
theorem sumC_of_deepGood_alt : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩
end GlobalTheory.CovTop
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_c_of_deep_good : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.sumC_of_deepGood_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.LowCover
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem low_of_cover_hypotheses : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LowDefectCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition → _root_.GlobalTheory.CovTop.MapsCondition → _root_.GlobalTheory.CovTop.CoverRank → _root_.GlobalTheory.CovTop.MinimalGenerator → _root_.GlobalTheory.CovTop.FlatnessCondition → _root_.GlobalTheory.CovTop.UniformLowerBound → _root_.GlobalTheory.CovTop.LiftLowBound := by
  intro hS hD hE hG hR hM hK hGm hF hU
  refine Closed.imp (((((((((hS.and hD).and hE).and hG).and hR).and hM).and hK).and hGm).and hF).and hU) ?_
  intro eps Fm CH _ hh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨CS, -, aS⟩, CD, -, aD⟩, _, -, aE⟩, _, -, aG⟩, _, -, aR⟩, _, -, aM⟩, _, -, aK⟩, _, -, aGm⟩,
    CF, hCF, aF⟩, CU, hCU, aU⟩ := hh
  refine ⟨max CD (2 * (CF + CU) + 9), le_max_of_le_right (by linarith), ?_⟩
  obtain ⟨x0, h⟩ := ((((((((aS.and aD).and aE).and aG).and aR).and aM).and aK).and aGm).and aF).and aU
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨bS, bD⟩, bE⟩, bG⟩, bR⟩, bM⟩, bK⟩, bGm⟩, bF⟩, bU⟩ := h x hx hle ι p hp
  have hS' := bS i
  have hE0 : 0 ≤ unitE p := by obtain ⟨a, b, -⟩ := hS'; linarith
  rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with heq | hlt
  · exact lowAt_mono (bD i heq) (le_max_left _ _) hE0
  · obtain ⟨Y, hY⟩ := bE i hlt
    exact lowAt_mono (lowAt_of_cover p i _ CS CF CU hCF hCU hS' Y (bG i hlt Y hY) (bR i hlt Y hY) (bM i hlt Y hY)
      (bK i hlt Y hY) (bGm i hlt Y hY) (bF i hlt Y hY) (bU i hlt Y hY)) (le_max_right _ _) hE0
end GlobalTheory.CovTop.LowCover
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLowBound_of_cover_estimates : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LowDefectCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition → _root_.GlobalTheory.CovTop.MapsCondition → _root_.GlobalTheory.CovTop.CoverRank → _root_.GlobalTheory.CovTop.MinimalGenerator → _root_.GlobalTheory.CovTop.FlatnessCondition → _root_.GlobalTheory.CovTop.UniformLowerBound → _root_.GlobalTheory.CovTop.LiftLowBound := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.LowCover.low_of_cover_hypotheses
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem covering_rank_of_descent_steps_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverRank := by
  intro hX h1 h2 h3 hS hT hL h4 h5 h6 h7 h8
  refine Formalism.MainNotions.Closed.imp (_root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt hX h1 hS hT h2 h3 hL h4 h5 h6 h7 h8) ?_
  rintro _ Fm _ _ ⟨C, h0, a, h⟩
  refine ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => ?_⟩
  have H := h x hx hle ι p hp i hi Y hY 1 le_rfl (by norm_num)
  rw [Nat.cast_one, one_mul] at H
  refine H.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact add_le_add le_rfl (min_le_right _ _)
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverRank_of_coverDegree_and_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoverRank := by
  first | exact @_root_.GlobalTheory.CovTop.covering_rank_of_descent_steps_alt | exact _root_.GlobalTheory.CovTop.covering_rank_of_descent_steps_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_rank_of_descent_steps_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw
namespace GlobalTheory.FlatSplit
section Congr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}
end Congr
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)
end Weights
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
theorem flat_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.FlatnessCondition := by
  intro hP hDG hFD hA
  refine Closed.imp (Closed.and (Closed.and (Closed.and (Closed.and hDG (_root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD)) hA) _root_.GlobalTheory.T.lift_weight_numerator)
    (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨CA, hCA, h3⟩⟩, ⟨C4, -, h4⟩⟩, ⟨C5, -, h5⟩⟩
  refine ⟨11 * CA + 83, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := (((h1.and h2).and h3).and h4).and h5
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hx x hx' hle ι p hp
  exact _root_.GlobalTheory.FlatSplit.flat_at_of_split_covering p i Y hY hP (a1 i hi Y hY) (a2 i hi Y hY) (a3 i) (a4 i) (a5 i)
end GlobalTheory.FlatSplit
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_prints_deepGood_flatDeg_anchor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.FlatnessCondition := by
  first | exact @_root_.GlobalTheory.FlatSplit.flat_alt_alt | exact _root_.GlobalTheory.FlatSplit.flat_alt_alt | (intros; apply _root_.GlobalTheory.FlatSplit.flat_alt_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology
namespace GlobalTheory.CovTop.Assembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covolX_of_lift_bounds_and_coreLe : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2 (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤ mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith
end GlobalTheory.CovTop.Assembly
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolX_of_truncation_badSet_lambda_lowBound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CoreSlope
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem coreLe_of_gram_meas_rat_alt : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftRational → _root_.GlobalTheory.CovTop.CoreBound' := by
  intro hg hm hr
  unfold _root_.GlobalTheory.CovTop.GramCondition _root_.GlobalTheory.CovTop.MeasureCondition _root_.GlobalTheory.CovTop.LiftRational _root_.GlobalTheory.CovTop.CoreBound' _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩
end GlobalTheory.CoreSlope
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreLe_of_gram_meas_liftRational : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftRational → _root_.GlobalTheory.CovTop.CoreBound' := by
  atlas_forward_decl _root_.GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates
set_option maxHeartbeats 1000000 in
theorem topCovolG_alt_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → _root_.GlobalTheory.CovTop.CovolumeBoundOfX :=
  by
  intro hSB hX hP hH hGD hQ hD
  have hS := hH.sieg
  have hK := hX.ks
  have hN := hX.lie
  have gram := _root_.GlobalTheory.T.covering_gram_of_prints hP
  have size := _root_.GlobalTheory.T.cov_size_bound
  have meas := _root_.GlobalTheory.T.covering_meas_of_prints hP
  have anc := _root_.GlobalTheory.T.anchor_bound
  have dex := _root_.GlobalTheory.T.covering_deepEx_of_prints hP
  have dg := _root_.GlobalTheory.T.deepGood_of_toroidal_and_semiabelian hP hGD hQ hS hK hN
  have fd := _root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints hP
  have deg := _root_.GlobalTheory.T.coverDegree_of_grothendieck_deformation hX hP hS hK hGD hQ hN dg size fd
  have sh := _root_.GlobalTheory.T.share_of_deep_good_size_flat_deg_cover_degree hX hP hS hK hGD hQ hN dg size fd deg
  have ht := _root_.SelfIntersectionVolumeEstimates.height_lower_bound_general_alt hSB hX hGD hQ hP hH hD dg size deg fd
  have hs := _root_.GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share hX hP hGD hQ hS hK hN dg size fd deg sh
  have ul := _root_.GlobalTheory.T.uniform_lower_bound_of_sums' dg size deg sh ht hs (_root_.GlobalTheory.T.sum_c_of_deep_good dg)
  have low := _root_.GlobalTheory.T.liftLowBound_of_cover_estimates size (_root_.GlobalTheory.T.lowDef_of_gram_of_anchor hP gram anc) dex dg (_root_.GlobalTheory.T.covering_ring_of_prints_gram_deepGood hP gram dg) (_root_.GlobalTheory.T.covering_maps_of_gram_deep_size_flatDeg hP hGD hQ hS hK hN gram dg size fd) (_root_.GlobalTheory.T.coverRank_of_coverDegree_and_share hX hP hGD hQ hS hK hN dg size fd deg sh) (_root_.GlobalTheory.T.covering_gmin_of_prints_gram_deep_size hP gram dg size) (_root_.GlobalTheory.T.flat_of_prints_deepGood_flatDeg_anchor hP dg fd anc) ul
  exact _root_.GlobalTheory.T.covolX_of_truncation_badSet_lambda_lowBound gram (_root_.GlobalTheory.T.lift_recursion_of_gram_bound gram) (_root_.GlobalTheory.T.liftTruncation_of_prints hP) (_root_.GlobalTheory.T.liftBadSet_of_deep_size_flatDeg_share hX hP hGD hQ hS hK hN hX.green gram dex dg size fd deg sh) (_root_.GlobalTheory.T.liftLambdaBound_of_gram_meas hP gram meas) size (_root_.GlobalTheory.T.coreLe_of_gram_meas_liftRational gram meas (_root_.GlobalTheory.T.liftRational_of_prints hP)) low
end SelfIntersectionVolumeEstimates
end
end
end
