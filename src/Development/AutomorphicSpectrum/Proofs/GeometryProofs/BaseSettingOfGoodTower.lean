import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBound
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportional
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.StokesLimitBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomMassIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomCuspIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChartStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTp
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitT
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpIntegrandLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRegAboveWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsMonoSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNMixedExpand
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNVbInt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarChartSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSemipos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryNull
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcChartSemipos
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcLeviChart
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PAPrimeMarginCharts
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PChartVelLiftCharts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLeviLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GoodOriginTowerHeight
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenericFibreIntersectionPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AbelianCmStokesIdentity

section
noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.StokesLimitBound

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def localDataToSetting_of_scaleMove (H : HodgeData D) (Cd : CuspData D O Lt) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H))
    (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)) (hS : S.IsTied) (hS' : S'.IsTied) : ComponentSetting D O Lt :=
  ⟨H, Cd, M, S, hS, S', hS', 1, 0⟩

end Clauses

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  first | exact @LevelTowerAlt.good_origin_tower_height | exact LevelTowerAlt.good_origin_tower_height
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open SheetDecomposition.PF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  intro II hII K _ ρ _ K' _ ρ' _ κ v P' d r G Jf L L' N hv hP' hP hJ hL hLL' hN
  have hA : IsArithVar P' (d + r + 1) := by rwa [Nat.add_right_comm] at hP'
  have hs : ∀ j, IsSmoothHerm (Fin.append L' N j) := fun j => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]
      exact GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hv (hLL' j) (hL j)
    · rw [Fin.append_right]
      exact hN j
  have h := GlobalTheory.T.projection_formula_of_arith_system ⟨II, hII⟩ II hII.1 K ρ K' ρ' κ v P' (d + 1) r G Jf
    (Fin.snoc (α := fun _ => HermLine ρ) L (cst ρ)) (Fin.snoc (α := fun _ => HermLine ρ') L' (cst ρ')) N hv hP' hP hJ
    (LevelTowerAlt.snoc_cst_smooth L hL)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.snoc_last]
        refine ⟨?_, fun z => rfl⟩
        show (0 : K' → ℤ) = pullDeg κ 0
        funext k
        by_cases hk : ∃ a, κ a = k
        · obtain ⟨a, rfl⟩ := hk
          exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
        · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm
      · simpa using hLL' j)
    hN
  rw [LevelTowerAlt.ii_cst_int hII.1 hP L hL, ← position_eq, ii_cast hII.1 _ hA _ (LevelTowerAlt.snoc_cst_smooth _ hs), LevelTowerAlt.ii_cst_int hII.1 hA _ hs,
    mul_neg, neg_inj] at h
  exact h
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem testPoly_eq_slX : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  intro hAg hPr hCmp hGiv hPts E _ _ _ _ H D Xo l c Y _ T o II hGl hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or hB hBB hqp hbg hsm hGood hgen hS
  have hIn : PB.Inputs := hGiv.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty (CMType H) := GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.cm_nonempty H
  have hUnif := GlobalTheory.T.good_tower_real_agreement hGiv E H D Xo l c Y T o II hGl hEx hII hp hq
  have hProp : T.Proportional :=
    GlobalTheory.T.real_tower_proportional hPr hIn II hII (CMType H) (D.p + D.q) T (Top.realOf o.toTowerOrigin) hUnif
  have hJpos : 0 < Top.testDeg (CMType H) (D.p + D.q) T.j :=
    (GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) T.j T.j_pos T.j_lt).2.1
  have hLim : ArLimExists X.H X.S B :=
    (GlobalTheory.T.height_comparison_between_models hGiv hPts K J II (CMType H) Ω W Dc X.H X.M X.M X.S X.S B hII X.S_tied X.S_tied).1
  have hMass := (GlobalTheory.T.measure_limit_statement_holds II (CMType H) K J Ω W Dc O Lt X B hII.1 hLim).2
  have hSm := GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II (CMType H) Ω W Dc X.H X.M X.S B X.S_tied
  obtain ⟨K₃, _, ι₃, _, κ, v, P₃, e, r, cf, Mt, Nt, δ, hb, hY, himg, hδ, hdeg, hNs, hpull, hT, hGeo⟩ :=
    GlobalTheory.T.good_origin_intersection_relay hAg hPr hCmp hGiv hPts E H D Xo l c Y T o II hGl hEx hII hp hq B B₁ a K J Ω W Dc O Lt X Or hB hBB hqp hbg hsm hGood hgen hS
  have hXar : IsArithVar (imageZ v P₃) (Dc.n + 1) := by rw [himg]; exact Dc.arith
  obtain ⟨G⟩ := GlobalTheory.CompanionTheory.Ar.PB.Known.genFibreExists K J K₃ ι₃ κ v P₃ _ hb hY
  obtain ⟨Jf, hJf, -⟩ := (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers G.Φ (FibreBlock κ) (fibreIdx ι₃ κ)).1
  have hPF := GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula ⟨II, hII⟩
  set fibN : Fin r → ℝ := fun m => (Jf (fibreIdeal κ G) e (fun i => fibreDeg κ (Nt 1 m i).a) : ℝ) with hfibN
  set fib : ℝ := ∑ m, cf m * fibN m with hfib
  have hEq1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m)) =
      fib * arLimFun X.H X.S B t := by
    filter_upwards [hSm, hpull] with t ht hp'
    rw [hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := hPF II hII.1 K J K₃ ι₃ κ v P₃ (Dc.n + 1) e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt t m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs t m)
    have hd : (fun i => fibreDeg κ (Nt t m i).a) = fun i => fibreDeg κ (Nt 1 m i).a := by
      funext i; rw [hdeg t m i]
    rw [h, himg, hd]
    simp only [arLimFun, hfibN]
    ring
  have hEq2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      fib * geomDeg (mCoordIdeal Dc.y) (muReg X.H X.S B t) Dc.n := by
    filter_upwards [hSm, hpull, hGeo] with t ht hp' hg
    rw [← hg, hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image II hII K J K₃ ι₃ κ v P₃ Dc.n e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt 1 m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs 1 m)
    rw [h, himg]
    simp only [geomDeg, hfibN]
    ring
  obtain ⟨L, hL⟩ := hLim
  have hA : arLim X.H X.S B = L := hL.limUnder_eq
  have h1 : δ * T.PPc II B a (Top.testPoly T.j) = fib * L :=
    tendsto_nhds_unique hT ((hL.const_mul fib).congr' (hEq1.mono fun t h => h.symm))
  have h2 : δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = fib * degMu X.H :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hEq2) (hMass.const_mul fib)
  have h3 : (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := hProp.2.1 B a _
  rw [h3] at h2
  have hvol : 0 < T.vol a := hProp.1 a
  have hvJ : 0 < T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := mul_pos hvol hJpos
  have hpos : 0 < fib * degMu X.H := by rw [← h2]; exact mul_pos hδ hvJ
  have hd0 : 0 ≤ degMu X.H := GlobalTheory.CompanionTheory.StokesCompare.degMu_nonneg X
  have hdpos : 0 < degMu X.H := by
    refine lt_of_le_of_ne hd0 fun h => ?_
    rw [← h, mul_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨hdpos, ⟨L, hL⟩, ?_⟩
  have hj : Dc.j = D.p := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · obtain ⟨τ⟩ := (inferInstance : Nonempty (CMType H))
      have := congrFun (hbg.symm.trans h) τ
      simp at this
  have hNn : Dc.N = D.p + D.q := Or.N_eq
  have hdim : ((Dc.n + 1 : ℕ) : ℝ) = (Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1 := by
    have hjT : T.j = D.p := o.j_eq
    have : Dc.n = Top.dimX (CMType H) (D.p + D.q) T.j := by
      simp only [ComponentData.n, Top.dimX, hj, hNn, hjT]
      ring
    rw [this]
    push_cast
    ring
  have hne : ((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) ≠ 0 := by positivity
  have hsl : slX X B = L / (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * degMu X.H) := by
    rw [slX, hA, hdim]
  rw [hsl]
  apply mul_left_cancel₀ hδ.ne'
  rw [h1]
  have hdn := hdpos.ne'
  field_simp
  linear_combination (-L) * h2

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_intersection_tower : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  first | exact @ModelDimension.abelian_cm_stokes_identity | exact ModelDimension.abelian_cm_stokes_identity
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.intersection_final_estimate
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopBase

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

theorem base_setting_of_good_origin : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  intro Ch Cu hNine hWeil hAgr hProp hCmp hGiven hPts E _ _ _ _ H D Xo l c Y _ T o II hGlob hExtra hFull hp hq hqp
    hbad B hB a
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  haveI := hne
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr hne
  have hN2 : 2 ≤ D.p + D.q := by omega
  have hsq : 4 ≤ (D.p + D.q) ^ 2 := by nlinarith
  have hB16 : 16 * Fintype.card (CMType H) ≤ B := by nlinarith
  have hB2 : 2 ≤ B := by omega
  have hB4 : 4 * Fintype.card (CMType H) + 2 ≤ B := by omega
  have hgen : genPt (o.Or B a).𝔐.ξ₀ = genPt (o.Fx a).ξf :=
    genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset ℕ, ∀ r, r ∈ S₁ ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad :=
    ⟨(Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ∉ T.bad), by
      intro r
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h3⟩⟩
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp => ((o.bad_iff p).1 hp).1
  have hS₁P : ∀ p ∈ S₁, p.Prime := fun p hp => ((hS₁ p).1 hp).1
  have hdisj : Disjoint S₁ T.bad := Finset.disjoint_left.2 fun p hp hp' => ((hS₁ p).1 hp).2.2 hp'
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ T.bad := fun p hp hd =>
    (o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, hgen', hS, hj, hbg, -, hHT⟩ :=
    GlobalTheory.T.full_intersection_generic_bound hGiven hWeil E H D Xo l c Y II hFull hGlob hp hq _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ T.bad S₁
      false hbadP hS₁P hdisj hdisc
  simp only [Bool.false_eq_true, if_false] at hj hbg
  have hsm : Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨h, -, -⟩
    · exact h
    · exact absurd (congrFun (hbg.symm.trans h) hne.some) Sum.inl_ne_inr
  have hGood : Or.Good :=
    ⟨fun p hp => hHT p (Finset.mem_union_left _ hp),
      fun p hp => hHT p (Finset.mem_union_right _ (by rw [← hS]; exact hp))⟩
  have hSc : ∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad := by
    intro r; rw [hS]; exact hS₁ r
  have hN : Dc.N = D.p + D.q := Or.N_eq
  have hAdm : admitted Xo l c Y Or B := by
    refine ⟨hGlob, hGood, o.bad_iff, ?_, ?_, hSc, ?_⟩
    · show T.bad.card ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2
      rw [hN]; exact hbad
    · exact hB4
    · show Dc.N - Dc.j ≤ Dc.j
      rw [hN, hj]; omega
  obtain ⟨U, M, S, S', hcw, hU0, hUt, hSt, hS't, hconj⟩ :=
    GlobalTheory.T.cusp_weight_regularisations_tied hGiven E H D Xo l c Y II K J Ω W Dc Hd T.bad Or
  obtain ⟨hpos, hht, hmean⟩ := hNine E H D Xo l c Y II K J Ω W Dc Hd T.bad Or B U M S' hFull hAdm hcw hS't
  obtain ⟨X, hXH, hXU, hXrd, hXL, hX1, hX2, hX3, hX4, hX5⟩ :=
    GlobalTheory.T.corrected_weight_regularization K J II (CMType H) Ω W Dc Hd M U S S' (hostRd E) (hostLval H) Ch Cu hSt hS't hU0 hUt hpos hconj
      hht hmean
  subst hXH
  obtain ⟨hdeg, hlim, hPP⟩ := GlobalTheory.T.good_origin_intersection_tower hAgr hProp hCmp hGiven hPts E H D Xo l c Y T o II hGlob hExtra hFull hp hq
    B B a K J Ω W Dc ℤ (Fin 2 → ℤ) X Or hB2 le_rfl hqp hbg hsm hGood (hgen'.trans hgen) hSc
  obtain ⟨-, -, hSemi, -, hResK, -, -, hGaga, -, hInputs, -, hAn, -, -⟩ := hGiven
  have hStk : Top.StokesAt X B :=
    GlobalTheory.T.intersection_final_estimate hInputs hAn hResK hGaga hSemi E H D Xo l c Y II K J Ω W Dc X.H T.bad Or B U hFull hAdm hcw ℤ
      (Fin 2 → ℤ) X rfl hXU hX1 B hB4 hlim
  exact ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, W, inferInstance, inferInstance, Dc, ℤ,
    Fin 2 → ℤ, inferInstance, inferInstance, inferInstance, X, hN, hj.trans o.j_eq.symm, hXrd, hXL, hX1, hX2, hX3, hX4,
    hX5, hdeg, hlim, hStk, hPP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopBase
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_setting_of_good_tower : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.TopBase.base_setting_of_good_origin
end
