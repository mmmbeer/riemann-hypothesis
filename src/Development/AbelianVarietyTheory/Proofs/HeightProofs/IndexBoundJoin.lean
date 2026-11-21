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
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedBoundForRunScalarsStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditionsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditions
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralFormsLogSupNormLowerBoundAbsolute
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBoundStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PageBoundPolynomialDomination
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBounds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBound
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesIndefiniteLiftIndex
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.NetNorms Formalism.L2.Pj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.NetWire

def NormLaws {D : D7} (B : WeightFamilies.Prov D) (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ) : Prop :=
  (∀ j ka σ F, 0 ≤ N j ka σ F) ∧ (∀ j ka σ F, N j ka σ F = 0 ↔ F = 0) ∧
  (∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F) ∧
  (∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G) ∧
  (∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

section Defs

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ} (n : NormLaws B N)

abbrev base : WeightFamilies.Prov D := withNorm B N n.1 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2

def pj (X : PJ D B P j) : PJ D (base n) P j := PJ.tol2NormAlt N n.1 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 X

def sc (S : Scal B) : Scal (base n) := scalarsWithNorm N n.1 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 S

def gd {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) : GlobalFamilyData (pj n X) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

end Defs

section Wrappers

def FinalTheorems (α : Sort 1) : Sort 1 := α

def Tgt (α : Sort 1) : Sort 1 := α

def SrcP (p : Prop) : Prop := p

def TgtP (p : Prop) : Prop := p

end Wrappers

local unif_hint (α β : Type) where
  ⊢ FinalTheorems α =?= Tgt β

local unif_hint (p q : Prop) where
  ⊢ SrcP p =?= TgtP q

attribute [local irreducible] FinalTheorems Tgt SrcP TgtP

end GlobalTheory.NetWire
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunJoin

theorem genOK_refill {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (c : ℝ) (hG : GenOK h j hj large₂ G S c)
    (del th' rz alz th0 zc rq th iet et) :
    GenOK h j hj large₂ (FamilyHypotheses.refill G del th' rz alz th0 zc rq th iet et) S c := hG

end GlobalTheory.RunJoin
end
