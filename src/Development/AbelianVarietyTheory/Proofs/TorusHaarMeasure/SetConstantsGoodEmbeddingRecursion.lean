import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMul
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponents

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendenceDegree_ratios_cuspForms_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z (G.w k₀).1 ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z (G.w k).1 / evC hG Z (G.w k₀).1)) = WeightFamilies.dimY D j := by
  first | exact @GlobalTheory.BigTrdeg.trdeg_ratios_record | exact GlobalTheory.BigTrdeg.trdeg_ratios_record | (intros; apply GlobalTheory.BigTrdeg.trdeg_ratios_record <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

noncomputable section

namespace GlobalTheory.BigRec

section Inst

variable {D : D7} {T : Top D}

variable (h : LawsP T) {j : ℕ} (hj : InR D j)

end Inst

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bigAt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg _
  exact ⟨hN, GlobalTheory.T.transcendenceDegree_ratios_cuspForms_components D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg⟩

end GlobalTheory.BigRec
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_constants_good_embedding_recursion : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  atlas_forward_decl GlobalTheory.BigRec.bigAt_record
end
