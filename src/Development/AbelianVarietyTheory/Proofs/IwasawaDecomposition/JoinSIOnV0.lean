import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeOfImNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem chainTie_and_v0Onto :
    ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool)
      (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), (R.DcPt → M.ChainTie) ∧ (R.ReadingFormsSpanGoodSubspace → M.GoodPartHasComplexCoordinates) := by
  intro D Bs A X fc s R cr M
  refine ⟨fun h u x y => ?_, fun h => ?_⟩
  · rw [M.cφ_eq, M.cF_eq]
    exact (h u x y).symm
  · unfold Seam.GoodPartHasComplexCoordinates
    rw [← h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, M.cF_eq y⟩

end GlobalTheory.Mem.SJ
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem cxFacts_of_prims : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → CxFacts (R.toCx3 F) F.cr (F.eV (R.toCx3 F).zs) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hC hP
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hSep hC hP
  exact
    { wf := hR.wf true
      h2 := (hR.what₂ true).1
      pos := hR.h4pos
      theta := fun y => CxData.theta_eV _ _ _ _ hR.jIsoR (hR.levs true).1 (hR.levs true).2.1 (hR.levs true).2.2
        (definite_coordinates_in_good_part _ true) (EvTie.evTie_of_ok hOk F _) _ y }

end GlobalTheory.Mem.SJ
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem kOf_apply_self_on {K : Type} [Field K] (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a := by
  unfold kOf
  have h : ∃ b : K, σ b = σ a := ⟨a, rfl⟩
  rw [dif_pos h]
  exact σ.injective h.choose_spec

theorem relMat_self_on {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  ext i k
  have h : ∃ y, f y = f (Pi.single k 1) := ⟨_, rfl⟩
  have : solve f (f (Pi.single k 1)) = Pi.single k 1 := by
    unfold solve
    rw [dif_pos h]
    exact hf h.choose_spec
  simp only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

theorem kMat_one_on {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_apply_self_on σ 1
  · simpa using kOf_apply_self_on σ 0

theorem thetaMap_referenceTuple_goodPart_onto_rows : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → R.ReadingFormsSpanGoodSubspace → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D Bs A X fc s R cr eV hF hI hV
  have h1 : X.rowMat cr true Bs.μ0 = 1 := by
    unfold CxData.rowMat CxData.rowMatC
    rw [relMat_self_on _ hF.h2.1, kMat_one_on]
  rw [eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx⟩ := R.eRR.surjective (D.div.RR.b i)
  obtain ⟨y, hy⟩ := hF.wf.Pq_surj Bs.μ0 x
  refine ⟨R.jV y, ?_, ?_⟩
  · have : R.jV y ∈ Submodule.span ℂ (Set.range R.jV) := Submodule.subset_span ⟨y, rfl⟩
    rw [hV] at this
    exact this
  · have := hI y
    rw [h1, Matrix.one_mulVec] at this
    exact this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))

end GlobalTheory.Mem.SJ
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem sharp_iota_eq (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [PrimeDegreeVariant.sharp_downTo]
  rfl

theorem exists_read_of_matrix_tie (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (hv : Bs.v0 = InfinitePlace.mk D.what₂.embLL) {n : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ)
    (H E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin ((fc X.zs).Df1.nV Bs.μ0)) D.what₂.LL)
    (wU : D.what₂.Word → (fc X.zs).Dc.Mem)
    (eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin (X.data cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V)
    (hF : FormsTie D.what₂.embLL (W := (RowSide.sharp D).Amb μ) jA H E ((RowSide.sharp D).eOp μ))
    (hE : LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin)
    (hι : ∀ y, (RowSide.sharp D).iota μ (jA (V.mulVec y)) =
      (RowSide.sharp D).jEE (eRR (((X.data cr true).ι Bs.μ0).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec y))))
    (hNu : ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (wU u)) (eNu u)) :
    ∃ Rd : Read D X fc (twAt D.what₂.embLL Bs.v0), HEq Rd.wU wU ∧ HEq Rd.eNu eNu ∧ HEq Rd.eRR eRR ∧
      (∀ y, HEq (Rd.jV y) (jA (V.mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd cr ∧ Rd.NuTie ∧
      ((∃ L, HLatTie D.div.RR L (X.data cr true).XE eRR) → Rd.RRTie cr) ∧
      ((∀ (u : D.what₂.Word) (x : Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL)
          (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
          D.what₂.embLL ((fc X.zs).Dc.Pt (wU u) Bs.μ0 x y) =
            D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec y))) → Rd.DcPt) := by
  subst hμ
  refine ⟨⟨wU, eNu, eRR, jA.comp V.mulVecLin, hv, fun a => ?_⟩, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl,
    ?_, fun y => ?_, hNu, fun h => h, fun h => h⟩
  · rw [emb_eq D.what₂.embLL Bs.v0 a, sgAt_mk D.what₂.embLL hv]
  · exact (GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (W := (RowSide.sharp D).Amb D.what₂.mu0) jA H E _ V hF hE).symm
  · have h := hι y
    rw [sharp_iota_eq] at h
    exact h

end GlobalTheory.Mem.SJ
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_read_of_divDef3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (Sp : SPer (F.Dc (R.toCx3 F).zs)) (C : ColData (F.Dc (R.toCx3 F).zs) Sp ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → ∃ Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0), HEq Rd.wU I.wU ∧ HEq Rd.eNu I.eNu ∧ HEq Rd.eRR I.eRR ∧ (∀ y, HEq (Rd.jV y) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd F.cr ∧ Rd.NuTie ∧ (DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → Rd.RRTie F.cr) ∧ ((∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → Rd.DcPt) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk S0 p0 Sp C NuC I h
  obtain ⟨Rd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_read_of_matrix_tie D (R.toCx3 F) F.fc F.cr (I.tup A3.A.μ0) h.tup.mu0 h.tup.v0 (I.jA A3.A.μ0)
      (rH D A3.A F.P1 F.ψ1 A3.A.μ0) (rE D A3.A F.P1 F.ψ1 A3.A.μ0) (rV0 D A3.A F.P1 F.ψ1 A3.A.μ0) I.wU I.eNu I.eRR
      (h.sharp.forms A3.A.μ0) (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A n hOk.ok2 F.P1 F.ψ1 A3.A.μ0) (h.sharp.iota A3.A.μ0)
      (fun u => ⟨_, h.cols.Nu u⟩)
  exact ⟨Rd, h1, h2, h3, h4, h5, h6, h7, fun hR => h8 ⟨_, hR.sharpRR⟩, h9⟩

end GlobalTheory.Mem.SJ
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_im_ne_zero_of_totallyComplex {K : Type} [Field K] [IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  exact Complex.conj_eq_iff_im.2 (h a)

theorem lin_single_cpt {K : Type} [Field K] (σ : K →+* ℂ) {d : ℕ} {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (e : (Fin d → K) ≃ₗ[K] V) (j : V →ₛₗ[σ] W) (x : Fin d → K) :
    lin (fun k => j (e (Pi.single k 1))) (cpt σ x) = j (e x) := by
  rw [lin_apply]
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum, map_smulₛₗ, cpt]

theorem rows_eq_rows_level : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.RRTie cr → (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ ∀ F, ‖M.eR F‖ = Real.sqrt (X.nP true) * ‖F‖ := by
  intro D Bs A X fc s R cr M eV hX hT
  obtain ⟨L, hT⟩ := hT
  have hn : 0 < X.nP true := hX.pos.2.2 true
  let g := lin (fun k => D.jEE (R.eRR (Pi.single k 1)))
  have hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x) := lin_single_cpt _ R.eRR D.jEE
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩
  have key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z) := by
    intro z
    rw [← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, M.eR_eq]
    congr 2
    funext i
    by_cases h : i = k <;> simp [cpt, h]
  have hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z := by
    intro z
    funext i
    cases s <;> simp [cjv, cj]
  refine ⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key, ← hX.h2.2.2]
    exact ⟨_, rfl⟩
  · rw [← hX.h2.2.2] at he
    obtain ⟨z, rfl⟩ := he
    exact ⟨g (cjv s z), by rw [key, hcc]⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key]
    have hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _) :=
      DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))
    have hcj : Continuous (cj s) := by
      cases s
      · exact continuous_id
      · exact Complex.continuous_conj
    have hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z :=
      continuous_pi fun i => hcj.comp (continuous_apply i)
    have h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖ :=
      ((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm
    have h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖ :=
      continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    have hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
      funext i
      simp [cjv, cpt, R.twist]
    have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) := by
      simp [CxData.XE, rowXE, rowFrame, spliceFrame]
    have hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1) :=
      li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)
    have hm := majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x
    rw [lin_basis] at hm
    rw [hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K,
      ← Real.sqrt_mul hn.le]
    erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re =
      (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]
    rw [mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.Mem.SJ
end

section
noncomputable section

namespace GlobalTheory.Mem.SJ.RowB

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iC_cpt_eq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [CxData.iC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, cpt, RingHom.id_apply]

theorem theta_eq : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y))) := by
  intro D Bs A X fc s R cr M eV hF hI y
  rw [M.cF_eq, hI y, M.eR_eq, X.rowMat_base cr true hF.h2, Matrix.one_mulVec, iC_cpt_eq, hF.theta y]
  rfl

end GlobalTheory.Mem.SJ.RowB

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem seamEx_lin_cpt {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem seamEx_coords {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    ∃ c : E ≃ₗ[ℂ] (Fin n → ℂ), ∀ x, c.symm (cpt σ x) = j (e x) := by
  let g : (Fin n → K) →ₛₗ[σ] E := j.comp e.toLinearMap
  let f : (Fin n → ℂ) →ₗ[ℂ] E := lin (fun k => g (Pi.single k 1))
  have hf : ∀ x, f (cpt σ x) = j (e x) := fun x => seamEx_lin_cpt σ g x
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt σ (e.symm (b i)), by rw [hf]; simp⟩
  haveI : Module.Finite K V := Module.Finite.equiv e
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ E := Module.Basis.mk hb.1 hb.2.ge
  haveI : Module.Finite ℂ E := Module.Finite.of_basis B
  have hr : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis b, ← e.finrank_eq]
    simp
  have hinj : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).2 hsurj
  exact ⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, hf⟩

theorem seam_nonempty (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs)
    (s : Bool) (R : Read D X fc s) (cr : Crd A fc) : Nonempty (Seam R cr) := by
  choose cφ hφ using fun u => seamEx_coords D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u)
  obtain ⟨c, hc⟩ := seamEx_coords D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis
  refine ⟨{ cφ := cφ
            cF := lin (fun k => R.jV (Pi.single k 1))
            eR :=
              { toFun := fun F => X.iC cr true Bs.μ0 (cjv s (c F))
                map_add' := fun F G => ?_
                map_smul' := fun a F => ?_ }
            cφ_eq := hφ
            cF_eq := fun y => seamEx_lin_cpt _ _ y
            eR_eq := fun y => ?_ }⟩
  · rw [← map_add]
    congr 1
    funext i
    simp [cjv]
  · rw [← map_smul]
    congr 1
    funext i
    simp [cjv]
  · show X.iC cr true Bs.μ0 (cjv s (c _)) = _
    rw [← hc, LinearEquiv.apply_symm_apply]
    congr 1
    funext i
    simp [cjv, cpt, R.twist]

end GlobalTheory.Mem.SJ

end
end

section
open Formalism.BasicNotions Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem inner_eq_integral_of_ae {α : Type} [MeasurableSpace α] {m : Measure α} (f g : Lp ℂ 2 m) (f' g' : α → ℂ)
    (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') : ⟪f, g⟫_ℂ = ∫ x, star (f' x) * g' x ∂m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem eq_smul_of_eval {α A E V : Type} [MeasurableSpace α] {m : Measure α} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ (Lp ℂ 2 m)) (φ : E → V → α → ℂ) (p : V → V → ℂ)
    (hS : ∀ T T', ∃ k : ℂ, ∀ v v', ∫ x, star (φ T v x) * φ T' v' x ∂m = k * p v v')
    (v₁ v₀ : V) (hp : p v₁ v₁ = 1) (j' : E ≃ₗ[ℂ] W) (hj' : ∀ T, ((j' T : W) : Lp ℂ 2 m) =ᵐ[m] φ T v₁)
    (e : A → E) (j : A → W) (a : ℂ) (hj : ∀ F, ((j F : W) : Lp ℂ 2 m) =ᵐ[m] fun x => a * φ (e F) v₀ x) (F : A) :
    j F = (a * p v₁ v₀) • j' (e F) := by
  have hmix : ∀ T : E, ⟪j' T, j F⟫_ℂ = (a * p v₁ v₀) * ⟪j' T, j' (e F)⟫_ℂ := by
    intro T
    obtain ⟨k, hk⟩ := hS T (e F)
    have h1 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj F)
    have h2 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj' (e F))
    rw [hk, hp, mul_one] at h2
    have h3 : ∫ x, star (φ T v₁ x) * (a * φ (e F) v₀ x) ∂m = a * ∫ x, star (φ T v₁ x) * φ (e F) v₀ x ∂m := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h3, hk] at h1
    rw [Submodule.coe_inner, Submodule.coe_inner, h1, h2]
    ring
  obtain ⟨T, hT⟩ := j'.surjective (j F - (a * p v₁ v₀) • j' (e F))
  have hz : ⟪j F - (a * p v₁ v₀) • j' (e F), j F - (a * p v₁ v₀) • j' (e F)⟫_ℂ = 0 := by
    conv_lhs => enter [2]; rw [← hT]
    rw [inner_sub_right, inner_smul_right, hmix, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_conj_scalar {A W H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup H]
    [Module ℂ H] (s : W →ₗ⋆[ℂ] H) (j f : A →ₗ[ℂ] W) (hj : Function.Injective j) (β : ℂ) (h : ∀ F, j F = β • f F) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ F, s (f F) = κ • s (j F) := by
  by_cases h0 : β = 0
  · refine ⟨1, one_ne_zero, fun F => ?_⟩
    have hF : j F = 0 := by rw [h, h0, zero_smul]
    have hF0 : F = 0 := hj (hF.trans (map_zero j).symm)
    subst hF0
    simp
  · refine ⟨(starRingEnd ℂ β)⁻¹, inv_ne_zero ((map_ne_zero _).2 h0), fun F => ?_⟩
    rw [h, LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).2 h0), one_smul]

theorem sEEofTT_eq_smul_conjHH : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0))) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) → EvalTieT M μ 𝓕 E St G ι t c → ∀ (e : D.what₂.EE →ₗ[ℂ] E) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (v₀ : M.Vec) (a : ℂ), (∀ F, ((j F : EEC St G) : L2X St) =ᵐ[muX St] fun x => a * ev M v₀ (e F : MMap M) (ι.symm x * t)) → ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ F, sEEofTT M μ 𝓕 E St G ι t c (e F) = κ₀ • conjHH St G (j F) := by
  intro D S M E St G μ 𝓕 ι t c hS hT e j v₀ a hj
  have hv := hT.choose_spec.1
  have hj' := fun T => (hT.choose_spec.2.choose_spec T).1
  have hp : ∏ τ, ⟪(hT.choose τ : M.H τ), (hT.choose τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  have hkey := eq_smul_of_eval (m := muX St) (EEC St G) (fun (T : E) (v : M.Vec) x => (T : MMap M) v (ι.symm x * t))
    (fun v v' => ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) (fun T T' => hS T T.2 T' T'.2) hT.choose v₀ hp
    hT.choose_spec.2.choose hj' e j a hj
  have hs : sEEofTT M μ 𝓕 E St G ι t c
      = (conjHH St G).toLinearMap.comp hT.choose_spec.2.choose.toLinearMap := dif_pos hT
  rw [hs]
  exact exists_conj_scalar (conjHH St G).toLinearMap j.toLinearEquiv.toLinearMap
    (hT.choose_spec.2.choose.toLinearMap.comp e) j.injective _ hkey

end GlobalTheory.Mem.SJ
end

section
noncomputable section

namespace GlobalTheory.Mem.SJ.Pair

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}
  {R : Read D X fc s} {cr : Crd A fc}

theorem cpt_single {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (i : Fin n) :
    (fun k => σ ((Pi.single i 1 : Fin n → K) k)) = (Pi.single i 1 : Fin n → ℂ) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem sum_coord_jN (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.jN u (R.eNu u (Pi.single i 1)) = φ := by
  have h : ∀ i, D.jN u (R.eNu u (Pi.single i 1)) = (M.cφ u).symm (Pi.single i 1) := fun i => by
    rw [← M.cφ_eq]
    exact congrArg _ (cpt_single D.what₂.embLL i)
  simp only [h, ← map_smul, ← map_sum]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_coord_eMu (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.eMu u (D.jN u (R.eNu u (Pi.single i 1))) = D.eMu u φ := by
  simp only [← map_smul, ← map_sum]
  rw [sum_coord_jN]

theorem sum_coord_heq (M : Seam R cr) (u w : D.what₂.Word) (hw : w = u)
    (b : Fin ((fc X.zs).Dc.a (R.wU u)) → (D.mem w).A.Mram)
    (hb : ∀ i, HEq (b i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) (φ : D.what₂.Mu u) :
    HEq (∑ i, M.cφ u φ i • b i) (D.eMu u φ) := by
  subst hw
  have : b = fun i => D.eMu w (D.jN w (R.eNu w (Pi.single i 1))) := funext fun i => eq_of_heq (hb i)
  subst this
  exact heq_of_eq (sum_coord_eMu M w φ)

theorem inner_tw_of_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (x y : Tw s E) (κ₀ : ℂ) (v : E)
    (hx : Tw.out x = κ₀ • v) : ⟪x, y⟫_ℂ = cj s (starRingEnd ℂ κ₀ * ⟪v, Tw.out y⟫_ℂ) := by
  rw [Tw.inner_eq, hx, inner_smul_left]

end GlobalTheory.Mem.SJ.Pair

end
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SJ.PairMain

theorem op_ramCrd_eq {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : St.LevelSubgroupCharacter) (w u : D.what₂.Word) (hw : w = u)
    (p : PerW St hK w) (q : PerW St hK u) (hpq : HEq p q) {n : ℕ} (b : Fin n → (D.mem w).A.Mram) (c : Fin n → ℂ)
    (φ : (D.mem u).A.Mram) (hc : HEq (∑ i, c i • b i) φ) (T : Cu St u hK)
    (hT : colDictL St q.Tr hK T = ((φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    (((p.op (ramCrd b c) : HHX St)) : L2X St) = PuFun St u hK q.Dt T := by
  subst hw
  obtain rfl := eq_of_heq hpq
  obtain rfl := eq_of_heq hc
  have h1 : ramCrd b c = Submodule.inclusion inf_le_left (∑ i, c i • b i) := by
    show Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ b c) = _
    rw [Fintype.linearCombination_apply]
    rfl
  have h2 : (colDict St p.Tr hK p.hI p.hB).symm (Submodule.inclusion inf_le_left (∑ i, c i • b i)) = T := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [colDict_apply, hT]
    rfl
  rw [h1]
  simp only [PerW.op, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2]
  rfl

theorem pair_step : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  intro D Bs A X fc s R cr M St G hK pw wdD bR hw hSp hb
  generalize (fc X.zs).Sp = SP at hSp ⊢
  subst hSp
  intro sEE sEEc hE j κ₀ hκ₀ hout u
  obtain rfl := eq_of_heq hE
  refine ⟨starRingEnd ℂ κ₀, (map_ne_zero _).2 hκ₀, ?_⟩
  intro F φ T hT
  refine (Pair.inner_tw_of_smul (E := HHX St) s (sEE (M.eR F) : Tw s (HHX St))
    ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ)) : Tw s (HHX St)) κ₀
    ((conjHH St G (j F) : HHX St)) (hout F)).trans ?_
  congr 2
  have hcc : cjVec s _ (cjv s (M.cφ u φ)) = M.cφ u φ := funext fun i => cj_cj s _
  have hP : Tw.out (s := s) ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ))) =
      (pw (wdD (R.wU u))).op (ramCrd (bR (R.wU u)) (M.cφ u φ)) :=
    (spOf_Pu s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR (R.wU u) (cjv s (M.cφ u φ))).trans (by rw [hcc])
  have key := op_ramCrd_eq St hK _ u (hw u) _ _ (congr_arg_heq pw (hw u)) (bR (R.wU u)) (M.cφ u φ) _
    (Pair.sum_coord_heq M u _ (hw u) (bR (R.wU u)) (hb u) φ) T hT
  rw [Submodule.coe_inner]
  exact congrArg _ ((congrArg Subtype.val hP).trans key)

end GlobalTheory.Mem.SJ.PairMain
end
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_operator_spectrum : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  first | exact @GlobalTheory.Mem.SJ.PairMain.pair_step | exact GlobalTheory.Mem.SJ.PairMain.pair_step | (intros; apply GlobalTheory.Mem.SJ.PairMain.pair_step <;> assumption)
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

theorem kernelJoin_onV0 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → SchurAll D → (D.sp.Y 0).SigOK → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (C : ColData (F.Dc (R.toCx3 F).zs) (F.Sp (R.toCx3 F).zs) ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → (∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → ∃ (Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : Seam Rd F.cr), HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (R.toCx3 F).zs) ∧ M.ColNorm ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧ ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (I.wU u) = u) → F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1))))) → ∀ (t : GA D (D.sp.Y 0)) (c : ℝ), EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → κS ≠ 0 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c ⟨R.HE.e (Tw.out x), hx⟩)) → ∀ (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))) → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (R.MY 0).Vec) (a : ℂ), (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St] fun g => a * ev (R.MY 0) v₀ (R.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK), colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR x), (F.fc (R.toCx3 F).zs).Sp.Pu (Rd.wU u) (cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hCW hPR hSchur hSig S0 p0 C NuC I hDef hRows hPer
  obtain ⟨Rd, hwU, heNu, heRR, hjV, hV0, hIota, hNu, hRR, hDc⟩ :=
    exists_read_of_divDef3 D G Pl0 I0 T A3 Ks R F n hOk S0 p0 _ C NuC I hDef
  obtain ⟨M⟩ := seam_nonempty D _ _ _ _ _ Rd F.cr
  have hCx := cxFacts_of_prims D G Pl0 I0 T A3 Ks R F n hOk hSep hCW hPR
  have hRow := rows_eq_rows_level D _ _ _ _ _ Rd F.cr M _ hCx (hRR hRows)
  have hCV := chainTie_and_v0Onto D _ _ _ _ _ Rd F.cr M
  refine ⟨Rd, M, hwU, hCV.1 (hDc hPer), hCV.2 hV0,
    ⟨hRow.1, hRow.2.1, ⟨_, Real.sqrt_pos.2 (hCx.pos.2.2 true), hRow.2.2⟩, 1, one_ne_zero, fun y => by
      rw [one_smul]; exact RowB.theta_eq D _ _ _ _ _ Rd F.cr M _ hCx hIota y⟩,
    colNorm_of_nuTie D _ _ _ _ _ Rd F.cr M hNu, thetaMap_referenceTuple_goodPart_onto_rows D _ _ _ _ _ Rd F.cr _ hCx hIota hV0, ?_⟩
  intro St h Gd hK pw wdD bR hwd hSp hbR t c hEv sEE sEEc κS hS hκS hsEEc eE heE j v₀ a hj u
  have hwUe : Rd.wU = I.wU := eq_of_heq hwU
  have heRRe : Rd.eRR = I.eRR := eq_of_heq heRR
  have hME : ∀ x, M.eR x = Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H (eE x) := by
    have hsp : Submodule.span ℂ (Set.range fun i => D.jEE (D.div.RR.b i)) = ⊤ := D.jEE_basis.2
    have hext := LinearMap.ext_on_range hsp (f := M.eR)
      (g := (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H).comp eE) (fun i => ?_)
    · exact fun x => LinearMap.congr_fun hext x
    · obtain ⟨y, hy⟩ := Rd.eRR.surjective (D.div.RR.b i)
      have h1 := heE y
      rw [← heRRe] at h1
      rw [← hy, M.eR_eq y]
      exact (congrArg (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H) h1).symm
  have hmem : ∀ x, R.HE.e (eE x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := fun x => by
    have h1 := hRow.1 x
    rw [hME x] at h1
    exact h1
  let e : D.what₂.EE →ₗ[ℂ] R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
    LinearMap.codRestrict _ (R.HE.e ∘ₗ eE) hmem
  have hSch := SchurMove.schur_iotaX D _ (R.MY 0) (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St h R.θ _ _ t
    hSchur hSig hCW.base.models.inf (goodPart_le _ _ _ _ _)
  obtain ⟨κ₀, hκ₀, hκe⟩ := sEEofTT_eq_smul_conjHH D _ (R.MY 0) _ St Gd R.ν0 R.fd0
    (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c hSch hEv e j v₀ a hj
  have h3 : ∀ z : HHX St, (Tw.mk (twAt D.what₂.embLL A3.A.v0) z).out = z := fun z => rfl
  have hkey : ∀ x, (sEEc (M.eR x)).out = (κS * κ₀) • conjHH St Gd (j x) := fun x => by
    have hx : R.HE.e (Tw.out (M.eR x)) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
      (congrArg (fun z => R.HE.e (Tw.out z) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) (hME x)).mpr (hmem x)
    have h2 : (⟨R.HE.e (Tw.out (M.eR x)), hx⟩ : R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) = e x :=
      Subtype.ext (congrArg (fun z => R.HE.e (Tw.out z)) (hME x))
    exact (congrArg Tw.out (hsEEc (M.eR x) hx)).trans (smul_apply_eq_of_eq _ h2 κS κ₀ (hκe x))
  have hwd' : ∀ u, wdD (Rd.wU u) = u := fun u => (congrArg wdD (congrFun hwUe u)).trans (hwd u)
  have hbR' := heq_of_reindex _ bR (fun u v => D.eMu u (D.jN u v)) Rd.wU I.wU Rd.eNu I.eNu hwUe heNu hbR
  exact GlobalTheory.T.good_operator_spectrum D _ _ _ _ _ Rd F.cr M St Gd hK pw wdD bR hwd' hSp hbR' sEE sEEc hS j (κS * κ₀)
    (mul_ne_zero hκS hκ₀) hkey u

end GlobalTheory.Mem.SJ.KernelJoin
end

section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_join_on_V0_three : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → SchurAll D → (D.sp.Y 0).SigOK → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (C : ColData (F.Dc (R.toCx3 F).zs) (F.Sp (R.toCx3 F).zs) ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → (∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → ∃ (Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : Seam Rd F.cr), HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (R.toCx3 F).zs) ∧ M.ColNorm ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧ ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (I.wU u) = u) → F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1))))) → ∀ (t : GA D (D.sp.Y 0)) (c : ℝ), EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → κS ≠ 0 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c ⟨R.HE.e (Tw.out x), hx⟩)) → ∀ (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))) → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (R.MY 0).Vec) (a : ℂ), (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St] fun g => a * ev (R.MY 0) v₀ (R.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK), colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR x), (F.fc (R.toCx3 F).zs).Sp.Pu (Rd.wU u) (cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  first | exact @GlobalTheory.Mem.SJ.KernelJoin.kernelJoin_onV0 | exact GlobalTheory.Mem.SJ.KernelJoin.kernelJoin_onV0 | (intros; apply GlobalTheory.Mem.SJ.KernelJoin.kernelJoin_onV0 <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.JTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def JoinPin (Q : RealT R P Dcf Spf Zscf S Ks) : Prop :=
  ∃ eE : D.what₂.EE →ₗ[ℂ] Q.Rl.HE.H,
    (∀ y y', HEq y y' → eE (D.jEE (P.I.eRR y)) =
      Tw.out (s := Formalism.L2.SG.JoinSI.twQ P) (E := Q.Rl.HE.H)
        ((Formalism.L2.SG.JoinSI.cx Q).iC Q.F.cr true P.A3.A.μ0 (cpt P.A3.A.v0.embedding y'))) ∧
    ∀ hF : Formalism.L2.SG.PackageTie2.FinX S.Y, GlobalTheory.Mem.SRe.RowJ Q.Rl.toRealDat eE S.X S.inst S.G Q.tS (Formalism.L2.SG.JoinSI.jOf S hF)

theorem core {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ) (hOk : A3.fam3.Ok3 n) (hSep : A3.fam3.TypesSep3)
    (hCh : Rl.WeakCharacterisation F) (hPrim : PrimRows3 Rl F) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK)
    (Zs : DefSub A3.fam3.amb3) (hzs : (Rl.toCx3 F).zs = Zs)
    (S0 : IndefData (A3.side3 F.P0 F.ψ0 Zs)) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs))
    (hs1 : HEq ((Rl.toCx3 F).data F.cr true) S1)
    (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (hdc : F.Dc Zs = Dc) (Sp : SPer Dc) (hsp : HEq (F.Sp Zs) Sp)
    (p0 : BaseLevelRowSide D) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 Dc)
    (hDef : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hDivR : DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hPt : ∀ (u : D.what₂.Word) (x : Fin (Dc.a (I.wU u)) → D.what₂.LL)
      (y : Fin ((A3.side3 F.P1 F.ψ1 Zs).nV A3.A.μ0) → D.what₂.LL),
      D.what₂.embLL (Dc.Pt (I.wU u) A3.A.μ0 x y) =
        D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y)))
    (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter)
    (pw : ∀ u, PerW St hK u) (wdD : Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hwdD : ∀ u, wdD (I.wU u) = u)
    (hSp : HEq Sp (spOf (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD (fun x => pw (wdD x)) bR))
    (hbR : ∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1)))))
    (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hEv : EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd
      (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c)
    (sEE : (Rl.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (Rl.toCx3 F).zs).Sp.HH)
    (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ)
    (hsE : HEq sEE sEEc) (hκ : κS ≠ 0)
    (hsee : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H)
      (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true))),
      sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0
        (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c
        ⟨Rl.HE.e (Tw.out x), hx⟩))
    (eE : D.what₂.EE →ₗ[ℂ] Rl.HE.H)
    (hRead : ∀ y y', HEq y y' → eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := Rl.HE.H)
      ((Rl.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y'))) :
    ∃ (Rd : GlobalTheory.Mem.SJ.Read D (Rl.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : GlobalTheory.Mem.SJ.Seam Rd F.cr),
      HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (Rl.toCx3 F).zs) ∧ M.ColNorm ∧
      (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧
      ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (Rl.MY 0).Vec) (a : ℂ),
        (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St]
          fun g => a * ev (Rl.MY 0) v₀ (Rl.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) →
        ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK),
          colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
          ⟪sEE (M.eR x), (F.fc (Rl.toCx3 F).zs).Sp.Pu (Rd.wU u)
              (GlobalTheory.Mem.SJ.cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ =
            cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  subst hzs
  subst hdc
  obtain rfl := eq_of_heq hs1
  obtain rfl := eq_of_heq hsp
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    GlobalTheory.T.kernel_join_on_V0_three D G Pl0 I0 T A3 Ks Rl F n hOk hSep hCh hPrim hSchur hSig S0 p0 C NuC I hDef hDivR hPt
  exact ⟨Rd, M, hw, h1, h2, h3, h4, hon, fun j v₀ a hj => hT St h Gd hK pw wdD bR hwdD (eq_of_heq hSp) hbR t c hEv
    sEE sEEc κS hsE hκ hsee eE (fun y => hRead y y HEq.rfl) j v₀ a hj⟩

theorem bR_heq (Q : RealT R P Dcf Spf Zscf S Ks) (hPin : RealPins Q) (u : D.what₂.Word) (i : Fin (P.Dc.a (P.I.wU u))) :
    HEq (Q.bR (P.I.wU u) i) (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
  refine HEq.trans (heq_of_eq (hPin.bR_read (P.I.wU u) i)) ?_
  have key : ∀ (w : D.what₂.Word) (hw : w = u) (hc : P.Dc.a (P.I.wU u) = P.Dc.a (P.I.wU w)),
      HEq (D.eMu w (D.jN w (P.I.eNu w (Pi.single (Fin.cast hc i) 1))))
        (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
    intro w hw hc
    subst hw
    rfl
  exact key _ (Q.wdD_wU u) _

end GlobalTheory.Mem.JTop
end
end
