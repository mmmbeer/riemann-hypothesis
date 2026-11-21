import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInfOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpanGoodBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RationalTransitionKernel
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DownUpLambdaOperators

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem exists_ix_of_mem_eigAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m), A3.fam3.Ok3 s → ∀ (x : (A3.rowI A3.A.μ0).OpIx → K) (f : (A3.A.fam.R A3.A.μ0).S.Forms), f ≠ 0 → f ∈ (A3.A.fam.R A3.A.μ0).ZHg A3.A.X → f ∈ Formalism.L2.Col.eigAt (A3.rowI A3.A.μ0).opAll x → ∃ p : A3.fam3.base3.Ix, (A3.rowI A3.A.μ0).HasRes3 p.1 x := by
  classical
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 h x f hf0 hfZ hfx
  have hB : (A3.A.fam.R A3.A.μ0).Ok s := h.ok2.what₂ A3.A.μ0
  have hD : (A3.rowI A3.A.μ0).Ok3 := h.what₂ A3.A.μ0
  have hs := (A3.rowI A3.A.μ0).splitOver_opAll hB hD

  have hfZH : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
    le_eigSum_elim (A3.A.fam.R A3.A.μ0).op (A3.rowI A3.A.μ0).opI hD.comm hs _ (by exact hfZ.1)
  have hHB : Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => x (Sum.inl i)) := by
    by_contra hn
    have hf2 : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
      Formalism.L2.Col.eigAt_le_eigSum (C := fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i))) hn hfx
    exact hf0 (Submodule.disjoint_def.1 (Formalism.L2.Col.disjoint_eigSum hD.comm fun y h1 h2 => h2 h1) f hfZH hf2)
  choose c hc using hHB
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg ((A3.A.fam.R A3.A.μ0).pl P) = c P := by
    intro P
    have hP : ∃ P', (A3.A.fam.R A3.A.μ0).pl P' = (A3.A.fam.R A3.A.μ0).pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [hB.pl_inj hP.choose_spec]
  let e : I0 × Ty → K := fun k0 => if hP : ∃ P, (A3.rowI A3.A.μ0).plI P = k0.1 then x (Sum.inr (hP.choose, k0.2)) else 0
  have he : ∀ (P : (A3.rowI A3.A.μ0).PlI) (y : Ty), e ((A3.rowI A3.A.μ0).plI P, y) = x (Sum.inr (P, y)) := by
    intro P y
    have hP : ∃ P', (A3.rowI A3.A.μ0).plI P' = (A3.rowI A3.A.μ0).plI P := ⟨P, rfl⟩
    simp only [e, dif_pos hP]
    rw [hD.plI_inj hP.choose_spec]
  have hres : (A3.rowI A3.A.μ0).HasRes3 (Sg, e) x := by
    refine ⟨fun P => ?_, fun k => (he k.1 k.2).symm⟩
    show _ = Sg ((A3.A.fam.R A3.A.μ0).pl P) * (A3.A.fam.R A3.A.μ0).blockProd P
    rw [hSg P, mul_comm]
    exact hc P

  set a0 := goodAt A3.A.fam.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a0 * a0 = a0 :=
    (good_at_spec K A3.A.fam.v0 h.ok2.conj G A3.A.fam.X h.ok2.irr (⊥ : Subgroup G) 1).idem
  have hfix : (A3.A.fam.R A3.A.μ0).S.gaOp (A3.A.fam.R A3.A.μ0).r a0 f = f := by
    obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hfZ.2
    have hid' : a0 * goodAt A3.A.X (⊥ : Subgroup G) 1 = goodAt A3.A.X (⊥ : Subgroup G) 1 := hidem
    rw [← hg, ← BlockDat.gaOp_mul, hid']
  obtain ⟨u0, hu0⟩ := (A3.A.fam.R A3.A.μ0).exists_vE_of_fix (Lvl.full A3.A.fam.X) hfix
  have hmem : (Sg, e) ∈ (A3.rowI A3.A.μ0).ixFin3 A3.A.fam.X := by
    rw [(A3.rowI A3.A.μ0).mem_ixFin3 hD.comm]
    refine ⟨fun P0 hP0 => ?_, fun P0 hP0 y => ?_, ?_⟩
    · have hP : ¬ ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show Sg P0 = 1
      simp only [Sg, dif_neg hP]
    · have hP : ¬ ∃ P, (A3.rowI A3.A.μ0).plI P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show e (P0, y) = 0
      simp only [e, dif_neg hP]
    · intro hbot
      have hu0mem : u0 ∈ (A3.A.fam.R A3.A.μ0).inV0 (Lvl.full A3.A.fam.X) ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum (Sg, e)) := by
        rw [BlockDat.mem_goodPart_iff, hu0]
        exact Formalism.L2.Col.eigAt_le_eigSum (C := (A3.rowI A3.A.μ0).HasRes3 (Sg, e)) hres hfx
      rw [hbot, Submodule.mem_bot] at hu0mem
      apply hf0
      rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]
  exact ⟨⟨(Sg, e), hmem⟩, hres⟩

end GlobalTheory.Div
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.UpSystem

theorem flatMap_cast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = List.map (fun a : ℕ => (a : ℤ)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem labIn_eq (n : ℕ) (s : List ℕ) : Formalism.IndefR.Links.labIn n s =
    List.map (fun a : ℕ => (a : ℤ)) s ++ List.replicate (n - 2 * s.length) 0 ++ List.map (fun a : ℕ => -(a : ℤ)) s.reverse := by
  unfold Formalism.IndefR.Links.labIn
  simp only [List.bind_eq_flatMap, List.pure_def, flatMap_cast, List.map_map]
  rfl

theorem labIn_pairwise {n : ℕ} {s : List ℕ} (h : Formalism.L2.Col.InertTypeOk n s) :
    (Formalism.IndefR.Links.labIn n s).Pairwise (fun a b : ℤ => b ≤ a) := by
  obtain ⟨h1, -, -⟩ := h
  rw [labIn_eq]
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact List.pairwise_map.2 (h1.imp fun h => by exact_mod_cast h)
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hb]
    exact Int.natCast_nonneg x
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact h1.imp fun h => by omega
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      omega
    · rw [List.eq_of_mem_replicate ha]
      omega

end GlobalTheory.UpSystem

namespace GlobalTheory.UpSystem

set_option maxHeartbeats 1000000 in

theorem up_sys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hOk hW hEx hS hTS hInert
  have h1 := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW
  have hC := h1.1 hEx
  have hSF := h1.2.1
  have hIn := h1.2.2.1
  have hEE := h1.2.2.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt A3.A.μ0)).J) (χ := (levEnv _ R.βX (R.datXt A3.A.μ0)).χ) (R.B.R A3.A.μ0).pres
    (R.HX A3.A.μ0) (hC.models.HX A3.A.μ0) (hC.models.jX A3.A.μ0)
  choose Tc hTc using fun i => GlobalTheory.AdjBlock.exists_cx hf.1 hf.2.1 ((A3.rowI A3.A.μ0).opAll i)
  refine ⟨Tc, fun i f => (hTc i f).symm, fun c => ?_⟩
  have hext : ∀ i (U : Module.End ℂ (R.HX A3.A.μ0).H),
      (∀ f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = U (R.jX A3.A.μ0 f)) → Tc i = U :=
    fun i U hU => GlobalTheory.AdjBlock.ext_of_span hf.2.1 fun f => (hTc i f).trans (hU f)
  have hzero : ∀ i, (A3.rowI A3.A.μ0).opAll i = 0 → Tc i = 0 := by
    intro i h0
    refine hext i 0 (fun f => ?_)
    have e1 : (A3.rowI A3.A.μ0).opAll i f = 0 := by rw [h0]; rfl
    exact (congrArg (R.jX A3.A.μ0) e1).trans ((map_zero _).trans (LinearMap.zero_apply _).symm)
  have hsys : ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 P cX c0 → ∀ i,
      Tc i = hX P cX → ∃ a : ℂ, ∀ w ∈ R.EEc c,
        Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P hP cX c0 hm i hi
    have h10 := (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 P hP cX c0 hm hX hXo).2 c
    refine ⟨_, fun w hw => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) hi).trans
      (h10 w ((hEE c).symm ▸ hw))⟩
  have hev0 : ∀ i, Tc i = 0 → ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i h0 =>
    ⟨0, fun w _ => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) h0).trans
      ((LinearMap.zero_apply _).trans (zero_smul ℂ _).symm)⟩
  have key : ∀ i, ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    rintro (⟨P, k⟩ | ⟨Q, y⟩)
    · by_cases hk : k ≤ D.sp.X'.rank
      · have hgood := ((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P.1 P.2).1
        have h99 := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 (P : A3.A.ok A3.A.μ0)
        have hso := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo
          (P : A3.A.ok A3.A.μ0) k hk
        exact hsys _ hgood _ _ (h99.choose_spec.1 k hk) _ (hext _ _ hso)
      · exact hev0 _ (hzero _ ((hC.fam.degR A3.A.μ0 P).2 k (not_le.1 hk)))
    · refine Or.elim (hInert.1 A3.A.μ0 ((Q : A3.okI A3.A.μ0), y)) (fun h0 => ?_) (fun hy => ?_)
      · exact hev0 (Sum.inr (Q, y)) (hzero (Sum.inr (Q, y)) h0)
      · have hgc := hIn A3.A.μ0 Q.1 Q.2
        have tie := (hW.inert.hR A3.A.μ0).some
        have hy'' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hy.choose := R.B.rankR ▸ hy.choose_spec.1
        have h78 := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hC.lev hC.fam hC.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
          (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI A3.A.μ0)
          (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
          (fun i hi => ⟨(hIn A3.A.μ0 i.1.1 i.1.2).1, (hIn A3.A.μ0 i.1.1 i.1.2).2, labIn_pairwise hi⟩) tie (Q, hy.choose) hy''
        have hm := (hTS _ hgc.1 hgc.2).1.1 (Finsupp.single (Formalism.IndefR.Links.labIn D.sp.X'.rank hy.choose) 1)
        refine hsys _ hgc.1 _ _ hm.choose_spec (Sum.inr (Q, y)) (hext _ _ fun f => ?_)
        exact (congrArg (R.jX A3.A.μ0) (LinearMap.congr_fun hy.choose_spec.2 f)).trans (h78.2.2.2 hX hXo f)
  exact ⟨fun i => (key i).choose, fun w hw i => (key i).choose_spec w hw⟩

end GlobalTheory.UpSystem
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  atlas_forward_decl GlobalTheory.UpSystem.up_sys
end

section
open NumberField
open scoped Matrix InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.EquivariantEuclideanComplex

open Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel

section Lin

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)

theorem cpt_single {n : ℕ} (k : Fin n) : cpt v.embedding (Pi.single k (1 : K)) = Pi.single k 1 := by
  funext i
  by_cases hi : i = k <;> simp [cpt, hi]

variable {E : Type} [AddCommGroup E] [Module ℂ E]

theorem ext_cpt {n : ℕ} {f g : (Fin n → ℂ) →ₗ[ℂ] E}
    (h : ∀ x : Fin n → K, f (cpt v.embedding x) = g (cpt v.embedding x)) : f = g := by
  rw [← lin_basis f, ← lin_basis g]
  congr 1
  funext i
  rw [← cpt_single v i, h]

def RatRel {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (g : (Fin n → ℂ) →ₗ[ℂ] E) : Prop :=
  ∃ Y : Matrix (Fin D) (Fin n) K, Function.Bijective Y.mulVec ∧ g = f ∘ₗ cx v Y

end Lin

section Dict

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J}

def IsCoord {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) (Zs : DefSub F.amb)
    (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ t, Function.Injective (cr.toR Zs b t) ∧
    LinearMap.range (cr.toR Zs b t) = LinearMap.range ((F.R t).toF (F.lvl P ψ) (Zs.Z t))

variable (X : CxData F.amb) {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool)
  (P : Subgroup G) (ψ : P →* Kˣ)

theorem orth_span {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {S : Set A} {f : A}
    (hf : ∀ p ∈ S, ⟪p, f⟫_ℂ = 0) : ∀ p ∈ Submodule.span ℂ S, ⟪p, f⟫_ℂ = 0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact hf x hx
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

def EquivariantRat (ρ : Representation ℂ G X.EE) : Prop :=
  ∀ (t : T) (g : G), ∀ x ∈ (F.R t).goodF F.X, X.Θ t (X.jR t ((F.R t).r g x)) = ρ g (X.Θ t (X.jR t x))

end Dict

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)


end Concrete

section Onto

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)
  {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE)

def fr (t : T) : Matrix (Fin (F.R t).S.dim) (Fin (F.R t).S.dim) ℂ := frameOf ((F.R t).S.H.map F.v0.embedding)

def toEuc (t : T) : (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (F.R t).S.dim) :=
  (WithLp.linearEquiv 2 ℂ (Fin (F.R t).S.dim → ℂ)).symm.toLinearMap ∘ₗ (fr F t)⁻¹.mulVecLin

def ofEuc (t : T) : EuclideanSpace ℂ (Fin (F.R t).S.dim) →ₗ[ℂ] (Fin (F.R t).S.dim → ℂ) :=
  (fr F t).mulVecLin ∘ₗ (WithLp.linearEquiv 2 ℂ (Fin (F.R t).S.dim → ℂ)).toLinearMap

def cxOf : CxData F.amb where
  FC t := EuclideanSpace ℂ (Fin (F.R t).S.dim)
  jR t := (toEuc F t).comp ((cptL F.v0.embedding _).comp
    ((F.R t).S.basis.equivFun : (F.R t).S.Forms →ₗ[K] (Fin (F.R t).S.dim → K)))
  EE := EE
  Θ t := Θ t ∘ₗ ofEuc F t
  EEp _ := ⊤
  EEl _ := ⊤
  FLC _ _ := EuclideanSpace ℂ (Fin 0)
  jL _ _ := 0
  W _ := EuclideanSpace ℂ (Fin 0)
  θ' _ _ := 0
  Wp _ _ := ⊤
  dW _ _ := 0
  WC _ _ _ := EuclideanSpace ℂ (Fin 0)
  bW _ _ _ _ := 0
  eW _ _ := 0
  M _ _ := ⊤
  nP _ := 1
  μ _ := F.μ0
  Tw := ∅
  κ _ := 1
  lam _ _ _ _ := 1
  err0 _ _ := 0

variable {F} {s : ℕ} (hF : F.Ok s)

include hF

end Onto

example {K : Type} [Field K] (σ : K →+* ℂ) :
    IsRat σ (relMat (0 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) LinearMap.id) := by
  intro i k
  refine ⟨0, ?_⟩
  have h : ¬ ∃ y, (0 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) y = Pi.single k 1 := by
    rintro ⟨y, hy⟩
    simpa using congrFun hy k
  simp only [relMat, Matrix.of_apply, LinearMap.id_apply, solve, dif_neg h, map_zero, Pi.zero_apply]

end GlobalTheory.EquivariantEuclideanComplex
end
end

section
noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneFormTest

section Abstract

variable {K : Type} [Field K] {σ : K →+* ℂ} {E : Type} [AddCommGroup E] [Module ℂ E]
  {V : Type} [AddCommGroup V] [Module K V]

theorem exists_coord {I : Type} (ψ : I → E →ₗ[ℂ] ℂ) (ι : V →ₛₗ[σ] E) (h : ∀ x a, ∃ z : K, σ z = ψ a (ι x)) :
    ∃ f : V →ₗ[K] (I → K), ∀ x a, σ (f x a) = ψ a (ι x) := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => funext fun a => σ.injective ?_⟩, fun c x => funext fun a => σ.injective ?_⟩, hf⟩
  · rw [Pi.add_apply, map_add, hf, hf, hf, map_add, map_add]
  · simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hf, map_smulₛₗ]



theorem exists_orth [FiniteDimensional K V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : V →ₛₗ[σ] H)
    (hj : Function.Injective j) (hr : ∀ x y, ∃ z : K, σ z = ⟪j x, j y⟫_ℂ) (U : Submodule K V) (x : V) :
    ∃ k ∈ U, ∀ k' ∈ U, ⟪j k', j (x - k)⟫_ℂ = 0 := by
  let b := Module.finBasis K U
  obtain ⟨f, hf⟩ := exists_coord (fun i => innerₛₗ ℂ (j (b i : V))) j fun y i => hr _ y
  have horth : ∀ y, f y = 0 → ∀ k' ∈ U, ⟪j k', j y⟫_ℂ = 0 := by
    intro y hy k' hk'
    have e : k' = ∑ i, b.repr ⟨k', hk'⟩ i • (b i : V) := by
      have := congrArg U.subtype (b.sum_repr ⟨k', hk'⟩)
      rw [map_sum] at this
      exact this.symm
    rw [e, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : ⟪j (b i : V), j y⟫_ℂ = 0 := by
      have := hf y i
      rw [hy, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [map_smulₛₗ, inner_smul_left, h0, mul_zero]
  have hinj : Function.Injective (f ∘ₗ U.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have := horth u hu u u.2
    rw [inner_self_eq_zero, ← map_zero j] at this
    exact Subtype.ext (hj this)
  have hsurj : Function.Surjective (f ∘ₗ U.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨k, hk⟩ := hsurj (f x)
  exact ⟨k, k.2, horth _ (by rw [map_sub, ← hk]; exact sub_self _)⟩

end Abstract

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K) {E : Type} [AddCommGroup E] [Module ℂ E]


end Coord

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J} (X : CxData F.amb)

structure FormsTie : Prop where

  inner_eq : ∀ t (x y : (F.R t).S.Forms),
    ⟪X.jR t x, X.jR t y⟫_ℂ = F.v0.embedding ((F.R t).S.csum (x : (F.R t).S.Cl → (F.R t).S.V) (y : (F.R t).S.Cl → (F.R t).S.V))

  inj : ∀ t, Function.Injective (X.jR t)

  span : ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

def ThroughGood : Prop :=
  ∀ t (x : (F.R t).S.Forms), X.Θ t (X.jR t ((F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) x)) = X.Θ t (X.jR t x)

omit X in
theorem csum_gaOp_good (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hB : B.Ok s)
    {Y : Finset (G → K)} (hY : ∀ χ ∈ Y, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (x y : B.S.Forms) :
    B.S.csum (B.S.gaOp B.r (goodAt Y P ψ) x : B.S.Cl → B.S.V) (y : B.S.Cl → B.S.V) =
      B.S.csum (x : B.S.Cl → B.S.V) (B.S.gaOp B.r (goodAt Y P ψ) y : B.S.Cl → B.S.V) := by
  have hp := good_at_spec K v0 hv0 G Y hY P ψ
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt Y P ψ)
  rw [hp.selfAdj] at hadj
  have e : ∀ a b : B.S.Forms, B.S.csum (a : B.S.Cl → B.S.V) (b : B.S.Cl → B.S.V) =
      hform B.S.H (B.S.basis.equivFun a) (B.S.basis.equivFun b) := fun a b => by
    have := B.S.isClassSum (B.S.basis.equivFun a) (B.S.basis.equivFun b)
    rw [CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  rw [e, e, ← CSD.gaMat_mulVec_equivFun, ← CSD.gaMat_mulVec_equivFun, RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hadj]

variable {X}



end Family

end GlobalTheory.OneFormTest
end
end

section
noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem tw_span_top (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {I : Type} (v : I → E)
    (h : Submodule.span ℂ (Set.range v) = ⊤) : Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : Tw.out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  have key : ∀ y ∈ Submodule.span ℂ (Set.range v),
      Tw.mkL s E y ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact key _ hx

theorem tw_map_surjective (s : Bool) {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] {f : E →ₗ[ℂ] E'} (h : Function.Surjective f) : Function.Surjective (Tw.map s f) := h

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]
    rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]


theorem surjective_of_scalar {H E : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E] (f : H →ₗ[ℂ] E)
    (g : E →ₗ[ℂ] H) {I : Type} (p : I → Submodule ℂ E) (hp : ⨆ c, p c = ⊤)
    (h : ∀ c, ∃ l : ℝ, 0 < l ∧ ∀ x ∈ p c, (f ∘ₗ g) x = (l : ℂ) • x) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hp, iSup_le_iff]
  intro c x hx
  obtain ⟨l, hl, h⟩ := h c
  refine ⟨(l : ℂ)⁻¹ • g x, ?_⟩
  have h1 : f (g x) = (l : ℂ) • x := h x hx
  rw [map_smul, h1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hl.ne'), one_smul]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

theorem formsTie (hH : R.models_HX) (hj : R.models_jX) : FormsTie (F := A.fam) (R.toCx F) where
  inner_eq t x y := ((congrArg (cj (twAt D.what₂.embLL A.v0)) ((model_jX R hH hj t).1 x y)).trans (R.emb0 _).symm :)
  inj t := (model_jX R hH hj t).2.1
  span t := tw_span_top (twAt D.what₂.embLL A.v0) (R.jX t) (model_jX R hH hj t).2.2





def PartsSpan : Prop := ⨆ c, GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R c = ⊤

theorem th_surjective (hB : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Concl R) (hS : PartsSpan R) (t : T) : Function.Surjective (R.Th t) :=
  surjective_of_scalar (R.Th t) (LinearMap.adjoint (R.Th t)) (GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R) hS (hB.scalar_pos t)

theorem theta_surjective (hon : ∀ t, Function.Surjective (R.Th t)) (t : T) : Function.Surjective ((R.toCx F).Θ t) :=
  tw_map_surjective (twAt D.what₂.embLL A.v0) (hon t)



end Concrete

end GlobalTheory.OneFormTest
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Div

theorem span_range_comp_basis {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) :
    Submodule.span ℂ (Set.range fun k => j (b k)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨b k, rfl⟩)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V)
    (opC : I → Module.End ℂ W) (Z : Submodule K V) (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hcomm : ∀ i v, j (op i v) = opC i (j v))
    (hpc : Formalism.L2.Col.PairComm op) (hso : Formalism.L2.Col.SplitOver op) (x : I → ℂ) (u : W)
    (hu : ∀ i, opC i u = x i • u) (hu0 : u ≠ 0) (huZ : u ∈ Submodule.span ℂ (j '' (Z : Set V))) :
    ∃ s : I → K, x = (fun i => σ (s i)) ∧
      Formalism.L2.Col.eigAt opC x = Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) ∧
      ∃ f, f ≠ 0 ∧ f ∈ Z ∧ f ∈ Formalism.L2.Col.eigAt op s := by
  have hsp' : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ := (span_range_comp_basis σ j b).trans hsp
  have key := GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp' hcomm
  have hmem : u ∈ Formalism.L2.Col.eigAt opC x := Formalism.L2.Col.mem_eigAt_of_forall_apply hu
  have hocc : Formalism.L2.Col.Occurs opC x := fun hbot => hu0 ((Submodule.eq_bot_iff _).1 hbot u hmem)
  obtain ⟨s, _, rfl⟩ := key.2.2 hpc hso x hocc
  refine ⟨s, rfl, (key.1 s).symm, ?_⟩
  have hin : u ∈ Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) := by
    rw [← GlobalTheory.span_image_inf_of_linearIndependent σ j b hli]
    exact ⟨huZ, (key.1 s) ▸ hmem⟩
  by_contra hcon
  push_neg at hcon
  apply hu0
  have hle : Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · subst hy0; simp
    · exact absurd hy.2 (hcon y hy0 hy.1)
  exact (Submodule.mem_bot ℂ).1 (hle hin)

theorem map_le_span_image {K V W H : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (Θ : H →ₗ[ℂ] W) (E : Submodule ℂ H)
    (A B : Submodule K V) (h : ∀ v ∈ E, Θ v ∈ Submodule.span ℂ (j '' (A : Set V))) (hAB : A ≤ B) :
    E.map Θ ≤ Submodule.span ℂ (j '' (B : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  exact Submodule.span_mono (Set.image_mono hAB) (h v hv)

set_option maxHeartbeats 400000 in

theorem carries_of_eEc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSch hTw hHk hPG hIx c hc
  obtain ⟨Tc, hTc, hx⟩ := GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  by_cases h0 : ∀ w ∈ R.EEc c, LinearMap.adjoint (R.Th A3.A.μ0) w = 0
  · obtain ⟨p⟩ := hIx
    refine ⟨p, hc, ?_⟩
    rewrite [Submodule.map_le_iff_le_comap]
    intro w hw
    have h := h0 w hw
    simp only [Submodule.mem_comap, h, Submodule.zero_mem]
  push_neg at h0
  obtain ⟨w, hw, hne⟩ := h0
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  refine ⟨p, hc, map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

end GlobalTheory.Div
end
