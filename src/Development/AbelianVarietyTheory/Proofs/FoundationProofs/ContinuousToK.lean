import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfJKMem
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheoremStatement

section
open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

theorem exists_map_const_eq_of_isAlgClosed {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [Field L] (i : Ω →+* L) (σ : L →+* L) (c : Ω) : ∃ c' : Ω, σ (i c) = i c' := by
  letI : Algebra Ω L := i.toAlgebra
  obtain ⟨p, hp, h0⟩ : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have e : (σ.comp i).comp (algebraMap ℚ Ω) = i.comp (algebraMap ℚ Ω) := RingHom.ext_rat _ _
  have hint : IsIntegral Ω (σ (i c)) := by
    refine ⟨p.map (algebraMap ℚ Ω), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    show p.eval₂ (i.comp (algebraMap ℚ Ω)) ((σ.comp i) c) = 0
    rw [← e, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c', hc'⟩ := minpoly.mem_range_of_degree_eq_one Ω (σ (i c))
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
  exact ⟨c', hc'.symm⟩

theorem isIntegral_map_of_map_range {R L : Type} [CommRing R] [Field L] [Algebra R L] (σ : L →+* L)
    (h : ∀ r : R, ∃ r' : R, σ (algebraMap R L r) = algebraMap R L r') {x : L} (hx : IsIntegral R x) :
    IsIntegral R (σ x) := by
  obtain ⟨p, hp, h0⟩ := hx
  have hl : p.map (σ.comp (algebraMap R L)) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨r', hr'⟩ := h (p.coeff n)
    exact ⟨r', by rw [Polynomial.coeff_map, RingHom.comp_apply, hr']⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, h0, map_zero]

theorem map_mem_ringOfIntegers_of_fix_mdl :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ)
      (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)),
      letI := GlobalTheory.K4.algPoly X Γ'
      letI := GlobalTheory.K4.algMdl X Γ' S
      ∀ (σ : GlobalTheory.K4.lev X Γ' ≃ₐ[GlobalTheory.K4.mdl X Γ' S] GlobalTheory.K4.lev X Γ') (x : GlobalTheory.K4.lev X Γ'),
        x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') →
          σ x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ _ ε X Γ' S
  letI := GlobalTheory.K4.algPoly X Γ'
  letI := GlobalTheory.K4.algMdl X Γ' S
  intro σ x hx
  have hj : σ ⟨X.jK, jK_mem_lev X Γ'⟩ = ⟨X.jK, jK_mem_lev X Γ'⟩ :=
    σ.commutes (⟨X.jK, jK_mem_mdl X Γ' S⟩ : mdl X Γ' S)
  have key : ∀ P : Polynomial Ω, ∃ Q : Polynomial Ω, σ (jPoly X Γ' P) = jPoly X Γ' Q := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P P' hP hP' =>
      obtain ⟨Q, hQ⟩ := hP
      obtain ⟨Q', hQ'⟩ := hP'
      exact ⟨Q + Q', by rw [map_add, map_add, hQ, hQ', map_add]⟩
    | monomial n c =>
      obtain ⟨c', hc'⟩ := exists_map_const_eq_of_isAlgClosed (levConst X Γ') (σ : lev X Γ' →+* lev X Γ') c
      refine ⟨Polynomial.monomial n c', ?_⟩
      simp only [jPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, map_pow]
      rw [hj, ← hc']
      rfl
  exact isIntegral_map_of_map_range (R := Polynomial Ω) (σ : lev X Γ' →+* lev X Γ') key hx

end GlobalTheory.K4
end

section
noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4.TopEta

open GlobalTheory.KZ GlobalTheory.NeedB GlobalTheory.KEdge

section General

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def toK : geo F K Ω →* (Ω ≃ₐ[K] Ω) :=
  MonoidHom.mk' (fun g => { (g : Ω ≃ₐ[F] Ω).toRingEquiv with commutes' := (TopW.mem_geo _).1 g.2 })
    (fun _ _ => AlgEquiv.ext fun _ => rfl)

theorem continuous_toK [Algebra.IsAlgebraic F Ω] : Continuous (toK : geo F K Ω →* (Ω ≃ₐ[K] Ω)) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hsub⟩ := hs
  let b := Module.finBasis K E
  have hop : IsOpen (⋂ i, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) (b i : Ω) : Set (Ω ≃ₐ[F] Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := F) (b i : Ω)
  refine Filter.mem_map.2 (Filter.mem_of_superset ((hop.preimage continuous_subtype_val).mem_nhds ?_) ?_)
  · simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    exact fun i => Subgroup.one_mem _
  · intro g hg
    simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hg
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hlin : (((toK g).toLinearMap).comp E.val.toLinearMap) = E.val.toLinearMap :=
      b.ext fun i => hg i
    exact LinearMap.congr_fun hlin ⟨z, hz⟩

theorem exists_extend [Algebra.IsAlgebraic F Ω] {N : ℕ} {ζ α β : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)}
    (hx : ∀ g, (x g).toAdd = kum (K := F) (N := N) ζ α g) (hy : ∀ g, (y g).toAdd = kum (K := F) (N := N) ζ β g)
    (R : Subring K) (η : (Ω ≃ₐ[K] Ω) → ZMod N) (h1 : IsLocallyConstant η)
    (h2 : ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g)
    (h3 : ∀ B : ValuationSubring Ω, Over R B → ∀ g, Inert B g → η g = 0) :
    ∃ η' : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η' ∧ IsLocallyConstant (fun g : geo F K Ω => η' g) ∧
      ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over R B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η' g = 0 := by
  classical
  refine ⟨fun g => if h : g ∈ geo F K Ω then η (toK ⟨g, h⟩) else 0, fun g hg h hh => ?_, ?_, fun B g hB hi hg => ?_⟩
  · simp only [dif_pos hg, dif_pos hh, dif_pos (mul_mem hg hh)]
    rw [hx, hy]
    have e : toK (⟨g * h, mul_mem hg hh⟩ : geo F K Ω) = toK ⟨g, hg⟩ * toK ⟨h, hh⟩ := map_mul toK ⟨g, hg⟩ ⟨h, hh⟩
    rw [e]
    exact h2 (toK ⟨g, hg⟩) (toK ⟨h, hh⟩)
  · have e : (fun g : geo F K Ω => if h : (g : Ω ≃ₐ[F] Ω) ∈ geo F K Ω then η (toK ⟨(g : Ω ≃ₐ[F] Ω), h⟩) else 0) = η ∘ toK :=
      funext fun g => by rw [dif_pos g.2]; rfl
    rw [e]
    exact h1.comp_continuous continuous_toK
  · simp only [dif_pos hg]
    exact h3 B hB _ hi

end General

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem fixMu_eq {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) :
    fixMu Ω M = (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup := by
  haveI : NeZero M := ⟨hM⟩
  unfold fixMu
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.subset_adjoin ℚ {ζ} rfl) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

attribute [local instance] algMdl

theorem normal_top [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) : Normal (topF X M) (topL X M) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have h := LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) (isPrimitiveRoot_eOm ε hM) le_rfl
  rw [← fixMu_eq hM (isPrimitiveRoot_eOm ε hM)] at h
  exact h

theorem over_iff (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M)) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    Over (FunctionField.ringOfIntegers Ω (topL X M)).toSubring B ↔
      ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) →
        algebraMap (topL X M) (topBar X M) f ∈ B := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  constructor
  · intro h f hf
    apply h
    have : ∃ P : Polynomial Ω, algebraMap (Polynomial Ω) (topL X M) P = f := by
      rcases hf with hf | ⟨c, hc⟩
      · exact ⟨Polynomial.X, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_X, hf]))⟩
      · exact ⟨C c, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_C, hc]))⟩
    obtain ⟨P, rfl⟩ := this
    exact Subalgebra.algebraMap_mem _ P
  · intro h f hf
    have hP : ∀ P : Polynomial Ω,
        ((algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M))) P ∈ B := by
      intro P
      induction P using Polynomial.induction_on with
      | C c => exact h _ (Or.inr ⟨c, ((coe_jPoly X _ _).trans (by rw [aeval_C])).symm⟩)
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | monomial k c hk =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact mul_mem hk (h _ (Or.inl ((coe_jPoly X _ _).trans (by rw [aeval_X]))))
    obtain ⟨q, hq, h0⟩ : IsIntegral (Polynomial Ω) f := hf
    let φ : Polynomial Ω →+* B := RingHom.codRestrict _ B hP
    have hi : IsIntegral B (algebraMap (topL X M) (topBar X M) f) := by
      refine ⟨q.map φ, hq.map φ, ?_⟩
      rw [eval₂_map]
      have := congrArg (algebraMap (topL X M) (topBar X M)) h0
      rw [hom_eval₂, map_zero] at this
      exact this
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hy]
    exact y.2

theorem spec_of_units [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M l n : ℕ} (hM : M ≠ 0) (hl : l ≠ 0) (hlM : l ^ n ∣ M) {u v : X.K}
    (hu : TopUnits.IsTopUnit X M u) (hv : TopUnits.IsTopUnit X M v) :
    (∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η) ∧
      ∀ φ : topGal X M, IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) φ
        (topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
          (topEta X M (topChar X M l n u) (topChar X M l n v)) φ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := algebraRat.charZero Ω
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  letI := algRat X (CongruenceSubgroup.Gamma M)
  haveI := isScalarTower_poly_rat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (topL X M) := GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M (Nat.pos_of_ne_zero hM) le_rfl
  haveI := normal_top X hM
  haveI : Algebra.IsAlgebraic (topF X M) (topBar X M) := Algebra.IsAlgebraic.trans _ (topL X M) _
  obtain ⟨hu0, huF, huL, hu1, hu2⟩ := hu
  obtain ⟨hv0, hvF, hvL, hv1, hv2⟩ := hv
  have hN : 0 < l ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hl)
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hα := topRoot_pow X M hN.ne' huL
  have hβ := topRoot_pow X M hN.ne' hvL
  have hx := topChar_apply X hl hlM huF hu0
  have hy := topChar_apply X hl hlM hvF hv0
  have ha : ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η := by
    obtain ⟨-, -, -, -, η, h1, h2, h3⟩ := GlobalTheory.T.kummerCupProduct_coboundary_theorem Ω (topL X M) (topBar X M) (l ^ n) _ hN hζ ⟨u, huL⟩ ⟨v, hvL⟩ _ _
      (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 hα hβ
    obtain ⟨η', g1, g2, g3⟩ := exists_extend hx hy _ η h1 h2 h3
    exact ⟨η', g1, g2, fun B g hB => g3 B g ((over_iff X M B).2 hB)⟩
  refine ⟨ha, fun φ => ?_⟩
  obtain ⟨g1, g2, g3⟩ := isTopEta_topEta X M ha
  refine isTopW_topW Ω (topL X M) (topBar X M) (topF X M) (l ^ n) _ hN hζ (topGal_topZeta X hl hlM)
    (map_mem_ringOfIntegers_of_fix_mdl Ω ε X _ _) ⟨u, huF⟩ ⟨v, hvF⟩ (topRoot X M (l ^ n) u) (topRoot X M (l ^ n) v)
    (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 ?_ ?_ _ _ hx hy _ g1 g2
    (fun B g hB => g3 B g ((over_iff X M B).1 hB)) φ
  · rw [hα, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl
  · rw [hβ, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl

end GlobalTheory.K4.TopEta

namespace GlobalTheory.K4

open GlobalTheory.KZ

attribute [local instance] algMdl


end GlobalTheory.K4
end
end
