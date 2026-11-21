import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsCurvePullbackOfIsCurveBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsDedekindDomainAffineSectionsOfIsCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldFractionRingOfDedekindFiniteType
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.SurjectiveOfIsPullbackSpecFieldExt
import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeAffineSectionsSubalgebraTensor
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsMayerVietorisConnectingExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected
import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPfEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OffDiagonalContinuationInductive
import Development.EtaleCohomology.WeilConjectures.EmptyVan2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.EtaleCohomology.KummerTheory.FinAlgExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootOfKummerClassEqZero

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add, map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_functionField_hom_germ_of_surjective :
    ∀ {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (u : X ⟶ C), Surjective u → ∃ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u ∧ ∀ (W : C.Opens) [Nonempty W] [Nonempty (u ⁻¹ᵁ W)] (a : Γ(C, W)), φ (C.germToFunctionField W a) = X.germToFunctionField (u ⁻¹ᵁ W) (u.app W a) := by
  intro C X _ _ u hu
  have hgX : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hcl : closure ({u (genericPoint X)} : Set C) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 := image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous
    rw [Set.image_singleton, hgX, Set.image_univ,
      (Surjective.surj (f := u)).range_eq] at h1
    exact h1
  have hsp : u (genericPoint X) ⤳ genericPoint C := by
    rw [specializes_iff_mem_closure, hcl]
    trivial
  refine ⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro W _ _ a
    have hmem : u (genericPoint X) ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)
    change (u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom
      ((C.presheaf.germ W (genericPoint C) _).hom a)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]
    exact Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_finite_nonempty_affine_cover_of_integral :
    ∀ (C : Scheme.{0}) [CompactSpace C] [IsIntegral C], ∃ (n : ℕ) (U : Fin n → C.Opens), (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Nonempty (U i)) ∧ (0 < n) ∧ ∀ y : C, ∃ i, y ∈ U i := by
  intro C _ _
  have hex : ∀ y : C, ∃ W : C.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hWa hyW using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set C))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  obtain ⟨y0⟩ := (inferInstance : Nonempty C)
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y0))
    exact ⟨i, hi⟩
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => hWa _,
    fun i => ⟨⟨_, hyW _⟩⟩, Finset.card_pos.2 htne, fun y => ?_⟩
  obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
  simpa using hy
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.baseChange_functionField_hom_genericPoint_comp :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u → ∃ f : L →+* X.functionField, (∀ r : k, f (algebraMap k L r) = φ (algebraMap k C.functionField r)) ∧ ∀ (V : X.Opens) [Nonempty V] (l : L), X.germToFunctionField V (x.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) = f l := by
  intro k L _ _ _ C X _ _ c u x hpb _ hc φ hφ
  let F : CommRingCat.of L ⟶ X.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  have hx : X.fromSpecStalk (genericPoint X) ≫ x = Spec.map F := by
    have h1 := Scheme.toSpecΓ_naturality x
    have h2 : x = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← h1, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [h2, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    simp only [F, Category.assoc]
  have key : ∀ (V : X.Opens) (hV : genericPoint X ∈ V),
      x.appLE ⊤ V le_top ≫ X.presheaf.germ V (genericPoint X) hV =
        x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    intro V hV
    rw [← x.appLE_map (V := ⊤) (V' := V) le_top (homOfLE le_top).op, Category.assoc,
      X.presheaf.germ_res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨F.hom, ?_, ?_⟩
  · intro r
    have hsq : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k L) ≫ F) := by
      rw [Spec.map_comp, Spec.map_comp, hc, ← Category.assoc, hφ, Category.assoc, hpb.w,
        ← Category.assoc, hx]
    have := congrArg (fun g => g.hom r) (Spec.map_injective hsq)
    simpa using this.symm
  · intro V _ l
    have hV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom l)) (key V hV)
    simpa [F] using this
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K), IsDedekindDomain B → Algebra.FiniteType k B → ¬ IsField B → IsFractionRing B K → IsFunctionField k K := by
  intro k K _ _ _ B hD hF hB hFr
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B K hdim
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem ded_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [IsDedekindDomain S] :
    IsDedekindDomain R := by
  have : IsDomain R := Function.Injective.isDomain (e : R →+* S) e.injective
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  exact { }

private theorem base_comp {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom (algebraMap k C.functionField) =
      c.appLE ⊤ W le_top ≫ C.germToFunctionField W := by
  rw [← Scheme.ΓSpecIso_naturality, hgen]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem pre_ne {X Y : Scheme.{0}} (u : X ⟶ Y) (hu : Surjective u) (W : Y.Opens)
    (h : (W : Set Y).Nonempty) : ((u ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨y, rfl⟩ := hu.surj w
  exact ⟨y, hw⟩

theorem UpperTheory.isChart_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsChart B := by
  intro k _ _ C _ c hc _ hgen W _ hW B hB
  have hWne : (W : Set C).Nonempty := ⟨_, (Classical.arbitrary W).2⟩
  obtain ⟨hC1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve k c hc
  obtain ⟨hded, hnf⟩ := hC1 W hW hWne
  let f : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hmem : ∀ a, f a ∈ B := by
    intro a
    have : f a ∈ (B : Set C.functionField) := by
      rw [hB]; exact ⟨a, rfl⟩
    exact this
  let h : Γ(C, W) ≃+* B := RingEquiv.ofBijective
    (RingHom.codRestrict (σS := Subalgebra k C.functionField) f B hmem)
    ⟨fun a b hab => Scheme.germToFunctionField_injective C W (congrArg Subtype.val hab),
     fun b => by
      have hb : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
      rw [hB] at hb
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩
  have hh : ∀ a, (h a : C.functionField) = f a := fun a => rfl
  unfold IsChart
  refine ⟨?_, ded_of_equiv h.symm, fun hf => hnf (MulEquiv.isField hf h.toMulEquiv), ?_, ?_⟩
  · haveI : LocallyOfFiniteType c := @IsProper.toLocallyOfFiniteType _ _ _ hc.2.1
    have g0 := LocallyOfFiniteType.finiteType_of_affine_subset c (isAffineOpen_top (Sp k)) hW le_top
    have gi : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, by simp⟩)
    have g2 := (g0.comp gi).comp_surjective (g := (h : Γ(C, W) →+* B)) h.surjective
    rw [← RingHom.finiteType_algebraMap]
    convert g2
    ext x
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)) (base_comp c hgen W)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← hh] at this
    simpa using this
  · have hfr := functionField_isFractionRing_of_isAffineOpen C W hW
    have := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv C.functionField h).mp hfr
    have heq : ((algebraMap Γ(C, W) C.functionField).comp h.symm.toRingHom).toAlgebra =
        (inferInstance : Algebra B C.functionField) := by
      apply Algebra.algebra_ext
      intro b
      obtain ⟨a, rfl⟩ := h.surjective b
      show algebraMap Γ(C, W) _ (h.symm (h a)) = (h a : C.functionField)
      rw [h.symm_apply_apply]
      rfl
    rw [heq] at this
    exact this
  · intro L _ _ _
    have hp := IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    obtain ⟨hX, e, -, -⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c _ _ hp hgen W hW B hB
    have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c _ _ hp
    obtain ⟨hX1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve L _ (UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hc)
    obtain ⟨hd2, hn2⟩ := hX1 _ hX (pre_ne _ hsurj W hWne)
    exact ⟨ded_of_equiv e, fun hf => hn2 (MulEquiv.isField hf e.symm.toMulEquiv)⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_tensor_lift {k L K M : Type} [Field k] [Field L] [Field K] [CommRing M] [Algebra k L] [Algebra k K]
    (f : L →+* M) (g : K →+* M) (h : ∀ r : k, f (algebraMap k L r) = g (algebraMap k K r)) :
    ∃ θ : L ⊗[k] K →+* M, ∀ l a, θ (l ⊗ₜ[k] a) = f l * g a := by
  letI : Algebra k M := (g.comp (algebraMap k K)).toAlgebra
  let f' : L →ₐ[k] M := { f with commutes' := fun r => h r }
  let g' : K →ₐ[k] M := { g with commutes' := fun r => rfl }
  exact ⟨(Algebra.TensorProduct.productMap f' g').toRingHom, fun l a => by simp [f', g']⟩

private theorem core (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L)
    (hpb : IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [Algebra k C.functionField]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    {n : ℕ} (U : Fin n → C.Opens) (hUa : ∀ i, IsAffineOpen (U i)) [hne : ∀ i, Nonempty (U i)]
    (hUc : ∀ y : C, ∃ i, y ∈ U i) (hn : 0 < n)
    (B : Fin n → Subalgebra k C.functionField)
    (hB : ∀ i, (B i : Set C.functionField) = Set.range (C.germToFunctionField (U i)))
    (hfr : ∀ i, IsFractionRing (B i) C.functionField) :
    ∃ θ : L ⊗[k] C.functionField →+* X.functionField,
      Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c u x hpb
  obtain ⟨φ, hφgen, hφgerm⟩ := UpperTheory.exists_functionField_hom_germ_of_surjective u hsurj
  obtain ⟨f, hfk, hfx⟩ := UpperTheory.baseChange_functionField_hom_genericPoint_comp k L c u x hpb hK φ hφgen
  obtain ⟨θ, hθ⟩ := exists_tensor_lift f φ hfk
  have hne' : ∀ i, Nonempty (u ⁻¹ᵁ U i) := by
    intro i
    obtain ⟨⟨z, hz⟩⟩ := hne i
    obtain ⟨y, rfl⟩ := hsurj.surj z
    exact ⟨⟨y, hz⟩⟩
  have chart : ∀ i, IsAffineOpen (u ⁻¹ᵁ U i) ∧ ∃ e : L ⊗[k] B i ≃+* Γ(X, u ⁻¹ᵁ U i),
      ∀ s, θ (inc L (B i) s) = X.germToFunctionField (u ⁻¹ᵁ U i) (e s) := by
    intro i
    haveI := hne' i
    obtain ⟨hV, e, he1, he2⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c u x hpb hK (U i) (hUa i) (B i) (hB i)
    refine ⟨hV, e, fun s => ?_⟩
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul l b =>
      obtain ⟨a, ha⟩ : (b : C.functionField) ∈ Set.range (C.germToFunctionField (U i)) := by
        rw [← hB i]
        exact b.2
      have hsplit : l ⊗ₜ[k] b = (l ⊗ₜ[k] (1 : B i)) * ((1 : L) ⊗ₜ[k] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [show inc L (B i) (l ⊗ₜ[k] b) = l ⊗ₜ[k] (b : C.functionField) from rfl, hθ, hsplit,
        map_mul, map_mul, he1 a b ha.symm, he2 l, hfx, ← hφgerm (U i) a, ha]
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcomp : θ.comp Algebra.TensorProduct.includeRight.toRingHom = φ := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply, hθ]
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨hV0, e0, he0⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    obtain ⟨s, β, hβ, hs⟩ := UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator k L C.functionField (B ⟨0, hn⟩) (hfr _) t
    have h1 : θ (inc L (B ⟨0, hn⟩) s) = 0 := by rw [← hs, map_mul, ht, zero_mul]
    rw [he0] at h1
    have h2 : e0 s = 0 :=
      X.germToFunctionField_injective _ (h1.trans (map_zero _).symm)
    have h3 : s = 0 := e0.injective (h2.trans (map_zero e0).symm)
    rw [h3, map_zero] at hs
    have hβ' : (β : C.functionField) ≠ 0 := fun h => hβ (Subtype.ext h)
    have hu : IsUnit ((1 : L) ⊗ₜ[k] (β : C.functionField)) := by
      refine ⟨⟨1 ⊗ₜ[k] (β : C.functionField), 1 ⊗ₜ[k] (β : C.functionField)⁻¹, ?_, ?_⟩, rfl⟩
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hβ']
        rfl
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hβ']
        rfl
    exact hu.mul_left_eq_zero.mp hs
  refine ⟨θ, by rw [hcomp]; exact hφgen, hinj, ?_, ?_⟩
  · intro h
    obtain ⟨hV, e, he⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    haveI := functionField_isFractionRing_of_isAffineOpen X _ hV
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) h
    refine ⟨inc L (B ⟨0, hn⟩) (e.symm p), inc L (B ⟨0, hn⟩) (e.symm q), ?_, ?_⟩
    · intro h0
      have h4 := congrArg θ h0
      rw [he, map_zero, e.apply_symm_apply] at h4
      have h5 : (q : Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) = 0 :=
        X.germToFunctionField_injective _ (h4.trans (map_zero _).symm)
      exact nonZeroDivisors.coe_ne_zero q h5
    · rw [he, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hpq
  · intro y
    obtain ⟨i, hi⟩ := hUc (u y)
    haveI := hne' i
    obtain ⟨hV, e, he⟩ := chart i
    have hy : y ∈ u ⁻¹ᵁ U i := hi
    refine ⟨i, (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap e.toRingHom, inferInstance, fun s hs => ?_⟩
    have hsP : e s ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hs
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
    haveI := hV.isLocalization_stalk ⟨y, hy⟩
    refine ⟨(IsLocalization.map_units (X.presheaf.stalk y)
      (⟨e s, hsP⟩ : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)).unit, ?_⟩
    rw [he]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hy (e s)

theorem UpperTheory.isFunctionField_and_chart_cover_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ ∃ (n : ℕ) (B : Fin n → Subalgebra k C.functionField), (∀ i, IsChart (B i)) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], ∃ (X : Scheme.{0}) (_ : IsIntegral X) (u : X ⟶ C) (x : X ⟶ Sp L) (θ : L ⊗[k] C.functionField →+* X.functionField), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧ (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) ∧ Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  intro k _ _ C _ c hcurve _ hK
  have hprop : IsProper c := hcurve.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨n, U, hUa, hUne, hn, hUc⟩ := UpperTheory.exists_finite_nonempty_affine_cover_of_integral C
  haveI : ∀ i, Nonempty (U i) := hUne
  have hex : ∀ i, ∃ B : Subalgebra k C.functionField,
      (B : Set C.functionField) = Set.range (C.germToFunctionField (U i)) :=
    fun i => UpperTheory.exists_subalgebra_eq_range_germToFunctionField k c hK (U i)
  choose B hB using hex
  have hchart : ∀ i, IsChart (B i) :=
    fun i => UpperTheory.isChart_affine_sections_of_isCurve k c hcurve hK (U i) (hUa i) (B i) (hB i)
  refine ⟨UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing k C.functionField (B ⟨0, hn⟩) (hchart _).2.1 (hchart _).1
    (hchart _).2.2.1 (hchart _).2.2.2.1, n, B, hchart, ?_⟩
  intro L _ _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hpb : IsPullback (pullback.fst c g) (pullback.snd c g) c g := IsPullback.of_hasPullback c g
  have hcurve' := UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hcurve
  haveI hXint : IsIntegral (pullback c g) := hcurve'.1
  have hstalk := (UpperTheory.isDedekindDomain_affine_sections_of_isCurve L (pullback.snd c g) hcurve').2
  obtain ⟨θ, h1, h2, h3, h4⟩ := core k L c (pullback.fst c g) (pullback.snd c g) hpb hK U hUa hUc hn
    B hB (fun i => (hchart i).2.2.2.1)
  exact ⟨pullback c g, hXint, pullback.fst c g, pullback.snd c g, θ, hpb, hstalk, h1, h2, h3, h4⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.SeparatedH1Cohomology

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_h0_restriction_eq_of_le_open {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] {O P : E.Opens} (h : P ≤ O) (c : Ht q (sch.obj P) 0 1) :
    ∃ a : Ht q (sch.obj O) 0 1, pl q 1 (E.homOfLE h) 0 a = c := by
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q 1)
  by_cases hP : Nonempty (P : Scheme.{0})
  · haveI : IsIntegral (P : Scheme.{0}) := isIntegral_of_isOpenImmersion (P.ι ≫ j)
    haveI : ConnectedSpace (P : Scheme.{0}) := inferInstance
    obtain ⟨k, hk⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q 1 (P : Scheme.{0}) (ζ.map (P.ι ≫ j).appTop.hom) ((e P).symm c)
    refine ⟨e O (k • twGen 1 (ζ.map (O.ι ≫ j).appTop.hom)), ?_⟩
    have h1 : c = e P (k • twGen 1 (ζ.map (P.ι ≫ j).appTop.hom)) := by
      rw [← hk, AddEquiv.apply_symm_apply]
    have hk : E.homOfLE h ≫ O.ι ≫ j = P.ι ≫ j := by simp
    rw [h1, he, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1, ← hk]
    congr 1
  · have hb : P = ⊥ := le_bot_iff.1 fun p hp => (hP ⟨(⟨p, hp⟩ : P)⟩).elim
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := E) (tw q 1) 0
    exact ⟨0, Subsingleton.elim _ _⟩

private theorem two {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] (O₁ O₂ : E.Opens) (hcov : O₁ ⊔ O₂ = ⊤) (y : Ht q (sch.obj E) 1 1)
    (h₁ : pl q 1 O₁.ι 1 y = 0) (h₂ : pl q 1 O₂.ι 1 y = 0) : y = 0 := by
  obtain ⟨d, hd, -⟩ := UpperTheory.Cb.exists_mayerVietoris_connecting_exact (ZMod q) (tw q 1)
  have hc : Cover2 (ZMod q) (sch.map O₁.ι) (sch.map O₂.ι) := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 (ZMod q) O₁ O₂ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch
    infer_instance
  let e := ((isPullback_opens_inf O₁ O₂).map sch).isoPullback
  obtain ⟨-, hz, hx⟩ := hd _ _ hc 0
  obtain ⟨c, hcy⟩ := (hx y).1 ⟨h₁, h₂⟩
  obtain ⟨a, ha⟩ := exists_h0_restriction_eq_of_le_open ζ j (inf_le_left : O₁ ⊓ O₂ ≤ O₁) (pull (ZMod q) e.hom (tw q 1) 0 c)
  have hf : pullback.fst (sch.map O₁.ι) (sch.map O₂.ι) = e.inv ≫ sch.map (E.homOfLE inf_le_left) := by
    simp [e]
  have h0 : d _ _ hc 0 c = 0 := by
    refine (hz c).2 ⟨a, 0, ?_⟩
    rw [map_zero, sub_zero, hf, pull_comp]
    change c = pull _ e.inv _ 0 (pl q 1 _ 0 a)
    rw [ha, ← pull_comp, e.inv_hom_id, pull_id]
  exact hcy.symm.trans h0

private theorem step {q : ℕ} [NeZero q] {X : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (A B : X.Opens) (x : Ht q (sch.obj X) 1 1) (hA : pl q 1 A.ι 1 x = 0) (hB : pl q 1 B.ι 1 x = 0) :
    pl q 1 (A ⊔ B).ι 1 x = 0 := by
  have key : ∀ C : X.Opens, pl q 1 C.ι 1 x = 0 →
      pl q 1 ((A ⊔ B).ι ⁻¹ᵁ C).ι 1 (pl q 1 (A ⊔ B).ι 1 x) = 0 := by
    intro C hC
    have h1 : ((A ⊔ B).ι ⁻¹ᵁ C).ι ≫ (A ⊔ B).ι = ((A ⊔ B).ι ∣_ C) ≫ C.ι := (morphismRestrict_ι _ _).symm
    change pull _ _ _ _ (pull _ _ _ _ x) = 0
    rw [← pull_comp, ← sch.map_comp, h1, sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 C.ι 1 x) = 0
    rw [hC, map_zero]
  refine two ζ (A ⊔ B).ι ((A ⊔ B).ι ⁻¹ᵁ A) ((A ⊔ B).ι ⁻¹ᵁ B) ?_ _ (key A hA) (key B hB)
  refine eq_top_iff.2 fun p _ => ?_
  have hp : (A ⊔ B).ι p ∈ A ⊔ B := p.2
  exact TopologicalSpace.Opens.mem_sup.2 (TopologicalSpace.Opens.mem_sup.1 hp)

end UpperTheory.Cb.SeparatedH1Cohomology

theorem UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (V : X.Opens), V ≤ ⨆ i, U i → ∀ x : Ht q (sch.obj X) 1 1, (∀ i, pl q 1 (U i).ι 1 x = 0) → pl q 1 V.ι 1 x = 0 := by
  intro q _ X _ hζ _ n
  obtain ⟨ζ⟩ := hζ
  induction n with
  | zero =>
    intro U V hV x _
    have hb : V = ⊥ := le_bot_iff.1 (hV.trans (iSup_of_empty U).le)
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := X) (tw q 1) 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro U V hV x hx
    have hW := ih (fun i => U i.castSucc) (⨆ i : Fin n, U i.castSucc) le_rfl x (fun i => hx _)
    have hS := UpperTheory.Cb.SeparatedH1Cohomology.step ζ _ _ x hW (hx (Fin.last n))
    have hle : V ≤ (⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n) := hV.trans (iSup_le fun i => by
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact le_sup_of_le_left (le_iSup (fun i : Fin n => U i.castSucc) i))
    have hι : V.ι = X.homOfLE hle ≫ ((⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n)).ι := by simp
    rw [hι]
    change pull _ (sch.map _) _ _ x = 0
    rw [sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 _ 1 x) = 0
    rw [hS, map_zero]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.MuCohomologyGluing

private theorem sub_empty (q : ℕ) (Y : Scheme.{0}) [IsEmpty Y] (n i : ℤ) :
    Subsingleton (Ht q (sch.obj Y) n i) := by
  have e : Y ≅ ⊥_ Scheme.{0} := (isInitialOfIsEmpty (X := Y)).uniqueUpToIso initialIsInitial
  exact LateralTheory.EtaleTrace.H_sub (ZMod q) Y
    (LateralTheory.EWeil.EmptyVan₂.isZero_free.of_iso ((free (ZMod q)).mapIso (yoneda.mapIso e))) (tw q i) n

private theorem pl_le (q : ℕ) {X : Scheme.{0}} {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ C)
    (z : Ht q (sch.obj C) 1 1) :
    pl q 1 (X.homOfLE h1) 1 (pl q 1 (X.homOfLE h2) 1 z) = pl q 1 (X.homOfLE h3) 1 z := by
  rw [← pl_comp, Scheme.homOfLE_homOfLE]

private theorem van (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X] (hζ : Nonempty (Prim q Γ(X, ⊤)))
    (hq : IsUnit (q : Γ(X, ⊤))) (n : ℕ) (A : Fin n → X.Opens) (P : X.Opens) (hP : P ≤ ⨆ i, A i)
    (d : Ht q (sch.obj P) 1 1)
    (hd : ∀ i, pl q 1 (X.homOfLE (inf_le_right : A i ⊓ P ≤ P)) 1 d = 0) : d = 0 := by
  have hmem : ∀ x : P.toScheme, P.ι x ∈ P := fun x => by
    rw [← SetLike.mem_coe, ← P.range_ι]
    exact ⟨x, rfl⟩
  by_cases hne : Nonempty P.toScheme
  · haveI : IsIntegral P.toScheme := isIntegral_of_isOpenImmersion P.ι
    have hζ' : Nonempty (Prim q Γ(P.toScheme, ⊤)) := hζ.map (Prim.map P.ι.appTop.hom)
    have hq' : IsUnit (q : Γ(P.toScheme, ⊤)) := by simpa using hq.map P.ι.appTop.hom
    have key := UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero q P.toScheme hζ' hq' n (fun i => P.ι ⁻¹ᵁ A i) ⊤ (by
      intro x _
      have hx : P.ι x ∈ ⨆ i, A i := hP (hmem x)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩) d (fun i => by
        have e : P.ι ⁻¹ᵁ A i ≤ P.ι ⁻¹ᵁ (A i ⊓ P) := by
          intro x hx
          exact ⟨hx, hmem x⟩
        have w : P.ι.resLE (A i ⊓ P) (P.ι ⁻¹ᵁ A i) e ≫ X.homOfLE (inf_le_right : A i ⊓ P ≤ P) =
            (P.ι ⁻¹ᵁ A i).ι := by
          rw [← cancel_mono P.ι]
          simp
        rw [← w, pl_comp, hd i, map_zero])
    have w : P.toScheme.topIso.inv ≫ (⊤ : P.toScheme.Opens).ι = 𝟙 _ := P.toScheme.topIso.inv_hom_id
    have := congrArg (pl q 1 P.toScheme.topIso.inv 1) key
    rw [← pl_comp, w, map_zero] at this
    simpa [pl, pull_id] using this
  · haveI : IsEmpty P.toScheme := not_nonempty_iff.1 hne
    haveI := sub_empty q P.toScheme 1 1
    exact Subsingleton.elim _ _

end UpperTheory.Cb.MuCohomologyGluing

open UpperTheory.Cb.MuCohomologyGluing in
theorem UpperTheory.exists_h1Mu_glue_of_compatible :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (x : ∀ i, Ht q (sch.obj (U i)) 1 1), (∀ i j, pl q 1 (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) 1 (x i) = pl q 1 (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) 1 (x j)) → ∃ y : Ht q (sch.obj (⨆ i, U i : X.Opens)) 1 1, ∀ i, pl q 1 (X.homOfLE (le_iSup U i)) 1 y = x i := by
  intro q _ X _ hζ hq n
  induction n with
  | zero =>
    intro U x _
    exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro U x hx
    set W : X.Opens := ⨆ i : Fin n, U i.castSucc with hW
    have hAW : ∀ i : Fin n, U i.castSucc ≤ W := fun i => le_iSup (fun i : Fin n => U i.castSucc) i
    obtain ⟨y, hy⟩ : ∃ y : Ht q (sch.obj W) 1 1, ∀ i : Fin n, pl q 1 (X.homOfLE (hAW i)) 1 y = x i.castSucc :=
      ih (fun i => U i.castSucc) (fun i => x i.castSucc) (fun i j => hx _ _)
    set B : X.Opens := U (Fin.last n) with hB
    have c : UpperTheory.Cb.OffDiagonalContinuation.Sq W B (W ⊔ B) (W ⊓ B) := ⟨rfl, rfl⟩
    obtain ⟨dd, hdd, -⟩ := UpperTheory.Cb.OffDiagonalContinuation.mv q 1
    have hex := (hdd c 1).2.2
    have d0 : pl q 1 (X.homOfLE (inf_le_left : W ⊓ B ≤ W)) 1 y -
        pl q 1 (X.homOfLE (inf_le_right : W ⊓ B ≤ B)) 1 (x (Fin.last n)) = 0 := by
      refine van q X hζ hq n (fun i => U i.castSucc) (W ⊓ B) inf_le_left _ (fun i => ?_)
      have h1 : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc ⊓ B := inf_le_inf_left _ inf_le_right
      rw [map_sub, pl_le q _ _ (inf_le_right.trans inf_le_left), pl_le q _ _ (inf_le_right.trans inf_le_right),
        ← pl_le q (inf_le_left : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc) (hAW i),
        ← pl_le q h1 (inf_le_right : U i.castSucc ⊓ B ≤ B), hy i, ← hx i.castSucc (Fin.last n),
        pl_le q h1 inf_le_left inf_le_left, sub_self]
    obtain ⟨z, hz⟩ := (hex (y, x (Fin.last n))).1 d0
    have hz1 : pl q 1 (X.homOfLE (le_sup_left : W ≤ W ⊔ B)) 1 z = y := congrArg Prod.fst hz
    have hz2 : pl q 1 (X.homOfLE (le_sup_right : B ≤ W ⊔ B)) 1 z = x (Fin.last n) := congrArg Prod.snd hz
    have hle : (⨆ i, U i : X.Opens) ≤ W ⊔ B := by
      refine iSup_le fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact le_sup_right
      · exact (hAW j).trans le_sup_left
    refine ⟨pl q 1 (X.homOfLE hle) 1 z, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [pl_le q _ _ le_sup_right, hz2]
    · rw [pl_le q _ _ ((hAW j).trans le_sup_left), ← pl_le q (hAW j) (le_sup_left : W ≤ W ⊔ B), hz1]
      exact hy j
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicGlue

variable {X : Scheme.{0}}

private theorem top_le (V : X.Opens) : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp

private theorem top_pre {A B : Scheme.{0}} (f : A ⟶ B) : (⊤ : A.Opens) ≤ f ⁻¹ᵁ (⊤ : B.Opens) :=
  fun _ _ => trivial

private theorem appTop_eq {A B : Scheme.{0}} (f : A ⟶ B) : f.appTop = f.appLE ⊤ ⊤ (top_pre f) :=
  Scheme.Hom.app_eq_appLE f

private noncomputable def rho (V : X.Opens) : Γ(X, V) →+* Γ(V.toScheme, ⊤) :=
  (V.ι.appLE V ⊤ (top_le V)).hom

private theorem appLE_congr' {A B : Scheme.{0}} {g g' : A ⟶ B} (hg : g = g') (V : B.Opens) (W : A.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

private theorem rho_res {U V : X.Opens} (e : V ≤ U) (s : Γ(X, U)) :
    (X.homOfLE e).appTop.hom (rho U s) = rho V ((X.presheaf.map (homOfLE e).op).hom s) := by
  have h1 : U.ι.appLE U ⊤ (top_le U) ≫ (X.homOfLE e).appTop =
      X.presheaf.map (homOfLE e).op ≫ V.ι.appLE V ⊤ (top_le V) := by
    rw [Scheme.Hom.map_appLE, appTop_eq, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr' (X.homOfLE_ι e) _ _ _ _
  exact congr($(h1).hom s)

private theorem rho_generic (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    (U.fromSpecStalkOfMem x hx).appTop.hom (rho U s) =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s) := by
  have hp : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
    intro z _
    have hz : X.fromSpecStalk x z ⤳ x := by
      have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hz.mem_open U.2 hx
  have h1 : U.ι.appLE U ⊤ (top_le U) ≫ (U.fromSpecStalkOfMem x hx).appTop =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [appTop_eq, Scheme.Hom.appLE_comp_appLE,
      appLE_congr' (Scheme.Opens.fromSpecStalkOfMem_ι U x hx) U ⊤ _ hp,
      Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE hp).op :
        Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  exact congr($(h1).hom s)

private theorem sec [IsIntegral X] (V : X.Opens) [Nonempty V] (f : X.functionField)
    (h : ∀ x ∈ V, ∃ w : X.presheaf.stalk x, algebraMap _ X.functionField w = f) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = f := by
  have hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧
      ∃ s : Γ(X, W), X.germToFunctionField W (h := ⟨⟨x.1, hxW⟩⟩) s = f := by
    intro x
    obtain ⟨w, hw⟩ := h x.1 x.2
    obtain ⟨W, hxW, g, hg⟩ := X.presheaf.exists_germ_eq w
    refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩
    have : Nonempty W := ⟨⟨x.1, hxW⟩⟩
    rw [← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]
    simp
  choose W hxW hWV s hs using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s := by
    intro i j
    obtain ⟨y, hy⟩ : ((W i : Set X) ∩ W j).Nonempty :=
      nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩
    have : Nonempty (W i ⊓ W j : X.Opens) := ⟨⟨y, hy⟩⟩
    have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
    have : Nonempty (W j) := ⟨⟨_, hxW j⟩⟩
    apply Scheme.germToFunctionField_injective X (W i ⊓ W j)
    change X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) =
      X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))
    simp [hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat
  refine ⟨t, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty V›
  have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
  rw [← hs i, ← ht i]
  change _ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

private theorem sec_unit [IsIntegral X] (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (q : ℕ) (hq : q ≠ 0)
    (W : X.Opens) [Nonempty W] (g : (X.functionField)ˣ) (c : (Γ(X, W))ˣ)
    (hc : X.germToFunctionField W (c : Γ(X, W)) = (g : X.functionField) ^ q) :
    ∃ w : (Γ(X, W))ˣ, X.germToFunctionField W (w : Γ(X, W)) = g := by
  have key : ∀ (f : X.functionField) (d : Γ(X, W)), X.germToFunctionField W d = f ^ q →
      ∃ s : Γ(X, W), X.germToFunctionField W s = f := by
    intro f d hd
    refine sec W f fun x hx => ?_
    have := hn x
    have h1 : IsIntegral (X.presheaf.stalk x) (f ^ q) := by
      rw [← hd, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
      exact isIntegral_algebraMap
    exact (IsIntegrallyClosed.isIntegral_iff (K := X.functionField)).1 (h1.of_pow (Nat.pos_of_ne_zero hq))
  obtain ⟨s, hs⟩ := key g c hc
  obtain ⟨s', hs'⟩ := key (g⁻¹ : (X.functionField)ˣ) ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) (by
    have h2 : X.germToFunctionField W ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * X.germToFunctionField W (c : Γ(X, W)) = 1 := by
      rw [← map_mul]; simp
    rw [hc] at h2
    rw [eq_comm, ← mul_right_inj' (pow_ne_zero q g.ne_zero)]
    rw [← mul_pow]
    simpa [mul_comm] using h2.symm)
  have h3 : s * s' = 1 := Scheme.germToFunctionField_injective X W (by
    rw [map_mul, hs, hs', map_one]; simp)
  have h4 : s' * s = 1 := by rw [mul_comm]; exact h3
  exact ⟨⟨s, s', h3, h4⟩, hs⟩

private theorem spread (y : X) (u : (X.presheaf.stalk y)ˣ) :
    ∃ (W : X.Opens) (hy : y ∈ W) (v : (Γ(X, W))ˣ), (X.presheaf.germ W y hy).hom (v : Γ(X, W)) = u := by
  obtain ⟨W, hW, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk y)
  have hb : y ∈ X.basicOpen s := (X.mem_basicOpen s y hW).2 (by rw [hs]; exact u.isUnit)
  refine ⟨X.basicOpen s, hb, (X.toRingedSpace.isUnit_res_basicOpen s).unit, ?_⟩
  rw [IsUnit.unit_spec, ← hs]
  exact X.presheaf.germ_res_apply _ _ _ _

end UpperTheory.PicGlue

namespace UpperTheory.PicGlue

variable {X : Scheme.{0}}

private theorem qU (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) (V : X.Opens) : IsUnit (q : Γ(V.toScheme, ⊤)) := by
  simpa using hq.map V.ι.appTop.hom

private noncomputable def tr (V : X.Opens) (v : (Γ(X, V))ˣ) : (Γ(V.toScheme, ⊤))ˣ :=
  Units.map (rho V).toMonoidHom v

private noncomputable def resU {U V : X.Opens} (e : V ≤ U) (v : (Γ(X, U))ˣ) : (Γ(X, V))ˣ :=
  Units.map (X.presheaf.map (homOfLE e).op).hom.toMonoidHom v

private theorem nat_tr (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(X, ⊤))) {U V : X.Opens} (e : V ≤ U) (v : (Γ(X, U))ˣ) :
    pl q 1 (X.homOfLE e) 1 (kum q (tr U v)) = kum q (tr V (resU e v)) := by
  have h := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (X.homOfLE e) (tr U v) (qU q hq U)
  have h2 : Units.map (X.homOfLE e).appTop.hom.toMonoidHom (tr U v) = tr V (resU e v) := by
    ext
    exact rho_res e _
  exact h.trans (congrArg _ h2)

private theorem gtf_res [IsIntegral X] {U V : X.Opens} [Nonempty U] [Nonempty V] (e : V ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField V ((X.presheaf.map (homOfLE e).op).hom s) = X.germToFunctionField U s :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem agree [IsIntegral X] (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(X, ⊤)))
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (F : X.functionField) {U V W : X.Opens}
    [Nonempty U] [Nonempty V] [Nonempty W] (eU : W ≤ U) (eV : W ≤ V) (v : (Γ(X, U))ˣ) (v' : (Γ(X, V))ˣ)
    (h h' : (X.functionField)ˣ) (hF : F = X.germToFunctionField U (v : Γ(X, U)) * (h : X.functionField) ^ q)
    (hF' : F = X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q) :
    pl q 1 (X.homOfLE eU) 1 (kum q (tr U v)) = pl q 1 (X.homOfLE eV) 1 (kum q (tr V v')) := by
  rw [nat_tr q hq, nat_tr q hq]
  have hA : X.germToFunctionField W (resU eU v : Γ(X, W)) = X.germToFunctionField U (v : Γ(X, U)) := gtf_res eU _
  have hB : X.germToFunctionField W (resU eV v' : Γ(X, W)) = X.germToFunctionField V (v' : Γ(X, V)) := gtf_res eV _
  have hb : X.germToFunctionField V (v' : Γ(X, V)) ≠ 0 := (v'.isUnit.map (X.germToFunctionField V).hom).ne_zero
  have hc1 : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) *
      X.germToFunctionField V (v' : Γ(X, V)) = X.germToFunctionField U (v : Γ(X, U)) := by
    rw [← hA, ← hB, ← map_mul]
    simp
  have hh : (h : X.functionField) ^ q ≠ 0 := pow_ne_zero q h.ne_zero
  have hc : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) =
      (((h' / h : (X.functionField)ˣ)) : X.functionField) ^ q := by
    rw [Units.val_div_eq_div_val, div_pow, eq_div_iff hh]
    have h3 : X.germToFunctionField V (v' : Γ(X, V)) *
        (X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * (h : X.functionField) ^ q) =
        X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q := by
      rw [← hF', hF, ← hc1]
      ring
    exact mul_left_cancel₀ hb h3
  obtain ⟨w, hw⟩ := sec_unit hn q (NeZero.ne q) W (h' / h) _ hc
  have hrel : resU eU v = resU eV v' * w ^ q := by
    have h4 : resU eU v * (resU eV v')⁻¹ = w ^ q := by
      ext
      apply Scheme.germToFunctionField_injective X W
      rw [hc, Units.val_pow_eq_pow_val, map_pow, hw]
    rw [← h4]
    simp
  have hm : tr W (resU eV v' * w ^ q) = tr W (resU eV v') * (tr W w) ^ q := by
    simp [tr]
  rw [hrel, hm, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W (resU eV v')) ((tr W w) ^ q) (qU q hq W)).1,
    ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W w) (tr W w) (qU q hq W)).2, add_zero]

private theorem isIso_ι (T : X.Opens) (hT : T = ⊤) : IsIso T.ι := by
  subst hT
  exact (inferInstance : IsIso (Scheme.topIso X).hom)

private theorem core (q : ℕ) [NeZero q] [IsIntegral X] (hP : Nonempty (Prim q Γ(X, ⊤))) (hq : IsUnit (q : Γ(X, ⊤)))
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (F : (X.functionField)ˣ) (n : ℕ) (U : Fin n → X.Opens)
    [∀ i, Nonempty (U i)] (hU : ⨆ i, U i = ⊤) (v : ∀ i, (Γ(X, U i))ˣ) (h : Fin n → (X.functionField)ˣ)
    (hF : ∀ i, (F : X.functionField) = X.germToFunctionField (U i) (v i : Γ(X, U i)) * (h i : X.functionField) ^ q) :
    ∃ x : Ht q (sch.obj X) 1 1, pl q 1 (X.fromSpecStalk (genericPoint X)) 1 x =
      kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) := by
  have hW : ∀ i j, Nonempty (U i ⊓ U j : X.Opens) := fun i j => by
    obtain ⟨⟨a, ha⟩⟩ := ‹∀ i, Nonempty (U i)› i
    obtain ⟨⟨b, hb⟩⟩ := ‹∀ i, Nonempty (U i)› j
    obtain ⟨y, hy⟩ : ((U i : Set X) ∩ U j).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨y, hy⟩⟩
  obtain ⟨y, hy⟩ := UpperTheory.exists_h1Mu_glue_of_compatible q X hP hq n U (fun i => kum q (tr (U i) (v i))) (fun i j => by
    have := hW i j
    exact agree q hq hn F inf_le_left inf_le_right (v i) (v j) (h i) (h j) (hF i) (hF j))
  have hξ : genericPoint X ∈ (⨆ i, U i : X.Opens) := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hξ
  have := isIso_ι (⨆ i, U i) hU
  have hcomp : X.fromSpecStalk (genericPoint X) ≫ inv (⨆ i, U i : X.Opens).ι =
      (U i).fromSpecStalkOfMem _ hi ≫ X.homOfLE (le_iSup U i) := by
    rw [← cancel_mono (⨆ i, U i : X.Opens).ι, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨pl q 1 (inv (⨆ i, U i : X.Opens).ι) 1 y, ?_⟩
  rw [← pl_comp, hcomp, pl_comp, hy i]
  have hqS : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hq.map (X.fromSpecStalk (genericPoint X)).appTop.hom
  have h1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 ((U i).fromSpecStalkOfMem _ hi) (tr (U i) (v i)) (qU q hq _)
  have h2 : Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F =
      Units.map ((U i).fromSpecStalkOfMem _ hi).appTop.hom.toMonoidHom (tr (U i) (v i)) *
        (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) ^ q := by
    ext
    have h3 := rho_generic (U i) _ hi (v i : Γ(X, U i))
    have h4 := congrArg (Scheme.ΓSpecIso X.functionField).inv.hom (hF i)
    rw [map_mul, map_pow] at h4
    exact h4.trans (congrArg (· * _) h3.symm)
  refine h1.trans ?_
  have hb := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i))
    (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) hqS).2
  rw [h2, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 _ _ hqS).1, hb, add_zero]

end UpperTheory.PicGlue

theorem UpperTheory.exists_h1Mu_of_locally_unit_times_power :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → CompactSpace X → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ x : Ht q (sch.obj X) 1 1, pl q 1 (X.fromSpecStalk (genericPoint X)) 1 x = kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) := by
  intro q _ X _ hP hq hc hn F hF
  choose u h hu using hF
  choose W hy v hv using fun y => UpperTheory.PicGlue.spread y (u y)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun y => (W y : Set X))
    (fun y _ => (W y).isOpen.mem_nhds (hy y))
  let idx : Fin t.card → X := fun i => (t.equivFin.symm i).1
  have : ∀ i, Nonempty (W (idx i)) := fun i => ⟨⟨_, hy _⟩⟩
  refine UpperTheory.PicGlue.core q hP hq hn F t.card (fun i => W (idx i)) ?_ (fun i => v (idx i)) (fun i => h (idx i)) (fun i => ?_)
  · rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨z, hz⟩, by simpa [idx] using hyz⟩
  · rw [hu (idx i), ← hv (idx i), Scheme.algebraMap_germ_eq_germToFunctionField X (hy (idx i))]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicRigid

private lemma exists_prim (q : ℕ) [NeZero q] (L : Type) [Field L] [IsAlgClosed L] (hq : IsUnit (q : L)) :
    Nonempty (Prim q L) := by
  have hdeg : (Polynomial.cyclotomic q L).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast this.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

private lemma pl_id (q : ℕ) (i : ℤ) {X : Scheme.{0}} (m : ℤ) (y : Ht q (sch.obj X) m i) :
    pl q i (𝟙 X) m y = y := by
  show pull (ZMod q) (sch.map (𝟙 X)) (tw q i) m y = y
  rw [CategoryTheory.Functor.map_id, pull_id]

private lemma main (hA : LateralTheory.KummerTheory.AlgExt) : Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q := by
  intro hy q _ k L _ _ _ _ _ hq C _ c hc X _ u x pb hnorm φ hφ F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e2, e3⟩ := hy
  have hP : IsProper c := hc.2.1
  have hS1 : SmoothOfRelativeDimension 1 c := hc.2.2
  have hS : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hqL : IsUnit (q : L) := by simpa using hq.map (algebraMap k L)
  have hxP : IsProper x := MorphismProperty.of_isPullback (P := @IsProper) pb hP
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  let ρ : L →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop).hom
  have hqX : IsUnit (q : Γ(X, ⊤)) := by simpa using hqL.map ρ
  obtain ⟨ζ⟩ := exists_prim q L hqL
  obtain ⟨xx, hxx⟩ := UpperTheory.exists_h1Mu_of_locally_unit_times_power q X ⟨Prim.map ρ ζ⟩ hqX hcpt hnorm F hF
  have E := hA e2 e3 q k L (algebraMap k L) hq c 1
  obtain ⟨x₀, hx₀⟩ := (E 1).2 (pl q 1 pb.isoPullback.inv 1 xx)
  have hu : pl q 1 u 1 x₀ = xx := by
    rw [← pb.isoPullback_hom_fst, pl_comp]
    have h1 : pl q 1 (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) 1 x₀ =
      pl q 1 pb.isoPullback.inv 1 xx := hx₀
    rw [h1, ← pl_comp, Iso.hom_inv_id, pl_id]

  let gC := C.fromSpecStalk (genericPoint C)
  let hk : k →+* C.functionField := (Spec.preimage (gC ≫ c)).hom
  have hqA : IsUnit (q : C.functionField) := by simpa using hq.map hk
  have hqK : IsUnit (q : X.functionField) := by
    simpa using hqA.map φ
  have hqS : IsUnit (q : Γ(Spec C.functionField, ⊤)) := by
    simpa using hqA.map (Scheme.ΓSpecIso C.functionField).inv.hom
  have hqT : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hqK.map (Scheme.ΓSpecIso X.functionField).inv.hom
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q C.functionField hqA (fun c _ => Subsingleton.elim _ _) (pl q 1 gC 1 x₀)
  have K1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (Spec.map (CommRingCat.ofHom φ)) w hqS
  have K2 : kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) =
      kum q (Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w) := by
    rw [← hxx, ← hu, ← pl_comp, ← hφ, pl_comp]
    have h2 : pl q 1 (C.fromSpecStalk (genericPoint C)) 1 x₀ = kum q w := hw.symm
    rw [h2]
    exact K1
  let iX : (X.functionField)ˣ →* (Γ(Spec X.functionField, ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom
  let fK : (C.functionField)ˣ := Units.map (Scheme.ΓSpecIso C.functionField).hom.hom.toMonoidHom w
  let φu : (X.functionField)ˣ := Units.map φ.toMonoidHom fK
  have K3 : Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w = iX φu := by
    apply Units.ext
    have e : (Scheme.ΓSpecIso C.functionField).inv.hom
        ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))) = (w : Γ(Spec C.functionField, ⊤)) :=
      congrArg (fun m => m.hom (w : Γ(Spec C.functionField, ⊤))) (Scheme.ΓSpecIso C.functionField).hom_inv_id
    have h3 : (Scheme.ΓSpecIso X.functionField).inv.hom (φ ((fK : (C.functionField)ˣ) : C.functionField)) =
        (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso C.functionField).inv.hom
          ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤)))) :=
      congrArg (fun m => m.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    rw [e] at h3
    exact h3.symm
  have K4 : kum q (iX (F * φu⁻¹)) = 0 := by
    have h4 := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (iX (F * φu⁻¹)) (iX φu) hqT).1
    rw [← map_mul, inv_mul_cancel_right] at h4
    have h5 : kum q (iX F) = kum q (iX φu) := K2.trans (by rw [K3])
    rw [h5] at h4
    exact right_eq_add.mp h4
  obtain ⟨v, hv⟩ := UpperTheory.exists_root_of_kummer_class_eq_zero q (Spec X.functionField) (iX (F * φu⁻¹)) hqT K4
  let h : (X.functionField)ˣ := Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom v
  have hh : h ^ q = F * φu⁻¹ := by
    have e1 : h ^ q = Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom (v ^ q) := (map_pow _ v q).symm
    rw [e1, hv]
    apply Units.ext
    exact congrArg (fun m => m.hom (((F * φu⁻¹ : (X.functionField)ˣ)) : X.functionField))
      (Scheme.ΓSpecIso X.functionField).inv_hom_id
  refine ⟨fK, h, ?_⟩
  have h6 : F = φu * h ^ q := by rw [hh, mul_comm F, mul_inv_cancel_left]
  have h7 := congrArg Units.val h6
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at h7
  exact h7

end UpperTheory.PicRigid

theorem UpperTheory.baseChange_curve_functionField_comp_of_normal :
    Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q :=
  UpperTheory.PicRigid.main LateralTheory.Fin.AlgExt.intersectionNumber_baseChange
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective {k K L : Type} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
    (B : Subalgebra k K) : Function.Injective (inc L B) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := L) B.val.toLinearMap Subtype.val_injective

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve {E : Type*} [Field E] {f S T A D : E} {q : ℕ} (hS : S ≠ 0) (hD : D ≠ 0)
    (h : f * (S * D ^ q) = T * A ^ q) : f = T * S⁻¹ * (A * D⁻¹) ^ q := by
  have hDq : D ^ q ≠ 0 := pow_ne_zero _ hD
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination h

theorem UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit :
    Hyps → ∀ (q : ℕ) [NeZero q], ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ Charts k C.functionField q := by
  intro hH q _ k _ _ hq C _ c hc _ hgen
  obtain ⟨hff, n, B, hB, hX⟩ := UpperTheory.isFunctionField_and_chart_cover_of_isCurve k c hc hgen
  refine ⟨hff, n, B, hB, ?_⟩
  intro L _ _ _ F hF hloc
  obtain ⟨X, hXi, u, x, θ, hpb, hic, hcomm, hθ, hfrac, hloc'⟩ := hX L
  have hθF : θ F ≠ 0 := (map_ne_zero_iff θ hθ).mpr hF
  have key := UpperTheory.baseChange_curve_functionField_comp_of_normal hH q k L hq c hc u x hpb hic
    (θ.comp Algebra.TensorProduct.includeRight.toRingHom) hcomm (Units.mk0 (θ F) hθF) (by
      intro y
      obtain ⟨i, m, hm, hw⟩ := hloc' y
      obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal m hm.ne_top
      obtain ⟨s, t, a, b, hs, ht, ha, hb, he⟩ := hloc i M hM
      obtain ⟨ws, hws⟩ := hw s (fun h => hs (hmM h))
      obtain ⟨wt, hwt⟩ := hw t (fun h => ht (hmM h))
      have hinc := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective (L := L) (B i)
      have hne : ∀ z : L ⊗[k] ↥(B i), z ≠ 0 → θ (inc L (B i) z) ≠ 0 := fun z hz =>
        (map_ne_zero_iff θ hθ).mpr ((map_ne_zero_iff _ hinc).mpr hz)
      have hs0 : s ≠ 0 := fun h => hs (h ▸ M.zero_mem)
      have hA := hne a ha
      have hD := hne b hb
      have hS := hne s hs0
      refine ⟨wt * ws⁻¹, Units.mk0 (θ (inc L (B i) a) * (θ (inc L (B i) b))⁻¹) (mul_ne_zero hA (inv_ne_zero hD)), ?_⟩
      have h1 := congrArg θ he
      simp only [map_mul, map_pow] at h1
      rw [Units.val_mk0, Units.val_mk0, Units.val_mul, map_mul, map_units_inv, hws, hwt]
      exact UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve hS hD h1)
  obtain ⟨f, h, hfh⟩ := key
  rw [Units.val_mk0] at hfh
  obtain ⟨a, b, hb, hab⟩ := hfrac ↑h
  have hθb : θ b ≠ 0 := (map_ne_zero_iff θ hθ).mpr hb
  refine ⟨f, a, b, ?_, hb, ?_⟩
  · intro ha
    rw [ha, map_zero] at hab
    exact mul_ne_zero h.ne_zero hθb hab
  · apply hθ
    rw [map_mul, map_mul, map_pow, map_pow, ← hab, hfh]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply]
    ring
end
