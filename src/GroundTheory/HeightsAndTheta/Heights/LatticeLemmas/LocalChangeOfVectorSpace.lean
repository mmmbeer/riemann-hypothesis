import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HermitianDual

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.ComplexAt

noncomputable section

section Basic

variable {K : Type*} [Field K] [NumberField K]

def degOf {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) : ℝ :=
  arithDegree h / Module.finrank ℚ K

def deg (M : HermitianBundle K) : ℝ := degOf M.metric

def normAt {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ) (x : Fibre σ E) : ℝ :=
  ‖FibreSpace.equiv h σ x‖

def vecNorm {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ) (e : E) : ℝ :=
  ‖fibreVec h σ e‖

def fmap (σ : K →+* ℂ) {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup E']
    [Module (𝓞 K) E'] (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f

omit [NumberField K] in
theorem fmap_tmul (σ : K →+* ℂ) {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [AddCommGroup E'] [Module (𝓞 K) E'] (f : E' →ₗ[𝓞 K] E) (z : ComplexAt σ) (e : E') :
    fmap σ f (z ⊗ₜ e) = z ⊗ₜ f e := rfl

omit [NumberField K] in
theorem conjMap_fmap (σ : K →+* ℂ) {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [AddCommGroup E'] [Module (𝓞 K) E'] (f : E' →ₗ[𝓞 K] E) (x : Fibre σ E') :
    conjMap σ E (fmap σ f x) = fmap (conjugate σ) f (conjMap σ E' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [NumberField K] in

theorem conjMap_surjective (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] :
    Function.Surjective (conjMap σ E) := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul w e =>
    refine ⟨ofComplex σ (starRingEnd ℂ ((ofComplex (conjugate σ)).symm w)) ⊗ₜ e, ?_⟩
    rw [conjMap_tmul, conj_ofComplex, Complex.conj_conj]
    rfl
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end Basic

section Sub

variable {K : Type*} [Field K] [NumberField K]

def restrictedMetric (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) :
    HermitianMetric K F :=
  M.metric.comap F.subtype F.injective_subtype

def sub (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) : HermitianBundle K :=
  ⟨F, restrictedMetric M F⟩


end Sub

section Quotient

variable {K : Type*} [Field K] [NumberField K]

theorem isTorsionFree_quotient {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) : Module.IsTorsionFree (𝓞 K) (M.carrier ⧸ F) := by
  refine ⟨fun a ha z w hzw ↦ ?_⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective F z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective F w
  change a • Submodule.Quotient.mk x = a • Submodule.Quotient.mk y at hzw
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← smul_sub] at hzw
  exact (Submodule.Quotient.eq F).mpr (hF a _ ha0 hzw)

theorem projective_quotient {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) : Module.Projective (𝓞 K) (M.carrier ⧸ F) :=
  haveI := isTorsionFree_quotient hF
  projective_of_isTorsionFree _

variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier)

def subImage (σ : K →+* ℂ) : Submodule ℂ (FibreSpace M.metric σ) :=
  LinearMap.range ((FibreSpace.equiv M.metric σ).toLinearMap ∘ₗ fmap σ F.subtype)

def quotMap (σ : K →+* ℂ) : FibreSpace M.metric σ →ₗ[ℂ] Fibre σ (M.carrier ⧸ F) :=
  fmap σ F.mkQ ∘ₗ (FibreSpace.equiv M.metric σ).symm.toLinearMap

theorem quotMap_eq_zero_iff (σ : K →+* ℂ) (x : FibreSpace M.metric σ) :
    quotMap M F σ x = 0 ↔ x ∈ subImage M F σ := by
  have hex := Module.Flat.lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F)
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hex ((FibreSpace.equiv M.metric σ).symm x)).mp hx
    exact ⟨y, by
      change FibreSpace.equiv M.metric σ (F.subtype.lTensor (ComplexAt σ) y) = x
      rw [hy]; rfl⟩
  · rintro ⟨y, rfl⟩
    exact (hex _).mpr ⟨y, rfl⟩

theorem quotMap_surjective (σ : K →+* ℂ) : Function.Surjective (quotMap M F σ) := by
  intro ξ
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (Submodule.mkQ_surjective F) ξ
  exact ⟨FibreSpace.equiv M.metric σ y, hy⟩

theorem quotMap_perp_bijective (σ : K →+* ℂ) :
    Function.Bijective (quotMap M F σ ∘ₗ (subImage M F σ)ᗮ.subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h1 : (x : FibreSpace M.metric σ) ∈ subImage M F σ := (quotMap_eq_zero_iff M F σ _).mp hx
    have h2 : (x : FibreSpace M.metric σ) ∈ subImage M F σ ⊓ (subImage M F σ)ᗮ := ⟨h1, x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  · intro ξ
    obtain ⟨y, rfl⟩ := quotMap_surjective M F σ ξ
    have hy : y ∈ subImage M F σ ⊔ (subImage M F σ)ᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top
    obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    change quotMap M F σ x = quotMap M F σ (w + x)
    rw [map_add, (quotMap_eq_zero_iff M F σ w).mpr hw, zero_add]

def perpEquiv (σ : K →+* ℂ) : (subImage M F σ)ᗮ ≃ₗ[ℂ] Fibre σ (M.carrier ⧸ F) :=
  LinearEquiv.ofBijective _ (quotMap_perp_bijective M F σ)

theorem perpEquiv_apply (σ : K →+* ℂ) (x : (subImage M F σ)ᗮ) :
    perpEquiv M F σ x = quotMap M F σ x := rfl

theorem conj_mem_perp (σ : K →+* ℂ) (x : (subImage M F σ)ᗮ) :
    FibreSpace.equiv M.metric (conjugate σ)
        (conjMap σ M.carrier ((FibreSpace.equiv M.metric σ).symm x)) ∈
      (subImage M F (conjugate σ))ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨u, rfl⟩
  obtain ⟨u', rfl⟩ := conjMap_surjective σ F u
  change (M.metric.form (conjugate σ)).inner (fmap (conjugate σ) F.subtype (conjMap σ F u'))
    (conjMap σ M.carrier ((FibreSpace.equiv M.metric σ).symm x)) = 0
  rw [← conjMap_fmap, M.metric.form_conj]
  have h0 : inner ℂ (FibreSpace.equiv M.metric σ (fmap σ F.subtype u'))
      (x : FibreSpace M.metric σ) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range.mpr ⟨u', rfl⟩ : _ ∈ subImage M F σ) x.2
  change starRingEnd ℂ (inner ℂ (FibreSpace.equiv M.metric σ (fmap σ F.subtype u'))
    (FibreSpace.equiv M.metric σ ((FibreSpace.equiv M.metric σ).symm x))) = 0
  rw [LinearEquiv.apply_symm_apply, h0, map_zero]

theorem perpEquiv_symm_conj (σ : K →+* ℂ) (ξ : Fibre σ (M.carrier ⧸ F)) :
    (perpEquiv M F (conjugate σ)).symm (conjMap σ (M.carrier ⧸ F) ξ) =
      ⟨_, conj_mem_perp M F σ ((perpEquiv M F σ).symm ξ)⟩ := by
  apply (perpEquiv M F (conjugate σ)).injective
  rw [LinearEquiv.apply_symm_apply, perpEquiv_apply]
  change conjMap σ (M.carrier ⧸ F) ξ = fmap (conjugate σ) F.mkQ
    (conjMap σ M.carrier ((FibreSpace.equiv M.metric σ).symm ((perpEquiv M F σ).symm ξ)))
  rw [← conjMap_fmap]
  congr 1
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (perpEquiv M F σ) ξ]
  rfl

def quotientMetric (hF : M.Saturated F) :
    @HermitianMetric K _ _ (M.carrier ⧸ F) _ _ _ (projective_quotient hF) := by
  haveI := projective_quotient hF
  exact
    { form := fun σ ↦
        coreOfInjective (perpEquiv M F σ).symm.toLinearMap (perpEquiv M F σ).symm.injective
      form_conj := fun σ ξ η ↦ by
        simp only [coreOfInjective_inner, LinearEquiv.coe_coe, perpEquiv_symm_conj,
          Submodule.coe_inner]
        change (M.metric.form (conjugate σ)).inner (conjMap σ M.carrier _)
          (conjMap σ M.carrier _) = _
        rw [M.metric.form_conj]
        rfl }

def quotient (hF : M.Saturated F) : HermitianBundle K :=
  @HermitianBundle.mk K _ _ (M.carrier ⧸ F) _ _ _ (projective_quotient hF) (quotientMetric M F hF)

end Quotient

section BaseChange

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [Field E] [NumberField E] [Algebra K E]

variable (K) in

abbrev resEmb (τ : E →+* ℂ) : K →+* ℂ := τ.comp (algebraMap K E)

omit [NumberField K] [NumberField E] in
theorem coe_algebraMap_integers (a : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 E) a : 𝓞 E) : E) = algebraMap K E (a : K) := rfl

variable (K) in

def bcScalar (τ : E →+* ℂ) (z : ComplexAt τ) : 𝓞 E →ₗ[𝓞 K] ComplexAt (resEmb K τ) where
  toFun b := ofComplex _ (τ (b : E) * (ofComplex τ).symm z)
  map_add' b b' := by
    change (τ ((b + b' : 𝓞 E) : E) * _ : ℂ) = τ (b : E) * _ + τ (b' : E) * _
    push_cast; rw [map_add, add_mul]
  map_smul' a b := by
    rw [Algebra.smul_def]
    change τ ((algebraMap (𝓞 K) (𝓞 E) a : E) * (b : E)) * _ = τ (algebraMap K E (a : K)) * (τ (b : E) * _)
    rw [coe_algebraMap_integers, map_mul, mul_assoc]

omit [NumberField K] in
theorem bcScalar_apply (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) :
    bcScalar K τ z b = ofComplex _ (τ (b : E) * (ofComplex τ).symm z) := rfl

variable (M : HermitianBundle K)

def bcInner (τ : E →+* ℂ) (z : ComplexAt τ) :
    𝓞 E ⊗[𝓞 K] M.carrier →ₗ[𝓞 K] Fibre (resEmb K τ) M.carrier :=
  TensorProduct.map (bcScalar K τ z) LinearMap.id

theorem bcInner_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) (m : M.carrier) :
    bcInner M τ z (b ⊗ₜ m) = bcScalar K τ z b ⊗ₜ m := rfl

theorem bcInner_add (τ : E →+* ℂ) (z z' : ComplexAt τ) (t : 𝓞 E ⊗[𝓞 K] M.carrier) :
    bcInner M τ (z + z') t = bcInner M τ z t + bcInner M τ z' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul b m =>
    rw [bcInner_tmul, bcInner_tmul, bcInner_tmul, ← add_tmul]
    congr 1
    change (τ (b : E) * (ofComplex τ).symm (z + z') : ℂ) =
      τ (b : E) * (ofComplex τ).symm z + τ (b : E) * (ofComplex τ).symm z'
    rw [map_add, mul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

def bcAdd (τ : E →+* ℂ) : ComplexAt τ →+ (𝓞 E ⊗[𝓞 K] M.carrier →+ Fibre (resEmb K τ) M.carrier) :=
  AddMonoidHom.mk' (fun z ↦ (bcInner M τ z).toAddMonoidHom)
    (fun z z' ↦ AddMonoidHom.ext fun t ↦ bcInner_add M τ z z' t)

def bcFwdAdd (τ : E →+* ℂ) :
    Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) →+ Fibre (resEmb K τ) M.carrier :=
  TensorProduct.liftAddHom (bcAdd M τ) fun e z t ↦ by
    change bcInner M τ (e • z) t = bcInner M τ z (e • t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul b m =>
      rw [smul_tmul', bcInner_tmul, bcInner_tmul]
      congr 1
      change (τ (b : E) * (ofComplex τ).symm (ofComplex τ (τ (e : E)) * z) : ℂ) =
        τ ((e : E) * (b : E)) * (ofComplex τ).symm z
      rw [map_mul, map_mul, AlgEquiv.symm_apply_apply]; ring
    | add x y hx hy => rw [map_add, hx, hy, smul_add, map_add]

theorem bcFwdAdd_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (t : 𝓞 E ⊗[𝓞 K] M.carrier) :
    bcFwdAdd M τ (z ⊗ₜ t) = bcInner M τ z t := rfl

def bcFwd (τ : E →+* ℂ) :
    Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) →ₗ[ℂ] Fibre (resEmb K τ) M.carrier where
  toFun := bcFwdAdd M τ
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z x =>
      rw [smul_tmul', bcFwdAdd_tmul, bcFwdAdd_tmul, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul b m =>
        rw [bcInner_tmul, bcInner_tmul, smul_tmul']
        congr 1
        change (τ (b : E) * (ofComplex τ).symm (ofComplex τ c * z) : ℂ) =
          c * (τ (b : E) * (ofComplex τ).symm z)
        rw [map_mul, AlgEquiv.symm_apply_apply]; ring
      | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem bcFwd_tmul_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) (m : M.carrier) :
    bcFwd M τ (z ⊗ₜ (b ⊗ₜ m)) = bcScalar K τ z b ⊗ₜ m := rfl

def bcInv (τ : E →+* ℂ) :
    Fibre (resEmb K τ) M.carrier →+ Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun w ↦ AddMonoidHom.mk'
        (fun m ↦ ((ofComplex τ ((ofComplex (resEmb K τ)).symm w)) ⊗ₜ[𝓞 E]
          ((1 : 𝓞 E) ⊗ₜ[𝓞 K] m) : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)))
        (fun m m' ↦ by simp only [tmul_add]))
      (fun w w' ↦ AddMonoidHom.ext fun m ↦ by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_tmul]))
    fun a w m ↦ by
      simp only [AddMonoidHom.mk'_apply]
      have h1 : (ofComplex τ ((ofComplex (resEmb K τ)).symm (a • w)) : ComplexAt τ) =
          (algebraMap (𝓞 K) (𝓞 E) a) • ofComplex τ ((ofComplex (resEmb K τ)).symm w) := rfl
      rw [h1, TensorProduct.smul_tmul]
      congr 1
      rw [smul_tmul', ← TensorProduct.smul_tmul, algebraMap_smul]

theorem bcInv_bcFwd (τ : E →+* ℂ) (t : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)) :
    bcInv M τ (bcFwd M τ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z x =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b m =>
      rw [bcFwd_tmul_tmul]
      change (ofComplex τ (τ (b : E) * (ofComplex τ).symm z)) ⊗ₜ[𝓞 E] ((1 : 𝓞 E) ⊗ₜ[𝓞 K] m) = _
      have h1 : (ofComplex τ (τ (b : E) * (ofComplex τ).symm z) : ComplexAt τ) = b • z := rfl
      rw [h1, TensorProduct.smul_tmul, smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem bcFwd_injective (τ : E →+* ℂ) : Function.Injective (bcFwd M τ) := fun x y h ↦ by
  rw [← bcInv_bcFwd M τ x, ← bcInv_bcFwd M τ y, h]

theorem bcFwd_conj (τ : E →+* ℂ) (x : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)) :
    bcFwd M (conjugate τ) (conjMap τ _ x) = conjMap (resEmb K τ) M.carrier (bcFwd M τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b m =>
      rw [conjMap_tmul, bcFwd_tmul_tmul, bcFwd_tmul_tmul, conjMap_tmul]
      congr 1
      change (starRingEnd ℂ (τ (b : E)) * starRingEnd ℂ ((ofComplex τ).symm z) : ℂ) =
        starRingEnd ℂ (τ (b : E) * (ofComplex τ).symm z)
      rw [map_mul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

def baseChangeMetric : HermitianMetric E (𝓞 E ⊗[𝓞 K] M.carrier) where
  form τ := coreOfInjective ((FibreSpace.equiv M.metric (resEmb K τ)).toLinearMap ∘ₗ bcFwd M τ)
    (by rw [LinearMap.coe_comp]
        exact (FibreSpace.equiv M.metric (resEmb K τ)).injective.comp (bcFwd_injective M τ))
  form_conj τ x y := by
    have h := M.metric.form_conj (resEmb K τ) (bcFwd M τ x) (bcFwd M τ y)
    rw [← bcFwd_conj, ← bcFwd_conj] at h
    exact h

variable (E) in

def baseChange : HermitianBundle E := ⟨𝓞 E ⊗[𝓞 K] M.carrier, baseChangeMetric M⟩

end BaseChange

structure HermitianSpace (K : Type*) [Field K] (r : ℕ) where

  form : (K →+* ℂ) → InnerProductSpace.Core ℂ (Fin r → ℂ)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fin r → ℂ),
    (form (conjugate σ)).inner (star x) (star y) = starRingEnd ℂ ((form σ).inner x y)

section Space

variable {K : Type*} [Field K] [NumberField K]

theorem tmul_smul_field (σ : K →+* ℂ) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (z : ComplexAt σ) (c : K) (x : V) :
    z ⊗ₜ[𝓞 K] (c • x) = (ofComplex σ (σ c) * z) ⊗ₜ[𝓞 K] x := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hσd : σ (algebraMap (𝓞 K) K d) ≠ 0 := (map_ne_zero σ).mpr hd0
  set w : ComplexAt σ := ofComplex σ ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d)) with hw
  have hz : z = d • w := by
    rw [smul_def]
    change (ofComplex σ).symm z = σ (algebraMap (𝓞 K) K d) * ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d))
    field_simp
  have hx : d • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) • x) = a • x := by
    rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hd0, algebraMap_smul]
  rw [hz, TensorProduct.smul_tmul, hx, ← TensorProduct.smul_tmul]
  congr 1
  rw [smul_def, hw]
  change σ (algebraMap (𝓞 K) K a) * ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d)) =
    σ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) * (ofComplex σ).symm (d • w)
  rw [← hz, map_div₀]
  field_simp

def fieldCoordO (σ : K →+* ℂ) : Fibre σ K →ₗ[𝓞 K] ComplexAt σ :=
  TensorProduct.lift (LinearMap.mk₂ (𝓞 K) (fun z c ↦ ofComplex σ (σ c) * z)
    (fun z z' c ↦ mul_add _ _ _)
    (fun a z c ↦ by
      change ofComplex σ (σ c) * (ofComplex σ (σ (a : K)) * z) =
        ofComplex σ (σ (a : K)) * (ofComplex σ (σ c) * z)
      ring)
    (fun z c c' ↦ by rw [map_add, map_add, add_mul])
    (fun a z c ↦ by
      change ofComplex σ (σ ((a : K) * c)) * z = ofComplex σ (σ (a : K)) * (ofComplex σ (σ c) * z)
      rw [map_mul, map_mul, mul_assoc]))

def fieldCoord (σ : K →+* ℂ) : Fibre σ K →ₗ[ℂ] ℂ where
  toFun t := (ofComplex σ).symm (fieldCoordO σ t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z a =>
      rw [smul_tmul', RingHom.id_apply, smul_eq_mul]
      change (ofComplex σ).symm (ofComplex σ (σ a) * (ofComplex σ c * z)) =
        c * (ofComplex σ).symm (ofComplex σ (σ a) * z)
      simp only [map_mul, AlgEquiv.symm_apply_apply]; ring
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (r : ℕ)

def coordMap (σ : K →+* ℂ) : Fibre σ (Fin r → K) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.pi fun i ↦ fieldCoord σ ∘ₗ fmap σ (LinearMap.proj i)

variable {r}

theorem coordMap_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (v : Fin r → K) (i : Fin r) :
    coordMap r σ (z ⊗ₜ v) i = σ (v i) * (ofComplex σ).symm z := by
  change (ofComplex σ).symm (ofComplex σ (σ (v i)) * z) = _
  rw [map_mul, AlgEquiv.symm_apply_apply]

def coordInv (σ : K →+* ℂ) (w : Fin r → ℂ) : Fibre σ (Fin r → K) :=
  ∑ i, ofComplex σ (w i) ⊗ₜ[𝓞 K] (Pi.single i (1 : K) : Fin r → K)

theorem coordInv_coordMap (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordInv σ (coordMap r σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | tmul z v =>
    simp only [coordInv, coordMap_tmul]
    have h : ∀ i, ofComplex σ (σ (v i) * (ofComplex σ).symm z) ⊗ₜ[𝓞 K]
        (Pi.single i (1 : K) : Fin r → K) = z ⊗ₜ[𝓞 K] (v i • (Pi.single i (1 : K) : Fin r → K)) := by
      intro i
      rw [tmul_smul_field, map_mul, AlgEquiv.apply_symm_apply]
    simp only [h, ← tmul_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy =>
    rw [map_add]
    simp only [coordInv, Pi.add_apply, map_add, add_tmul, Finset.sum_add_distrib] at hx hy ⊢
    rw [hx, hy]

theorem coordMap_injective (σ : K →+* ℂ) : Function.Injective (coordMap r σ) := fun s t h ↦ by
  rw [← coordInv_coordMap σ s, ← coordInv_coordMap σ t, h]

def latticeMap (σ : K →+* ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Fibre σ L →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fmap σ L.subtype

theorem latticeMap_injective (σ : K →+* ℂ) (L : Submodule (𝓞 K) (Fin r → K)) :
    Function.Injective (latticeMap σ L) := by
  rw [latticeMap, LinearMap.coe_comp]
  exact (coordMap_injective σ).comp
    (Module.Flat.lTensor_preserves_injective_linearMap L.subtype L.injective_subtype)

theorem latticeMap_conj (σ : K →+* ℂ) (L : Submodule (𝓞 K) (Fin r → K)) (x : Fibre σ L) :
    latticeMap (conjugate σ) L (conjMap σ L x) = star (latticeMap σ L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul z l =>
    ext i
    rw [conjMap_tmul]
    change coordMap r (conjugate σ) (conj σ z ⊗ₜ (l : Fin r → K)) i =
      starRingEnd ℂ (coordMap r σ (z ⊗ₜ (l : Fin r → K)) i)
    rw [coordMap_tmul, coordMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]

def IsLattice (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤

omit [NumberField K] in
theorem finite_of_fg {L : Submodule (𝓞 K) (Fin r → K)} (hL : L.FG) : Module.Finite (𝓞 K) L :=
  Module.Finite.iff_fg.mpr hL

theorem projective_of_fg {L : Submodule (𝓞 K) (Fin r → K)} (hL : L.FG) :
    Module.Projective (𝓞 K) L :=
  haveI := finite_of_fg hL
  projective_of_isTorsionFree L

def HermitianSpace.latticeMetric (H : HermitianSpace K r) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) : @HermitianMetric K _ _ L _ _ (finite_of_fg hL) (projective_of_fg hL) :=
  @HermitianMetric.mk K _ _ L _ _ (finite_of_fg hL) (projective_of_fg hL)
    (fun σ ↦ coreComap (H.form σ) (latticeMap σ L) (latticeMap_injective σ L))
    (fun σ x y ↦ by
      rw [coreComap_inner, coreComap_inner, latticeMap_conj, latticeMap_conj, H.form_conj])

def HermitianSpace.lattice (H : HermitianSpace K r) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) : HermitianBundle K :=
  @HermitianBundle.mk K _ _ L _ _ (finite_of_fg hL) (projective_of_fg hL) (H.latticeMetric L hL)

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

open IsDedekindDomain.HeightOneSpectrum in

def locVec (x : Fin r → K) : Fin r → v.adicCompletion K :=
  fun i ↦ algebraMap K (v.adicCompletion K) (x i)

def localLattice (L : Submodule (𝓞 K) (Fin r → K)) :
    Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K) :=
  Submodule.span _ (locVec v '' (L : Set (Fin r → K)))

def IsLocalLattice (N : Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K)) :
    Prop :=
  N.FG ∧ Submodule.span (v.adicCompletion K) (N : Set (Fin r → v.adicCompletion K)) = ⊤

theorem locVec_smul (a : 𝓞 K) (x : Fin r → K) :
    locVec v (a • x) = (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) • locVec v x := by
  funext i
  change algebraMap K _ ((a : K) * x i) =
    ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
      v.adicCompletion K) * algebraMap K _ (x i)
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, map_mul]
  rfl

theorem locVec_zero : locVec v (0 : Fin r → K) = 0 := by funext i; simp [locVec]

theorem locVec_add (x y : Fin r → K) : locVec v (x + y) = locVec v x + locVec v y := by
  funext i; simp [locVec]

variable {v} in

def ofLocal (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K)) :
    Submodule (𝓞 K) (Fin r → K) where
  carrier := {x | ∀ v, locVec v x ∈ N v}
  add_mem' {x y} hx hy v := by
    rw [locVec_add]
    exact (N v).add_mem (hx v) (hy v)
  zero_mem' v := by
    rw [locVec_zero]
    exact (N v).zero_mem
  smul_mem' a x hx v := by
    rw [locVec_smul]
    exact (N v).smul_mem _ (hx v)

def glMap (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) →ₗ[v.adicCompletionIntegers K] (Fin r → v.adicCompletion K) :=
  (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K))).restrictScalars _

end Space

section Chain

variable {K : Type*} [Field K] [NumberField K]

theorem saturated_comap {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) (G : Submodule (𝓞 K) M.carrier) :
    (sub M G).Saturated (F.comap G.subtype) := fun a x ha hx ↦ hF a (G.subtype x) ha hx

def chainStep {M : HermitianBundle K} {k : ℕ} (C : Fin (k + 1) → Submodule (𝓞 K) M.carrier)
    (a : Fin k) : Submodule (𝓞 K) (sub M (C a.castSucc)).carrier :=
  (C a.succ).comap (C a.castSucc).subtype

end Chain

universe u v w

def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (E : Type w) [Field E] [NumberField E] [Algebra K E],
    deg (baseChange E M) = deg M

def Sublattice.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier),
    Module.finrank (𝓞 K) F = Module.finrank (𝓞 K) M.carrier →
    deg M = deg (sub M F) + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K ∧
      deg (sub M F) ≤ deg M

def LatticeOfLocalisations.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (r : ℕ),
    (∀ (M₁ : Submodule (𝓞 K) (Fin r → K)), IsLattice M₁ →
      ∀ (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K)),
        (∀ v, IsLocalLattice v (N v)) → {v | N v ≠ localLattice v M₁}.Finite →
        IsLattice (ofLocal N) ∧ ∀ v, localLattice v (ofLocal N) = N v) ∧
    ∀ (L L' : Submodule (𝓞 K) (Fin r → K)), IsLattice L → IsLattice L' →
      (L ≤ L' ↔ ∀ v, localLattice v L ≤ localLattice v L')

def LocalChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (r : ℕ) (H : HermitianSpace K r)
    (M₁ M₂ : Submodule (𝓞 K) (Fin r → K)) (h₁ : IsLattice M₁) (h₂ : IsLattice M₂)
    (g : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)),
    {v | g v ≠ 1}.Finite →
    (∀ v, localLattice v M₂ = (localLattice v M₁).map (glMap v (g v))) →
    deg (H.lattice M₂ h₂.1) = deg (H.lattice M₁ h₁.1) +
      (∑ᶠ v, Real.log ‖(g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det‖) /
        Module.finrank ℚ K

def NormComparison.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (E : Type v) [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E)
    (A : (K →+* ℂ) → ℝ),
    (∀ (σ : K →+* ℂ) (x : Fibre σ E), normAt h' σ x ≤ A σ * normAt h σ x) →
    degOf h - Module.finrank (𝓞 K) E * ∑ σ : K →+* ℂ, Real.log (A σ) / Module.finrank ℚ K ≤
      degOf h'

def DiagonalChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (E : Type v) [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E)
    (T : ∀ σ : K →+* ℂ, Fibre σ E →ₗ[ℂ] Fibre σ E),
    (∀ (σ : K →+* ℂ) (x : Fibre σ E), normAt h' σ x = normAt h σ (T σ x)) →
    (∀ σ : K →+* ℂ, ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (FibreSpace h σ)) (c : Fin n → ℂ),
      ∀ i, FibreSpace.equiv h σ (T σ ((FibreSpace.equiv h σ).symm (b i))) = c i • b i) →
    degOf h' = degOf h - ∑ σ : K →+* ℂ, Real.log ‖LinearMap.det (T σ)‖ / Module.finrank ℚ K

def ExactSequence.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F),
    deg M = deg (sub M F) + deg (quotient M F hF)

def QuotientNorm.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) (σ : K →+* ℂ) (x : Fibre σ M.carrier),
    normAt (quotient M F hF).metric σ (fmap σ F.mkQ x) =
      ⨅ y : {y : Fibre σ M.carrier // fmap σ F.mkQ y = fmap σ F.mkQ x}, normAt M.metric σ y

def ChainSum.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K) (k : ℕ)
    (C : Fin (k + 1) → Submodule (𝓞 K) M.carrier) (_ : C 0 = ⊤) (_ : Antitone C)
    (hC : ∀ a, M.Saturated (C a)),
    deg M = deg (sub M (C (Fin.last k))) +
      ∑ a : Fin k, deg (quotient (sub M (C a.castSucc)) (chainStep C a)
        (saturated_comap (hC a.succ) (C a.castSucc)))

def Hadamard.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (x : Fin (Module.finrank (𝓞 K) M.carrier) → M.carrier) (La : ℝ),
    LinearIndependent (𝓞 K) x → (∀ i (σ : K →+* ℂ), vecNorm M.metric σ (x i) ≤ La) →
    -(Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log La ≤ deg M

def HadamardQuotient.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) (S : Set M.carrier) (La : ℝ),
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) S) = Module.finrank (𝓞 K) M.carrier →
    (∀ x ∈ S, ∀ σ : K →+* ℂ, vecNorm M.metric σ x ≤ La) →
    -(Module.finrank (𝓞 K) (M.carrier ⧸ F) : ℝ) * Real.log La ≤ deg (quotient M F hF)

def HadamardMean.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (x : Fin (Module.finrank (𝓞 K) M.carrier) → M.carrier),
    LinearIndependent (𝓞 K) x →
    -(∑ i, ∑ σ : K →+* ℂ, Real.log (vecNorm M.metric σ (x i)) / Module.finrank ℚ K) ≤ deg M

def HadamardMeanQuotient.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) (ι : Type w) [Fintype ι] (x : ι → M.carrier),
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier →
    (∃ J : Finset ι, LinearIndependent (𝓞 K) (fun j : J ↦ F.mkQ (x j)) ∧
      J.card = Module.finrank (𝓞 K) (M.carrier ⧸ F)) ∧
    ∀ J : Finset ι, LinearIndependent (𝓞 K) (fun j : J ↦ F.mkQ (x j)) →
      J.card = Module.finrank (𝓞 K) (M.carrier ⧸ F) →
      -(∑ j ∈ J, ∑ σ : K →+* ℂ, Real.log (vecNorm M.metric σ (x j)) / Module.finrank ℚ K) ≤
        deg (quotient M F hF)

section Examples

variable (K : Type*) [Field K] [NumberField K]

abbrev firstLine : Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier := standardFlag K 1

theorem firstLine_saturated : (HermitianBundle.standard K 2).Saturated (firstLine K) :=
  standardFlag_saturated 1

def exampleSub : HermitianBundle K := sub (HermitianBundle.standard K 2) (firstLine K)

def exampleQuotient : HermitianBundle K :=
  quotient (HermitianBundle.standard K 2) (firstLine K) (firstLine_saturated K)

example : HermitianBundle ℚ := exampleSub ℚ
example : HermitianBundle GaussianField := exampleSub GaussianField
example : HermitianBundle ℚ := exampleQuotient ℚ
example : HermitianBundle GaussianField := exampleQuotient GaussianField
example : Algebra ℚ GaussianField := inferInstance

def stdVec (i : Fin 2) : (HermitianBundle.standard K 2).carrier := Pi.single i 1

theorem range_stdVec :
    Set.range (stdVec K) = Set.range (Pi.basisFun (𝓞 K) (Fin 2)) := by
  congr 1; funext i; rw [Pi.basisFun_apply]; rfl

theorem span_stdVec : Submodule.span (𝓞 K) (Set.range (stdVec K)) = ⊤ := by
  rw [range_stdVec]; exact (Pi.basisFun (𝓞 K) (Fin 2)).span_eq

theorem linearIndependent_stdVec : LinearIndependent (𝓞 K) (stdVec K) := by
  have h := (Pi.basisFun (𝓞 K) (Fin 2)).linearIndependent
  rwa [show ⇑(Pi.basisFun (𝓞 K) (Fin 2)) = stdVec K from
    funext fun i ↦ by rw [Pi.basisFun_apply]; rfl] at h

theorem vecNorm_stdVec (σ : K →+* ℂ) (i : Fin 2) :
    vecNorm (HermitianBundle.standard K 2).metric σ (stdVec K i) = 1 := by
  refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
  rw [one_pow, norm_fibreVec_sq]
  change (((HermitianMetric.standard K (Fin 2)).form σ).inner (1 ⊗ₜ Pi.single i 1)
    (1 ⊗ₜ Pi.single i 1)).re = 1
  rw [HermitianMetric.standard_inner_single]; rfl

theorem finrank_standard_two : Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier = 2 :=
  Module.finrank_fin_fun _

def stdFamily : Fin (Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier) →
    (HermitianBundle.standard K 2).carrier :=
  fun i ↦ stdVec K (Fin.cast (finrank_standard_two K) i)

theorem linearIndependent_stdFamily : LinearIndependent (𝓞 K) (stdFamily K) :=
  (linearIndependent_stdVec K).comp _ (Fin.cast_injective _)

def twiceLattice : Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  LinearMap.range ((2 : 𝓞 K) • LinearMap.id)

theorem twiceLattice_rank : Module.finrank (𝓞 K) (twiceLattice K) =
    Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier := by
  have hinj : Function.Injective
      ((2 : 𝓞 K) • LinearMap.id : (HermitianBundle.standard K 2).carrier →ₗ[𝓞 K] _) := by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    exact smul_right_injective _ two_ne_zero hxy
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm

theorem normAt_scale {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) (σ : K →+* ℂ)
    (x : Fibre σ E) : normAt (h.scale c hc) σ x = c * normAt h σ x := by
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hc.le (norm_nonneg _))).mp ?_
  show ‖FibreSpace.equiv (h.scale c hc) σ x‖ ^ 2 = (c * ‖FibreSpace.equiv h σ x‖) ^ 2
  rw [mul_pow, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
    FibreSpace.inner_equiv, FibreSpace.inner_equiv, HermitianMetric.scale_inner]
  exact Complex.re_ofReal_mul _ _

theorem normComparison_hyps {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) :
    ∀ (σ : K →+* ℂ) (x : Fibre σ E), normAt (h.scale 2 two_pos) σ x ≤ 2 * normAt h σ x :=
  fun σ x ↦ (normAt_scale K h 2 two_pos σ x).le

theorem diagonalChange_hyps {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) :
    (∀ (σ : K →+* ℂ) (x : Fibre σ E),
      normAt (h.scale 2 two_pos) σ x = normAt h σ (((2 : ℂ) • LinearMap.id : Fibre σ E →ₗ[ℂ] _) x)) ∧
    (∀ σ : K →+* ℂ, ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (FibreSpace h σ)) (c : Fin n → ℂ),
      ∀ i, FibreSpace.equiv h σ (((2 : ℂ) • LinearMap.id : Fibre σ E →ₗ[ℂ] _)
        ((FibreSpace.equiv h σ).symm (b i))) = c i • b i) := by
  refine ⟨fun σ x ↦ ?_, fun σ ↦ ⟨_, stdOrthonormalBasis ℂ (FibreSpace h σ), fun _ ↦ 2, fun i ↦ ?_⟩⟩
  · rw [normAt_scale]
    show 2 * ‖FibreSpace.equiv h σ x‖ =
      ‖FibreSpace.equiv h σ (((2 : ℂ) • LinearMap.id : Fibre σ E →ₗ[ℂ] _) x)‖
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, norm_smul]
    norm_num
  · rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]

def exampleChain : Fin 3 → Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  fun a ↦ standardFlag K a.rev

theorem exampleChain_hyps : exampleChain K 0 = ⊤ ∧ Antitone (exampleChain K) ∧
    ∀ a, (HermitianBundle.standard K 2).Saturated (exampleChain K a) :=
  ⟨rfl, fun _ _ hab ↦ standardFlag_monotone (Fin.rev_le_rev.mpr hab),
    fun _ ↦ standardFlag_saturated _⟩

theorem hadamard_hyps : LinearIndependent (𝓞 K) (stdFamily K) ∧
    ∀ i (σ : K →+* ℂ), vecNorm (HermitianBundle.standard K 2).metric σ (stdFamily K i) ≤ 1 :=
  ⟨linearIndependent_stdFamily K, fun _ σ ↦ (vecNorm_stdVec K σ _).le⟩

theorem hadamardQuotient_hyps :
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
      Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier ∧
    ∀ x ∈ Set.range (stdVec K), ∀ σ : K →+* ℂ,
      vecNorm (HermitianBundle.standard K 2).metric σ x ≤ 1 := by
  refine ⟨by rw [span_stdVec, finrank_top], ?_⟩
  rintro _ ⟨i, rfl⟩ σ
  exact (vecNorm_stdVec K σ i).le

def HermitianSpace.standard (r : ℕ) : HermitianSpace K r where
  form _ := coreOfInjective (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).symm.injective
  form_conj σ x y := by
    simp only [coreOfInjective_inner, LinearEquiv.coe_coe, PiLp.inner_apply, RCLike.inner_apply,
      map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change star (y i) * starRingEnd ℂ (star (x i)) = starRingEnd ℂ (y i) * x i
    simp

variable (r : ℕ)

def stdLattice : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin r ↦ (Pi.single i (1 : K) : Fin r → K))

omit [NumberField K] in
theorem isLattice_std : IsLattice (stdLattice K r) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), top_unique ?_⟩
  rw [← (Pi.basisFun K (Fin r)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

variable {K r}

theorem locVec_single (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (i : Fin r) :
    locVec v (Pi.single i (1 : K)) = Pi.single i 1 := by
  funext j; by_cases h : j = i
  · subst h; simp [locVec]
  · simp [locVec, h]

theorem localLattice_span (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (S : Set (Fin r → K)) :
    localLattice v (Submodule.span (𝓞 K) S) = Submodule.span _ (locVec v '' S) := by
  apply le_antisymm
  · rw [localLattice, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [locVec_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [locVec_add]; exact add_mem hy hz
    | smul a y _ hy => rw [locVec_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

variable (K r)

theorem isLocalLattice_std (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsLocalLattice v (localLattice v (stdLattice K r)) := by
  refine ⟨?_, top_unique ?_⟩
  · rw [stdLattice, localLattice_span]
    exact Submodule.fg_span ((Set.finite_range _).image _)
  · rw [← (Pi.basisFun (v.adicCompletion K) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨Pi.single i 1, Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    rw [locVec_single]; simp

theorem latticeOfLocalisations_hyps :
    IsLattice (stdLattice K r) ∧ (∀ v, IsLocalLattice v (localLattice v (stdLattice K r))) ∧
      {v | localLattice v (stdLattice K r) ≠ localLattice v (stdLattice K r)}.Finite :=
  ⟨isLattice_std K r, isLocalLattice_std K r, by simp⟩

open Classical in

def signChange (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) :=
  if v = v₀ then -1 else 1

theorem localChange_hyps (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    {v | signChange K r v₀ v ≠ 1}.Finite ∧
    ∀ v, localLattice v (stdLattice K r) =
      (localLattice v (stdLattice K r)).map (glMap v (signChange K r v₀ v)) := by
  refine ⟨(Set.finite_singleton v₀).subset fun v hv ↦ ?_, fun v ↦ ?_⟩
  · by_contra h
    exact hv (by rw [signChange, if_neg (by simpa using h)])
  · by_cases h : v = v₀
    · have : glMap v (signChange K r v₀ v) = -LinearMap.id := by
        rw [signChange, if_pos h]
        refine LinearMap.ext fun x ↦ ?_
        simp only [glMap, LinearMap.restrictScalars_apply, Units.val_neg, Units.val_one,
          Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec, LinearMap.neg_apply,
          LinearMap.id_apply]
      rw [this, Submodule.map_neg, Submodule.map_id]
    · have : glMap v (signChange K r v₀ v) = LinearMap.id := by
        rw [signChange, if_neg h]
        refine LinearMap.ext fun x ↦ ?_
        simp only [glMap, LinearMap.restrictScalars_apply, Units.val_one, Matrix.toLin'_apply,
          Matrix.one_mulVec, LinearMap.id_apply]
      rw [this, Submodule.map_id]

example : HermitianSpace ℚ 2 := HermitianSpace.standard ℚ 2
example : HermitianSpace GaussianField 2 := HermitianSpace.standard GaussianField 2
example : HermitianBundle ℚ := (HermitianSpace.standard ℚ 2).lattice (stdLattice ℚ 2) (isLattice_std ℚ 2).1
example : HermitianBundle GaussianField :=
  (HermitianSpace.standard GaussianField 2).lattice (stdLattice GaussianField 2)
    (isLattice_std GaussianField 2).1
example := latticeOfLocalisations_hyps ℚ 2
example := latticeOfLocalisations_hyps GaussianField 2
example := localChange_hyps ℚ 2
example := localChange_hyps GaussianField 2
example := twiceLattice_rank ℚ
example := twiceLattice_rank GaussianField
example := normComparison_hyps ℚ (HermitianBundle.standard ℚ 2).metric
example := normComparison_hyps GaussianField (HermitianBundle.standard GaussianField 2).metric
example := diagonalChange_hyps ℚ (HermitianBundle.standard ℚ 2).metric
example := diagonalChange_hyps GaussianField (HermitianBundle.standard GaussianField 2).metric
example := exampleChain_hyps ℚ
example := exampleChain_hyps GaussianField
example := hadamard_hyps ℚ
example := hadamard_hyps GaussianField
example := hadamardQuotient_hyps ℚ
example := hadamardQuotient_hyps GaussianField
example := firstLine_saturated ℚ
example := firstLine_saturated GaussianField

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt

universe u v

noncomputable section

set_option linter.unusedSectionVars false

namespace LocalChangeEq

def AAt (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] : Prop :=
  ∀ (Nm : HermitianNorms K V) (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    {v | g v ≠ 1}.Finite →
    (∀ v, (Heights.localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' Heights.localLattice v M₁.carrier) →
      (Nm.bundle M₂).deg = (Nm.bundle M₁).deg +
        (∑ᶠ v, Real.log ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖) /
          Module.finrank ℚ K

def BAt (K : Type*) [Field K] [NumberField K] (r : ℕ) : Prop :=
  ∀ (H : HermitianSpace K r)
    (M₁ M₂ : Submodule (𝓞 K) (Fin r → K)) (h₁ : IsLattice M₁) (h₂ : IsLattice M₂)
    (g : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)),
    {v | g v ≠ 1}.Finite →
    (∀ v, localLattice v M₂ = (localLattice v M₁).map (glMap v (g v))) →
    deg (H.lattice M₂ h₂.1) = deg (H.lattice M₁ h₁.1) +
      (∑ᶠ v, Real.log ‖(g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det‖) /
        Module.finrank ℚ K

variable {K : Type*} [Field K] [NumberField K]

theorem coordMap_coordInv (r : ℕ) (σ : K →+* ℂ) (w : Fin r → ℂ) :
    coordMap r σ (coordInv σ w) = w := by
  funext j
  simp only [coordInv, map_sum, Finset.sum_apply, coordMap_tmul, AlgEquiv.symm_apply_apply,
    Pi.single_apply]
  simp

theorem coordMap_conjMap (r : ℕ) (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordMap r (conjugate σ) (conjMap σ (Fin r → K) t) = star (coordMap r σ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul z l =>
    ext i
    rw [conjMap_tmul]
    change coordMap r (conjugate σ) (conj σ z ⊗ₜ l) i = starRingEnd ℂ (coordMap r σ (z ⊗ₜ l) i)
    rw [coordMap_tmul, coordMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))

def intEquiv : V ≃ₗ[𝓞 K] (Fin r → K) := φ.restrictScalars (𝓞 K)

def fibreCoord (σ : K →+* ℂ) : Fibre σ V →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fibreMap σ (intEquiv φ).toLinearMap

theorem fibreCoord_bijective (σ : K →+* ℂ) : Function.Bijective (fibreCoord φ σ) := by
  refine ⟨(coordMap_injective σ).comp (fibreMap_injective σ (intEquiv φ).injective), ?_⟩
  intro w
  obtain ⟨t, ht⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (intEquiv φ).surjective (coordInv σ w)
  refine ⟨t, ?_⟩
  show coordMap r σ (((intEquiv φ).toLinearMap).lTensor (ComplexAt σ) t) = w
  rw [ht, coordMap_coordInv]

theorem fibreCoord_conjMap (σ : K →+* ℂ) (x : Fibre σ V) :
    fibreCoord φ (conjugate σ) (conjMap σ V x) = star (fibreCoord φ σ x) := by
  simp only [fibreCoord, LinearMap.comp_apply]
  rw [← conjMap_fibreMap, coordMap_conjMap]

def fibreCoordEquiv (σ : K →+* ℂ) : Fibre σ V ≃ₗ[ℂ] (Fin r → ℂ) :=
  LinearEquiv.ofBijective (fibreCoord φ σ) (fibreCoord_bijective φ σ)

theorem fibreCoordEquiv_symm_star (σ : K →+* ℂ) (w : Fin r → ℂ) :
    (fibreCoordEquiv φ (conjugate σ)).symm (star w) = conjMap σ V ((fibreCoordEquiv φ σ).symm w) := by
  rw [LinearEquiv.symm_apply_eq]
  change star w = fibreCoord φ (conjugate σ) (conjMap σ V _)
  rw [fibreCoord_conjMap]
  congr 1
  exact ((fibreCoordEquiv φ σ).apply_symm_apply w).symm

def normsOf (H : HermitianSpace K r) : HermitianNorms K V where
  form σ := coreComap (H.form σ) (fibreCoord φ σ) (fibreCoord_bijective φ σ).1
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, fibreCoord_conjMap, fibreCoord_conjMap, H.form_conj]

def spaceOf (Nm : HermitianNorms K V) : HermitianSpace K r where
  form σ := coreComap (Nm.form σ) (fibreCoordEquiv φ σ).symm.toLinearMap
    (fibreCoordEquiv φ σ).symm.injective
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner]
    simp only [LinearEquiv.coe_coe]
    rw [fibreCoordEquiv_symm_star, fibreCoordEquiv_symm_star, Nm.form_conj]

theorem normsOf_inner (H : HermitianSpace K r) (σ : K →+* ℂ) (x y : V) :
    ((normsOf φ H).form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (H.form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x)) (coordMap r σ (1 ⊗ₜ φ y)) := rfl

theorem spaceOf_inner (Nm : HermitianNorms K V) (σ : K →+* ℂ) (x y : V) :
    (Nm.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      ((spaceOf φ Nm).form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x))
        (coordMap r σ (1 ⊗ₜ φ y)) := by
  have h : ∀ z : V, (fibreCoordEquiv φ σ).symm (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ z)) =
      (1 : ComplexAt σ) ⊗ₜ z := fun z ↦ by
    rw [LinearEquiv.symm_apply_eq]; rfl
  change _ = (Nm.form σ).inner ((fibreCoordEquiv φ σ).symm _) ((fibreCoordEquiv φ σ).symm _)
  rw [h, h]

theorem deg_bundle_eq (Nm : HermitianNorms K V) (H : HermitianSpace K r)
    (hrel : ∀ (σ : K →+* ℂ) (x y : V), (Nm.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (H.form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x)) (coordMap r σ (1 ⊗ₜ φ y)))
    (L : FullLattice K V) (hL : (L.carrier.map (intEquiv φ).toLinearMap).FG) :
    (Nm.bundle L).deg = deg (H.lattice (L.carrier.map (intEquiv φ).toLinearMap) hL) := by
  unfold HermitianBundle.deg deg degOf HermitianBundle.arithDegree
  congr 1
  refine GroundTheory.Heights₂.Heights.LatticeLemmas.arithDegree_congr _ _
    (Submodule.equivMapOfInjective _ (intEquiv φ).injective L.carrier) fun σ x y ↦ ?_
  exact hrel σ (Subtype.val (p := (· ∈ L.carrier)) x) (Subtype.val (p := (· ∈ L.carrier)) y)

theorem deg_lattice_congr (H : HermitianSpace K r) {M M' : Submodule (𝓞 K) (Fin r → K)} (e : M = M')
    (h : M.FG) (h' : M'.FG) : deg (H.lattice M h) = deg (H.lattice M' h') := by
  subst e; rfl

theorem fg_map (L : Submodule (𝓞 K) V) (hL : L.FG) : (L.map (intEquiv φ).toLinearMap).FG :=
  hL.map _

theorem span_map (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span K ((L.map (intEquiv φ).toLinearMap : Submodule (𝓞 K) (Fin r → K)) :
      Set (Fin r → K)) = ⊤ := by
  rw [Submodule.map_coe]
  change Submodule.span K (φ.toLinearMap '' (L : Set V)) = ⊤
  rw [Submodule.span_image, hL, Submodule.map_top, LinearEquiv.range]

theorem isLattice_map (L : FullLattice K V) : IsLattice (L.carrier.map (intEquiv φ).toLinearMap) :=
  ⟨fg_map φ _ L.fg, span_map φ _ L.span_eq⟩

def pullLattice (M : Submodule (𝓞 K) (Fin r → K)) (hM : IsLattice M) : FullLattice K V where
  carrier := M.map (intEquiv φ).symm.toLinearMap
  fg := hM.1.map _
  span_eq := by
    rw [Submodule.map_coe]
    change Submodule.span K (φ.symm.toLinearMap '' (M : Set (Fin r → K))) = ⊤
    rw [Submodule.span_image, hM.2, Submodule.map_top, LinearEquiv.range]

theorem map_pullLattice (M : Submodule (𝓞 K) (Fin r → K)) (hM : IsLattice M) :
    (pullLattice φ M hM).carrier.map (intEquiv φ).toLinearMap = M := by
  show Submodule.map (intEquiv φ).toLinearMap (Submodule.map (intEquiv φ).symm.toLinearMap M) = M
  rw [← Submodule.map_comp]
  have : (intEquiv φ).toLinearMap ∘ₗ (intEquiv φ).symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x ↦ (intEquiv φ).apply_symm_apply x
  rw [this, Submodule.map_id]

theorem finiteDimensional (M : FullLattice K V) : FiniteDimensional K V := by
  obtain ⟨S, hS⟩ := M.fg
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff, ← M.span_eq, Submodule.span_le]
  intro x hx
  rw [SetLike.mem_coe, ← hS] at hx
  exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx

variable (v : HeightOneSpectrum (𝓞 K))

def localEquiv : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  (LinearEquiv.baseChange K (v.adicCompletion K) V (Fin r → K) φ).trans
    (TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) (Fin r))

theorem localEquiv_toLocal (x : V) : localEquiv φ v (Heights.toLocal v x) = locVec v (φ x) := by
  funext i
  simp [localEquiv, Heights.toLocal, locVec, Algebra.algebraMap_eq_smul_one]

theorem image_localLattice (L : Submodule (𝓞 K) V) :
    localEquiv φ v '' (Heights.localLattice v L : Set (v.adicCompletion K ⊗[K] V)) =
      (localLattice v (L.map (intEquiv φ).toLinearMap) : Set (Fin r → v.adicCompletion K)) := by
  let f := (localEquiv φ v).toLinearMap.restrictScalars (v.adicCompletionIntegers K)
  have hf : ⇑(localEquiv φ v) = ⇑f := rfl
  rw [hf, Heights.localLattice, ← Submodule.map_coe, Submodule.map_span, localLattice,
    Submodule.map_coe, Set.image_image]
  congr 2
  ext w
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, ⟨x, hx, rfl⟩, (localEquiv_toLocal φ v x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, localEquiv_toLocal φ v x⟩

def glEquiv (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (Matrix.toLin' ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
      Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

theorem glEquiv_apply (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K))
    (x : Fin r → v.adicCompletion K) : glEquiv v g x = glMap v g x := rfl

theorem glEquiv_one : glEquiv v (1 : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) = 1 := by
  ext x i
  simp [glEquiv]

theorem det_glEquiv (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    LinearMap.det (glEquiv v g : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) =
      (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det :=
  LinearMap.det_toLin' _

def glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :
    Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) where
  val := LinearMap.toMatrix' (f : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _)
  inv := LinearMap.toMatrix' (f.symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _)
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    exact LinearMap.ext fun x ↦ f.apply_symm_apply x
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    exact LinearMap.ext fun x ↦ f.symm_apply_apply x

theorem glMap_glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K))
    (x : Fin r → v.adicCompletion K) : glMap v (glOf v f) x = f x := by
  change Matrix.toLin' (LinearMap.toMatrix' (f : _ →ₗ[v.adicCompletion K] _)) x = f x
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem glOf_one : glOf v (1 : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] _) = 1 := by
  ext : 1
  change LinearMap.toMatrix' LinearMap.id = 1
  exact LinearMap.toMatrix'_id

theorem det_glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :
    (glOf v f : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det =
      LinearMap.det (f : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) :=
  LinearMap.det_toMatrix' _

include φ in

theorem bAt_of_aAt (hA : AAt K V) : BAt K r := by
  intro H M₁ M₂ h₁ h₂ g hg hloc
  set gA : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V) :=
    fun v ↦ (localEquiv φ v).trans ((glEquiv v (g v)).trans (localEquiv φ v).symm) with hgA
  have hfin : {v | gA v ≠ 1}.Finite := by
    refine hg.subset fun v hv h1 ↦ hv ?_
    refine LinearEquiv.ext fun x ↦ ?_
    simp [hgA, h1, glEquiv_one]
  have hloc' : ∀ v, (Heights.localLattice v (pullLattice φ M₂ h₂).carrier :
      Set (v.adicCompletion K ⊗[K] V)) = gA v '' Heights.localLattice v (pullLattice φ M₁ h₁).carrier := by
    intro v
    apply Set.image_injective.mpr (localEquiv φ v).injective
    rw [image_localLattice, map_pullLattice, hloc v, Set.image_image]
    have : (fun x ↦ localEquiv φ v (gA v x)) = glMap v (g v) ∘ localEquiv φ v := by
      funext x
      simp only [hgA, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Function.comp_apply,
        glEquiv_apply]
    rw [this, Set.image_comp, image_localLattice, map_pullLattice, Submodule.map_coe]
  have key := hA (normsOf φ H) (pullLattice φ M₁ h₁) (pullLattice φ M₂ h₂) gA hfin hloc'
  rw [deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1,
    deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1,
    deg_lattice_congr H (map_pullLattice φ M₂ h₂) _ h₂.1,
    deg_lattice_congr H (map_pullLattice φ M₁ h₁) _ h₁.1] at key
  have hdet : ∀ v, LinearMap.det (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V)) = (g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det := by
    intro v
    have : (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
        ((localEquiv φ v).symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ
          (glEquiv v (g v) : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ
          ((localEquiv φ v).symm.symm : _ →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, LinearMap.det_conj, det_glEquiv]
  simp only [hdet] at key
  exact key

include φ in

theorem aAt_of_bAt (hB : BAt K r) : AAt K V := by
  intro Nm L₁ L₂ g hg hloc
  set gB : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) :=
    fun v ↦ glOf v ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v))) with hgB
  have hfin : {v | gB v ≠ 1}.Finite := by
    refine hg.subset fun v hv h1 ↦ hv ?_
    have : (localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) = 1 :=
      LinearEquiv.ext fun x ↦ by simp [h1]
    simp only [hgB, this, glOf_one]
  have hloc' : ∀ v, localLattice v (L₂.carrier.map (intEquiv φ).toLinearMap) =
      (localLattice v (L₁.carrier.map (intEquiv φ).toLinearMap)).map (glMap v (gB v)) := by
    intro v
    apply SetLike.coe_injective
    rw [Submodule.map_coe, ← image_localLattice, ← image_localLattice, hloc v, ← Set.image_comp,
      ← Set.image_comp]
    congr 1
    funext x
    simp only [hgB, Function.comp_apply, glMap_glOf, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have hM₁ := isLattice_map φ L₁
  have hM₂ := isLattice_map φ L₂
  have key := hB (spaceOf φ Nm) _ _ hM₁ hM₂ gB hfin hloc'
  rw [deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₂ hM₂.1,
    deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₁ hM₁.1, key]
  have hdet : ∀ v, (gB v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det =
      LinearMap.det (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
        (v.adicCompletion K ⊗[K] V)) := by
    intro v
    simp only [hgB]
    rw [det_glOf]
    have : ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) :
        (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) =
        (localEquiv φ v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ
          (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ
          ((localEquiv φ v).symm : _ →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, LinearMap.det_conj]
  simp only [hdet]

end LocalChangeEq

open LocalChangeEq in

theorem LocalChange.kleimanNef_field_of_alt (hB : LocalChange.Statement.{u}) :
    GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ Nm M₁ M₂ g hg hloc
  have : FiniteDimensional K V := finiteDimensional M₁
  exact aAt_of_bAt (Module.finBasis K V).equivFun (hB K _) Nm M₁ M₂ g hg hloc

open LocalChangeEq in

theorem LocalChange.localChange_of_vectorSpace (hA : GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, max u v}) :
    LocalChange.Statement.{u} := by
  intro K _ _ r
  exact bAt_of_aAt (V := ULift.{v} (Fin r → K)) ULift.moduleEquiv (hA K (ULift.{v} (Fin r → K)))

theorem LocalChange.equiv :
    GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, max u v} ↔
      LocalChange.Statement.{u} :=
  ⟨LocalChange.localChange_of_vectorSpace, LocalChange.kleimanNef_field_of_alt⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
end
