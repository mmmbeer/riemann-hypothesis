import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemKFinOfIsLocallyConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsotropicComplGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCompactUnderWittChart
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantLinOm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift

section
noncomputable section

open GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace GlobalTheory.LocSW.Lin

section Alg

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {δ : A} {β ν κ : Type} [Fintype β]
  [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ] {JB : Matrix β β A} [Invertible (2 : k)]

theorem algebraMap_trace (h : IsQuad c δ) (z : A) : algebraMap k A (Algebra.trace k A z) = z + c z := by
  obtain ⟨b, h0, h1⟩ := h.basis
  have h2 : ∀ x : k, Algebra.trace k A (algebraMap k A x) = 2 * x := fun x => by
    rw [Algebra.trace_algebraMap_of_basis b]; simp
  have h3 : Algebra.trace k A δ = 0 := by
    obtain ⟨x, y, e⟩ := h.exists_eq (δ * δ)
    have e0 : δ * b 0 = (0 : k) • b 0 + (1 : k) • b 1 := by rw [h0, h1]; simp
    have e1 : δ * b 1 = x • b 0 + y • b 1 := by rw [h0, h1, e, Algebra.smul_def, Algebra.smul_def, mul_one]
    have hn := h.algebraMap_norm (1 + δ)
    have hn' := h.algebraMap_norm δ
    rw [Algebra.norm_eq_matrix_det b, det_fin_two] at hn hn'
    rw [Algebra.trace_eq_matrix_trace b, trace_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, add_mul, one_mul, e0, e1] at hn hn' ⊢
    simp [h.anti] at hn hn' ⊢
    apply h.algebraMap_injective
    rw [map_zero]
    linear_combination hn + hn'
  obtain ⟨x, y, rfl⟩ := h.exists_eq z
  rw [map_add, h2, ← Algebra.smul_def, map_smul, h3, map_add c, map_smul, h.anti, c.commutes]
  simp [two_mul]
  ring

theorem trace_conj (h : IsQuad c δ) (z : A) : Algebra.trace k A (c z) = Algebra.trace k A z :=
  h.algebraMap_injective (by rw [algebraMap_trace h, algebraMap_trace h, h.invol, add_comm])

theorem eq_zero_of_trace (h : IsQuad c δ) {z : A} (hz : ∀ a, Algebra.trace k A (a * z) = 0) : z = 0 := by
  have h1 := algebraMap_trace h (1 * z)
  have h2 := algebraMap_trace h (δ * z)
  rw [hz, map_zero, map_mul] at h1 h2
  rw [h.anti] at h2
  rw [map_one] at h1
  have h3 : algebraMap k A (⅟(2 : k)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap k A) 2, ← map_mul, invOf_mul_self, map_one]
  refine h.unit.mul_right_eq_zero.1 ?_
  linear_combination (-algebraMap k A (⅟(2 : k))) * h2 - algebraMap k A (⅟(2 : k)) * δ * h1 - δ * z * h3

variable (c JB) in

def trB : LinearMap.BilinForm k (β → A) :=
  LinearMap.mk₂ k (fun u v => -Algebra.trace k A (u ⬝ᵥ JB *ᵥ fun i => c (v i)))
    (fun u u' v => by rw [add_dotProduct, map_add, neg_add])
    (fun a u v => by rw [smul_dotProduct, map_smul, smul_neg])
    (fun u v v' => by
      rw [← neg_add, ← map_add, ← dotProduct_add, ← mulVec_add]; congr 4; funext i; simp)
    (fun a u v => by
      rw [smul_neg, ← map_smul, ← dotProduct_smul, ← mulVec_smul]; congr 4; funext i; simp)

omit [DecidableEq β] [Invertible (2 : k)] in

theorem trB_apply (u v : β → A) : trB c JB u v = -Algebra.trace k A (u ⬝ᵥ JB *ᵥ fun i => c (v i)) := rfl

omit [DecidableEq β] [Invertible (2 : k)] in

theorem trB_mulVec {γ γ' : Type} [Fintype γ] [Fintype γ'] (M : Matrix β γ A) (N : Matrix β γ' A) (u : γ → A) (v : γ' → A) :
    trB c JB (M *ᵥ u) (N *ᵥ v) = -Algebra.trace k A (u ⬝ᵥ (Mᵀ * JB * N.map c) *ᵥ fun i => c (v i)) := by
  have e : (fun i => c ((N *ᵥ v) i)) = N.map c *ᵥ fun i => c (v i) := funext fun i => RingHom.map_mulVec c.toRingHom N v i
  rw [trB_apply, e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]

omit [DecidableEq β] in

theorem symp_eq (hq : IsQuad c δ) (hJ : ∀ i j, c (JB j i) = -JB i j) (x y : Matrix (Fin 2) β A) :
    WeilM.symp c (-1) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) JB x y = trB c JB (x 0) (y 1) - trB c JB (y 0) (x 1) := by
  rw [trB_apply, trB_apply, ← trace_conj hq (y 0 ⬝ᵥ _), ← map_neg, ← map_neg, ← map_sub, WeilM.symp]
  congr 1
  simp only [hTens, Fin.sum_univ_two, dotProduct, mulVec, map_sum, map_mul, hq.invol, hJ, Finset.mul_sum]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero, mul_one, ← Finset.mul_sum, neg_mul, one_mul, sub_neg_eq_add, neg_add]
  congr 1
  · simp only [Finset.mul_sum, mul_assoc]
  · rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_coord (hq : IsQuad c δ) (hJ : ∀ i j, c (JB j i) = -JB i j) (hu : IsUnit JB.det) :
    ∃ (d : ℕ) (e : (β → A) ≃ₗ[k] (Fin d → k))
      (co : Darboux (WeilM.symp c (-1) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) JB) (Fin d)),
      ∀ x, (co.e x).1 = e (x 0) ∧ ∀ u, e u ⬝ᵥ (co.e x).2 = trB c JB u (x 1) := by
  obtain ⟨b, -, -⟩ := hq.basis
  have := Module.Finite.of_basis b
  let ε := Module.finBasis k (β → A)
  let f : (β → A) →ₗ[k] (Fin _ → k) := LinearMap.pi fun i => trB c JB (ε i)
  have hf : ∀ u v, ε.equivFun u ⬝ᵥ f v = trB c JB u v := fun u v => by
    conv_rhs => rw [← ε.sum_equivFun u]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    rfl
  have hi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv => by
    have h0 : ∀ u, trB c JB u v = 0 := fun u => by rw [← hf, hv, dotProduct_zero]
    have h1 : (JB *ᵥ fun i => c (v i)) = 0 := funext fun i => eq_zero_of_trace hq fun a => by
      have := h0 (Pi.single i a)
      rwa [trB_apply, single_dotProduct, neg_eq_zero] at this
    have h2 := congrArg (JB⁻¹ *ᵥ ·) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, mulVec_zero] at h2
    funext i
    rw [← hq.invol (v i), congrFun h2 i, Pi.zero_apply, map_zero]
  let f' := LinearMap.linearEquivOfInjective f hi (by simp)
  refine ⟨_, ε.equivFun, ⟨(LinearEquiv.finTwoArrow k (β → A)).trans (ε.equivFun.prodCongr f'), fun x y => ?_⟩,
    fun x => ⟨rfl, fun u => hf u _⟩⟩
  rw [symp_eq hq hJ, ← hf, ← hf]
  rfl

def actC (e : (β → A) ≃ₗ[k] (κ → k)) (g : GL β A) : (κ → k) →ₗ[k] (κ → k) :=
  e.toLinearMap ∘ₗ (Matrix.toLin' g.val).restrictScalars k ∘ₗ e.symm.toLinearMap

omit [Fintype κ] [Invertible (2 : k)]

theorem actC_apply (e : (β → A) ≃ₗ[k] (κ → k)) (g : GL β A) (u : β → A) : actC e g (e u) = e (g.val *ᵥ u) := by simp [actC]

theorem actC_actC (e : (β → A) ≃ₗ[k] (κ → k)) (g g' : GL β A) (x : κ → k) :
    actC e g (actC e g' x) = actC e (g * g') x := by simp [actC]

theorem actC_one (e : (β → A) ≃ₗ[k] (κ → k)) (x : κ → k) : actC e 1 x = x := by simp [actC]

variable (c JB) in

def linOm (e : (β → A) ≃ₗ[k] (κ → k)) : UG c JB →* Module.End ℂ ((κ → k) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ (actC e (h : GL β A)⁻¹)
  map_one' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_one]
  map_mul' h h' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_actC]

theorem linOm_apply (e : (β → A) ≃ₗ[k] (κ → k)) (h : UG c JB) (φ : (κ → k) → ℂ) (x : κ → k) :
    linOm c JB e h φ x = φ (actC e (h : GL β A)⁻¹ x) := rfl

theorem linOm_impl [Fintype κ] [Invertible (2 : k)] (ψ : AddChar k ℂ) (e : (β → A) ≃ₗ[k] (κ → k))
    (co : Darboux (WeilM.symp c (-1) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) JB) κ)
    (hco : ∀ x, (co.e x).1 = e (x 0) ∧ ∀ u, e u ⬝ᵥ (co.e x).2 = trB c JB u (x 1))
    (h : UG c JB) (w : Matrix (Fin 2) β A) (φ : (κ → k) → ℂ) :
    linOm c JB e h (co.rho ψ w φ) = co.rho ψ (actB c h w) (linOm c JB e h φ) := by
  funext x
  obtain ⟨u, rfl⟩ := e.surjective x
  have hr : ∀ i, actB c h w i = (h : GL β A).val *ᵥ w i := fun i => by
    funext j; simp [actB, mul_apply, mulVec, dotProduct, mul_comm]
  have h0 : ∀ u v, trB c JB ((h : GL β A).val *ᵥ u) ((h : GL β A).val *ᵥ v) = trB c JB u v := fun u v => by
    rw [trB_mulVec, show (h : GL β A).valᵀ * JB * (h : GL β A).val.map c = JB from h.2, trB_apply]
  have h1 : trB c JB u ((h : GL β A).val *ᵥ w 1) = trB c JB (((h : GL β A)⁻¹).val *ᵥ u) (w 1) := by
    rw [← h0 (_ *ᵥ u), mulVec_mulVec, Units.mul_inv, one_mulVec]
  simp only [linOm_apply, Darboux.rho, schr, (hco _).1, (hco _).2, actC_apply, ← map_add e, hr, h0, h1, mulVec_add,
    mulVec_mulVec, Units.inv_mul, one_mulVec]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {δ : A} {β ν κ : Type} [Fintype β]
  [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ] {JB : Matrix β β A} {ψ : AddChar k ℂ}

theorem linOm_mem (e : (β → A) ≃ₗ[k] (κ → k)) (h : UG c JB) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    linOm c JB e h φ ∈ SB (κ → k) := by
  let a : (κ → k) ≃ₜ (κ → k) :=
    { toFun := actC e (h : GL β A)⁻¹
      invFun := actC e (h : GL β A)
      left_inv := fun x => by rw [actC_actC, mul_inv_cancel, actC_one]
      right_inv := fun x => by rw [actC_actC, inv_mul_cancel, actC_one]
      continuous_toFun := LinearMap.continuous_on_pi _
      continuous_invFun := LinearMap.continuous_on_pi _ }
  exact ⟨hφ.1.comp_continuous a.continuous, hφ.2.comp_homeomorph a⟩

theorem isLocallyConstant_linOm [TopologicalSpace A] [IsModuleTopology k A] (hq : IsQuad c δ)
    (e : (β → A) ≃ₗ[k] (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    IsLocallyConstant fun h : UG c JB => linOm c JB e h φ := by
  obtain ⟨b, -, -⟩ := hq.basis
  have := Module.Finite.of_basis b
  have := IsModuleTopology.isTopologicalRing k A
  have := IsModuleTopology.toContinuousAdd k A
  refine isLocallyConstant_orbit _ ?_
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := LinearMap.continuous_on_pi e.symm.toLinearMap
  have hc : ∀ M : UG c JB → GL β A, Continuous M → Continuous fun q : UG c JB × (κ → k) => actC e (M q.1) q.2 :=
    fun M hM => by
      have c3 : Continuous fun q : UG c JB × (κ → k) => (M q.1).val := Units.continuous_val.comp (hM.comp continuous_fst)
      have c4 : Continuous fun q : UG c JB × (κ → k) => e.symm q.2 := c2.comp continuous_snd
      exact (c1.comp (c3.matrix_mulVec c4)).congr fun q => by simp [actC]
  have c5 : Continuous fun p : UG c JB => (p : GL β A) := continuous_subtype_val
  filter_upwards [eventually_comp_eq (p₀ := (1 : UG c JB)) (fun p v => actC e (p : GL β A)⁻¹ v)
    (fun p v => actC e (p : GL β A) v) (hc (fun p => (p : GL β A)⁻¹) c5.inv) (hc (fun p => (p : GL β A)) c5)
    (by simp [actC_one]) (by simp [actC_one]) (fun p v => by rw [actC_actC, mul_inv_cancel, actC_one]) hφ] with h h1
  exact funext h1

variable [Invertible (2 : k)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_lagr {α : Type} [Fintype α] [DecidableEq α] {ξ : A} {JA : Matrix α α A} (co : Darboux (WeilM.symp c ξ JA JB) κ)
    {C : Matrix β ν A} (h : IsLagr c JB C) : ∃ Λ : Submodule k ((κ → k) × (κ → k)),
      (∀ w, w ∈ Λ ↔ ∃ z : Matrix α ν A, co.e (z * Cᵀ) = w) ∧ (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank k Λ = Fintype.card κ := by
  let L : Matrix β ν A → Submodule k ((κ → k) × (κ → k)) := fun C => LinearMap.range (co.e.toLinearMap ∘ₗ
    { toFun := fun z : Matrix α ν A => z * Cᵀ, map_add' := fun _ _ => Matrix.add_mul _ _ _
      map_smul' := fun _ _ => Matrix.smul_mul _ _ _ })
  have iso : ∀ C : Matrix β ν A, Cᵀ * JB * C.map c = 0 → ∀ a ∈ L C, ∀ b ∈ L C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    rintro C h _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
    have e : z * Cᵀ * JB * ((z' * Cᵀ).map c)ᵀ = z * (Cᵀ * JB * C.map c) * (z'.map c)ᵀ := by
      rw [Matrix.map_mul, transpose_mul, transpose_map, transpose_transpose]
      simp only [Matrix.mul_assoc]
    change (co.e (z * Cᵀ)).1 ⬝ᵥ (co.e (z' * Cᵀ)).2 = (co.e (z' * Cᵀ)).1 ⬝ᵥ (co.e (z * Cᵀ)).2
    rw [← sub_eq_zero, ← co.form, WeilM.symp, hTens_eq_trace, e, h]
    simp
  obtain ⟨h0, Cx, M, hx, h1, -⟩ := h
  refine ⟨L C, fun _ => Iff.rfl, iso C h0, LagrFormLine.finrank_eq _ (L Cx) (iso C h0) (iso Cx hx) ?_⟩
  rw [← Matrix.fromRows_toRows M, Matrix.fromCols_mul_fromRows] at h1
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, rfl⟩ := co.e.surjective w
  have hu : u = u * M.toRows₁ᵀ * Cᵀ + u * M.toRows₂ᵀ * Cxᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, h1, Matrix.transpose_one, Matrix.mul_one]
  rw [hu, map_add]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem siegelRule_linOm (hq : IsQuad c δ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (e : (β → A) ≃ₗ[k] (κ → k))
    (co : Darboux (WeilM.symp c (-1) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) JB) κ)
    (hco : ∀ x, (co.e x).1 = e (x 0) ∧ ∀ u, e u ⬝ᵥ (co.e x).2 = trB c JB u (x 1)) {C : Matrix β ν A} (hL : IsLagr c JB C) :
    SiegelRule c (sbClass k) ψ (-1) _ _ co 1 C (linOm c JB e) ∧ ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
      (∀ z : Matrix (Fin 2) ν A, ∀ φ ∈ SB (κ → k), l (co.rho ψ (z * Cᵀ) φ) = l φ) ∧ ∃ φ ∈ SB (κ → k), l φ ≠ 0 := by
  borelize k
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨b, -, -⟩ := hq.basis
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis b
  obtain ⟨Λ, hΛ, hiso, hdim⟩ := exists_lagr co hL
  obtain ⟨h0, Cx, M, -, -, h1⟩ := hL
  rw [← Matrix.fromRows_toRows M, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h1
  let ε := Module.finBasis k (ν → A)
  let μ : Measure (Fin (Module.finrank k (ν → A)) → k) := Measure.pi fun _ => Measure.addHaar
  let j := e.toLinearMap ∘ₗ (Matrix.toLin' C).restrictScalars k ∘ₗ ε.equivFun.symm.toLinearMap
  have hj : ∀ a, j a = e (C *ᵥ ε.equivFun.symm a) := fun _ => rfl
  let p := ε.equivFun.toLinearMap ∘ₗ (Matrix.toLin' M.toRows₁).restrictScalars k ∘ₗ e.symm.toLinearMap
  have hpj : ∀ a, p (j a) = a := fun a => by
    show ε.equivFun (M.toRows₁ *ᵥ e.symm (e (C *ᵥ ε.equivFun.symm a))) = a
    rw [e.symm_apply_apply, mulVec_mulVec, h1.1, one_mulVec, ε.equivFun.apply_symm_apply]
  have hjc : Continuous j := LinearMap.continuous_on_pi j
  have hpc : Continuous p := LinearMap.continuous_on_pi p
  have hint : ∀ φ ∈ SB (κ → k), Integrable (fun a => φ (j a)) μ := fun φ hφ => by
    refine (hφ.1.continuous.comp hjc).integrable_of_hasCompactSupport (HasCompactSupport.intro (hφ.2.image hpc) fun x hx => ?_)
    by_contra h
    exact hx ⟨j x, subset_tsupport _ h, hpj x⟩
  let f : SB (κ → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ a, φ.1 (j a) ∂μ
      map_add' := fun φ φ' => integral_add (hint _ φ.2) (hint _ φ'.2)
      map_smul' := fun z φ => integral_const_mul z _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend f
  have hl' : ∀ φ ∈ SB (κ → k), l φ = ∫ a, φ (j a) ∂μ := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  have hY : ∀ z : Matrix (Fin 2) ν A, ∀ φ ∈ SB (κ → k), l (co.rho ψ (z * Cᵀ) φ) = l φ := fun z φ hφ => by
    have hr : ∀ i, (z * Cᵀ) i = C *ᵥ z i := fun i => by
      funext i'; simp [mul_apply, mulVec, dotProduct, mul_comm]
    rw [Darboux.rho, hl' _ (HypPair.schr_mem hψ _ hφ), hl' _ hφ,
      ← integral_add_right_eq_self (μ := μ) (fun a => φ (j a)) (ε.equivFun (z 0))]
    congr 1
    funext a
    simp only [schr, (hco _).1, hj, (hco _).2, hr, trB_mulVec, h0, map_add, mulVec_add, LinearEquiv.symm_apply_apply]
    simp
  have hN : ∃ φ ∈ SB (κ → k), l φ ≠ 0 := by
    obtain ⟨U, hUo, hUc, hU0⟩ := GlobalTheory.LagrFormLine.exists_compact_open k κ
    have hm : (U.indicator fun _ => (1 : ℂ)) ∈ SB (κ → k) :=
      ⟨(LocallyConstant.charFn ℂ (⟨hUc.isClosed, hUo⟩ : IsClopen U)).isLocallyConstant,
        HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
    refine ⟨_, hm, ?_⟩
    have hSo : IsOpen (j ⁻¹' U) := hUo.preimage hjc
    have hfin : μ (j ⁻¹' U) < ⊤ := lt_of_le_of_lt
      (measure_mono (show j ⁻¹' U ⊆ p '' U from fun y hy => ⟨j y, hy, hpj y⟩)) ((hUc.image hpc).measure_lt_top)
    have hpos : 0 < μ (j ⁻¹' U) := hSo.measure_pos μ ⟨0, by simpa using hU0⟩
    rw [hl' _ hm, show (fun a => U.indicator (fun _ => (1 : ℂ)) (j a)) = (j ⁻¹' U).indicator (fun _ => (1 : ℂ)) from rfl,
      integral_indicator_const _ hSo.measurableSet]
    exact smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩) one_ne_zero
  refine ⟨fun l₁ _ hl₁ q t hqt φ hφ => ?_, l, hY, hN⟩
  obtain ⟨y, hy⟩ := GlobalTheory.LagrInvForm.proportional k ψ hψ hψ1 _ Λ hiso hdim l₁ l
    (fun w hw => by obtain ⟨z, rfl⟩ := (hΛ w).1 hw; exact hl₁ z) (fun w hw => by obtain ⟨z, rfl⟩ := (hΛ w).1 hw; exact hY z) hN
  have hφ' := linOm_mem e q hφ
  rw [hy _ hφ, hy _ hφ', mul_left_comm, hl' _ hφ, hl' _ hφ']
  congr 1
  have hd : (LinearMap.toMatrix' (actC ε.equivFun t)).det = Algebra.norm k t.val.det := by
    rw [LinearMap.det_toMatrix', actC, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  let g := GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' (actC ε.equivFun t))
    (hd ▸ (((isUnit_iff_isUnit_det _).1 t.isUnit).map _).ne_zero)
  have hg : GeneralLinearGroup.det g = Units.map (Algebra.norm k : A →* k) (GeneralLinearGroup.det t) := Units.ext hd
  have hjg : ∀ a, actC e (q : GL β A)⁻¹ (j (g.val *ᵥ a)) = j a := fun a => by
    obtain ⟨s, rfl⟩ := ε.equivFun.surjective a
    have : g.val *ᵥ ε.equivFun s = ε.equivFun (t.val *ᵥ s) :=
      (LinearMap.toMatrix'_mulVec _ _).trans (actC_apply _ _ _)
    rw [this, hj, hj, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, actC_apply, mulVec_mulVec s, ← hqt,
      mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [← integral_comp_mulVec Measure.addHaar g]
  simp only [linOm_apply, hjg, hg]
  simp [sbClass, μ]

end Top

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LocIntw in

theorem exists_model {F E : Type} [Field F] [Field E] [Algebra F E] {k : Type} [Field k] [Algebra F k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] {σ : E →ₐ[F] E} {δ : k ⊗[F] E}
    (hq : IsQuad (conjR k σ) δ) {ψ : AddChar k ℂ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ}
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = StdUnn.blk4 0 1 (-1) 0) :
    ∃ (d : ℕ) (co : LocDbx σ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (k ⊗[F] E)) Q (Fin d))
      (om : UG (conjR k σ) (JR k Q) →* Module.End ℂ ((Fin d → k) → ℂ)) (l : ((Fin d → k) → ℂ) →ₗ[ℂ] ℂ),
      IsLocModel σ (sbClass k) ψ _ 1 co om ∧ IsYAdm σ (sbClass k) ψ co l ∧ (∃ φ ∈ SB (Fin d → k), l φ ≠ 0) ∧
      ∀ φ ∈ SB (Fin d → k), IsLocallyConstant fun g => om g φ := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  have hJ : ∀ i j, conjR k σ (JR (F := F) k Q j i) = -JR (F := F) k Q i j := fun i j => by
    rw [JR_eq k hQ]
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
      simp only [StdUnn.blk4, submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, map_zero, neg_zero, map_neg, neg_neg,
        apply_ite (conjR k σ), map_one, eq_comm (a := i)]
  have hu : IsUnit (JR (F := F) k Q).det := by
    rw [JR_eq k hQ]
    exact isUnit_det_of_right_inverse (B := StdUnn.blk4 0 (-1) 1 0)
      (by simp [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.block_matrix_one])
  obtain ⟨d, e, co, hco⟩ := exists_coord hq hJ hu
  obtain ⟨hS, l, hl, h0⟩ := siegelRule_linOm hq hψ hψ1 e co hco (isLagr_colY k σ hQ)
  exact ⟨d, co, linOm _ _ e, l, ⟨⟨fun g _ hφ => linOm_mem e g hφ, fun g w φ _ => linOm_impl ψ e co hco g w φ,
    fun _ _ _ => trivial⟩, hS⟩, ⟨trivial, hl⟩, h0, fun _ hφ => isLocallyConstant_linOm hq e hφ⟩

end GlobalTheory.LocSW.Lin

end
end

section
noncomputable section

open scoped Matrix NNReal TensorProduct ComplexConjugate
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.LocIntw

section Slices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)

def AlmostSph (φf : ∀ v, GLoc σ Q v → ℂ) : Prop := ∀ᶠ v in Filter.cofinite, ∀ k ∈ KUpFin σ Q v, φf v k = 1

variable {σ Q}

theorem AlmostSph.finite {φf : ∀ v, GLoc σ Q v → ℂ} (h : AlmostSph σ Q φf) (g : GAd σ Q) :
    (Function.mulSupport fun v => φf v (proj σ Q v g)).Finite :=
  (Filter.eventually_cofinite.1 (h.and (eventually_proj_mem_KUpFin g))).subset fun _ hv h' => hv (h'.1 _ h'.2)

variable (hc : IsCMExt F E σ) (hI : ∀ g : GAd σ Q, ∃ p : upperParabolic (AF F) σ Q, ∃ k ∈ KUpAd σ Q, g = p * k)
include hc hI

end Slices

section SlicesDatum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {n : ℕ}

end SlicesDatum

section FiniteProducts

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)

def intMat (v : HeightOneSpectrum (𝓞 F)) : Set (Fin m → Fin n → Fv F v ⊗[F] E) := {x | ∀ i j, x i j ∈ intLoc F E v}

variable {F E m n}

def AlmostInt (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ) : Prop :=
  ∀ᶠ v in Filter.cofinite, φ v = Set.indicator (intMat F E m n v) 1

def finProd (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ) (y : Fin m → Fin n → Af F ⊗[F] E) : ℂ :=
  ∏ᶠ v, φ v fun i j => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j)

theorem AlmostInt.finite {φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ} (h : AlmostInt φ)
    (y : Fin m → Fin n → Af F ⊗[F] E) : (Function.mulSupport fun v => φ v fun i j =>
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j)).Finite :=
  (Filter.eventually_cofinite.1 (h.and (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    eventually_map_evalV_mem_intLoc (y i j)))).subset fun v hv h' => hv (by
      beta_reduce
      rw [h'.1, Set.indicator_of_mem (s := intMat F E m n v) h'.2, Pi.one_apply])

theorem indicator_intMat_mem_SB (v : HeightOneSpectrum (𝓞 F)) :
    (Set.indicator (intMat F E m n v) 1 : _ → ℂ) ∈ WeilM.SB (Fin m → Fin n → Fv F v ⊗[F] E) := by
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := Fv F v)
  obtain ⟨hc, ho⟩ := ThK.isCompact_isOpen_intLoc (F := F) (E := E) v
  have e : intMat F E m n v = Set.univ.pi fun _ => Set.univ.pi fun _ => (intLoc F E v : Set (Fv F v ⊗[F] E)) := by
    ext x; simp [intMat]
  have h1 : IsCompact (intMat F E m n v) := e ▸ isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  have h2 : IsOpen (intMat F E m n v) :=
    e ▸ isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨h1.isClosed, h2⟩).isLocallyConstant,
    HasCompactSupport.intro h1 fun x hx => Set.indicator_of_notMem hx _⟩

omit [NumberField F] [NumberField E] in

def matCoord {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : (Fin m → Fin n → R ⊗[F] E) ≃ₜ (Fin m × Fin n × Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { toFun := fun x k => (Algebra.TensorProduct.basis R b).repr (x k.1 k.2.1) k.2.2
    invFun := fun y i j => ∑ k, y (i, j, k) • Algebra.TensorProduct.basis R b k
    left_inv := fun x => funext fun i => funext fun j => (Algebra.TensorProduct.basis R b).sum_repr (x i j)
    right_inv := fun y => funext fun k => congrFun ((Algebra.TensorProduct.basis R b).repr_sum_self fun t => y (k.1, k.2.1, t)) k.2.2
    continuous_toFun := continuous_pi fun k =>
      (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k.2.2)).comp
        ((continuous_apply k.2.1).comp (continuous_apply k.1))
    continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun k _ => (continuous_apply (i, j, k)).smul continuous_const }

omit [NumberField F] [NumberField E] in

theorem matCoord_map {d : ℕ} (b : Module.Basis (Fin d) F E) {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing R'] [Algebra F R'] [TopologicalSpace R'] [IsTopologicalRing R'] (φ : R →ₐ[F] R')
    (x : Fin m → Fin n → R ⊗[F] E) :
    matCoord b R' (fun i j => Algebra.TensorProduct.map φ (AlgHom.id F E) (x i j)) = fun k => φ (matCoord b R x k) := by
  funext k
  change (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) (x k.1 k.2.1)) k.2.2 =
    φ ((Algebra.TensorProduct.basis R b).repr (x k.1 k.2.1) k.2.2)
  induction x k.1 k.2.1 using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem eventually_mem_intMat_iff {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x, x ∈ intMat F E m n v ↔
      ∀ k, matCoord b (Fv F v) x k ∈ v.adicCompletionIntegers F :=
  (Cofinite.eventually_mem_intLoc_iff_repr b).mono fun _ h _ =>
    ⟨fun hx k => (h _).1 (hx k.1 k.2.1) k.2.2, fun hx i j => (h _).2 fun k => hx (i, j, k)⟩

theorem finProd_mem_SB {φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ}
    (hφ : ∀ v, φ v ∈ WeilM.SB (Fin m → Fin n → Fv F v ⊗[F] E)) (h : AlmostInt φ) :
    finProd φ ∈ WeilM.SB (Fin m → Fin n → Af F ⊗[F] E) := by
  let b := Module.finBasis F E
  have h1 := AdelicCoordSB.finprod_mem_SB F _ (fun v => φ v ∘ (matCoord b (Fv F v)).symm)
    (fun v => ⟨(hφ v).1.comp_continuous (matCoord b (Fv F v)).symm.continuous, (hφ v).2.comp_homeomorph _⟩) (by
      filter_upwards [h, eventually_mem_intMat_iff (m := m) (n := n) b] with v hv hv'
      funext y
      rw [hv, Function.comp_apply]
      refine Set.indicator_eq_indicator ?_ rfl
      rw [hv', Homeomorph.apply_symm_apply]; rfl)
  have e : finProd φ = (fun y => ∏ᶠ v, (φ v ∘ (matCoord b (Fv F v)).symm) fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y k)) ∘
      matCoord b (Af F) := funext fun y => finprod_congr fun v => by
    rw [Function.comp_apply, ← matCoord_map, Homeomorph.symm_apply_apply]
  rw [e]
  exact ⟨h1.1.comp_continuous (matCoord b (Af F)).continuous, h1.2.comp_homeomorph _⟩

theorem finProd_indicator : finProd (fun v => Set.indicator (intMat F E m n v) 1) =
    Set.indicator {y | ∀ v i j, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j) ∈
      intLoc F E v} 1 := by
  funext y
  by_cases hy : ∀ v i j, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j) ∈ intLoc F E v
  · rw [Set.indicator_of_mem (by exact hy)]
    exact finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (s := intMat F E m n v) (hy v) _
  · rw [Set.indicator_of_notMem (by exact hy)]
    obtain ⟨v, hv⟩ := not_forall.1 hy
    exact finprod_eq_zero _ v (Set.indicator_of_notMem (s := intMat F E m n v) hv _)
      (AlmostInt.finite (φ := fun v => Set.indicator (intMat F E m n v) 1) (.of_forall fun _ => rfl) y)

omit [NumberField E] in

theorem compFin_eq_map_sndA (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) : compFin F E v z =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  rfl

end FiniteProducts

section Factorizable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum

variable {D : D7} {n : ℕ}

def evalPolyAt {m : ℕ} (p : MvPolynomial (Fin m × Fin n × Bool) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun k => if k.2.2 then conj (z k.1 k.2.1) else z k.1 k.2.1) p

def gaussAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (z : Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * (((|l τ| : ℝ) : ℂ) * Matrix.trace (zᴴ * (gramAt D V τ * s τ) * z)))

theorem gauss_eq_prod (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) : StdUnn.gauss V l s z = ∏ τ, gaussAt V l s τ (z τ) := by
  rw [StdUnn.gauss, Finset.mul_sum, Complex.exp_sum]; rfl

theorem evalPoly_rename {m : ℕ} (τ : D.what₂.Tau) (p : MvPolynomial (Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    StdUnn.evalPoly (MvPolynomial.rename (Prod.mk τ) p) z = evalPolyAt p (z τ) := MvPolynomial.eval_rename _ _ _

def pureFun (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : D.what₂.Tau → MvPolynomial (Fin V.rank × Fin n × Bool) ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (x : Mx D V.rank n) : ℂ :=
  (∏ τ, evalPolyAt (p τ) (compAt θ τ x) * gaussAt V l s τ (compAt θ τ x)) *
    ∏ᶠ v, φ v fun i j => AdelicU.compFin D.host.F D.host.E v (x i j)

def IsFactorizable (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (Φ : Mx D V.rank n → ℂ) : Prop :=
  ∃ (p : D.what₂.Tau → MvPolynomial (Fin V.rank × Fin n × Bool) ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ),
    (∀ v, φ v ∈ WeilM.SB (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E)) ∧ AlmostInt φ ∧
      Φ = pureFun θ V l s p φ

theorem compFin_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) : AdelicU.compFin D.host.F D.host.E v z =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D z) := by
  exact compFin_eq_map_sndA v z

variable {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem pureFun_eq (p : D.what₂.Tau → MvPolynomial (Fin V.rank × Fin n × Bool) ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (x : Mx D V.rank n) : pureFun θ V l s p φ x =
      StdUnn.evalPoly (∏ τ, MvPolynomial.rename (Prod.mk τ) (p τ)) (fun τ => compAt θ τ x) *
        StdUnn.gauss V l s (fun τ => compAt θ τ x) * finProd φ fun i j => finPart D (x i j) := by
  rw [pureFun, Finset.prod_mul_distrib, gauss_eq_prod, StdUnn.evalPoly, map_prod, finProd]
  simp only [compFin_eq]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (evalPoly_rename τ (p τ) fun τ => compAt θ τ x).symm

theorem IsFactorizable.mem_fockA {Φ : Mx D V.rank n → ℂ} (h : IsFactorizable θ V n l s Φ) :
    Φ ∈ StdUnn.fockA θ V n l s := by
  obtain ⟨p, φ, h1, h2, rfl⟩ := h
  exact Submodule.subset_span ⟨_, _, finProd_mem_SB h1 h2, funext (pureFun_eq p φ)⟩

def vacFun (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Mx D V.rank n → ℂ := fun x => StdUnn.gauss V l s (fun τ => compAt θ τ x) *
  Set.indicator {x : Mx D V.rank n | ∀ v i j, AdelicU.compFin D.host.F D.host.E v (x i j) ∈ intLoc D.host.F D.host.E v} 1 x

theorem isFactorizable_vacFun : IsFactorizable θ V n l s (vacFun θ V n l s) := by
  refine ⟨1, fun v => Set.indicator (intMat _ _ _ _ v) 1, indicator_intMat_mem_SB, .of_forall fun _ => rfl,
    funext fun x => ?_⟩
  rw [pureFun_eq, finProd_indicator, vacFun]
  simp only [Pi.one_apply, map_one, Finset.prod_const_one, StdUnn.evalPoly, one_mul, compFin_eq]
  rfl

theorem vacFun_zero : vacFun θ V n l s 0 = 1 := by
  have h : ∀ τ, compAt θ τ (0 : Mx D V.rank n) = 0 := fun τ => by ext i j; simp [compAt]
  rw [vacFun, Set.indicator_of_mem (fun v i j => by simp)]
  simp [StdUnn.gauss, h]

example : ∃ Φ ∈ StdUnn.fockA θ V n l s, IsFactorizable θ V n l s Φ ∧ Φ 0 = 1 :=
  ⟨_, isFactorizable_vacFun.mem_fockA, isFactorizable_vacFun, vacFun_zero⟩

example {m : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    evalPolyAt (MvPolynomial.X (i, j, false)) z = z i j ∧ evalPolyAt (MvPolynomial.X (i, j, true)) z = conj (z i j) := by
  simp [evalPolyAt]

end Factorizable

end GlobalTheory.LocIntw

end
end

section
noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw

namespace GlobalTheory.LocSW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem exists_isQuad_conjR (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] : ∃ δ, IsQuad (conjR R σ) δ := by
  obtain ⟨a, ha, hξ⟩ := exists_integer_conj_eq_neg h
  have hξ0 : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  generalize (a : E) = ξ at hξ hξ0
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    simp only [Algebra.smul_def, mul_one] at hsu
    have h2 := congrArg σ hsu
    simp only [map_add, map_mul, AlgHom.commutes, hξ, map_zero] at h2
    have h3 : algebraMap F E u * ξ = 0 := by linear_combination (hsu - h2) / 2
    obtain rfl : u = 0 := (map_eq_zero (algebraMap F E)).mp ((mul_eq_zero.mp h3).resolve_right hξ0)
    exact ⟨(map_eq_zero (algebraMap F E)).mp (by simpa using hsu), rfl⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1]; rfl)
  have hb : ∀ i, b i = ![(1 : E), ξ] i := fun i => by simp [b]
  refine ⟨(1 : R) ⊗ₜ[F] ξ, (IsUnit.mk0 ξ hξ0).map (inclR (F := F) R), ?_, Algebra.TensorProduct.basis R b, ?_, ?_⟩
  · rw [conjR_tmul, hξ, TensorProduct.tmul_neg]
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl
  · rw [Algebra.TensorProduct.basis_apply, hb]; rfl

theorem continuous_psiAt {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (LatVac.psiAt ψ v) := hψ.comp (continuous_const.prodMk (continuous_singleFin v))

theorem psiAt_ne_one (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) :
    LatVac.psiAt ψ v ≠ 1 := fun h => by
  obtain ⟨a, -, ha⟩ := StdRescale.exists_isStd_mulShift F hF ψ hψ
  obtain ⟨t, ht⟩ := PsiNontrivAt.exists_psiAt_ne_one _ ha v
  refine ht ?_
  have h1 := DFunLike.congr_fun h (a • t)
  change ψ (LatVac.liftV v (a • t)) = 1 at h1
  change ψ (algebraMap F (AF F) a * LatVac.liftV v t) = 1
  rwa [map_smul, Algebra.smul_def] at h1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_mem_secFin_hyperbolic (hc : IsCMExt F E σ) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) {ψ : AddChar (AF F) ℂ}
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f ∈ secFin σ hQ ψ 1 !![0, 1; 1, 0] v, f 1 ≠ 0 ∧
      f ∈ psUp _ σ Q (absEv F E v) (KUpFin σ Q v) (charAt 1 v) ((((2 : ℕ) : ℂ) - n) / 2) := by
  letI := invTwo F (Fv F v)
  obtain ⟨δ, hq⟩ := exists_isQuad_conjR hc (Fv F v)
  obtain ⟨d, co, om, l, h1, h2, ⟨φ, hφ, h0⟩, h3⟩ :=
    Lin.exists_model hq (continuous_psiAt hψ.1 v) (psiAt_ne_one hc.1 hψ v) hQ
  have e : JR (F := F) (Fv F v) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [JR]
  have h4 := (h3 φ hφ).comp_continuous (continuous_toUG hQ)
  have hf : coefMap (om.comp (toUG _ σ hQ).toMonoidHom) l φ ∈ secFin σ hQ ψ 1 !![0, 1; 1, 0] v := by
    rw [secFin_eq, e]
    exact secOf_le_secLoc h1 h2 ⟨φ, mem_kFin_of_isLocallyConstant (isCompact_KUpFin v) hφ h4, rfl⟩
  exact ⟨_, hf, by simpa using h0, mem_psUp_fin hf (h4.comp l).continuous⟩

example : IsHermND σ !![0, 1; 1, 0] :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩

example (hσ : ∀ x, σ (σ x) = x) (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (f : GLoc σ Q v → ℂ) (hf : f ∈ secFin σ hQ ψ 1 !![0, 1; 1, 0] v) (a : GL (Fin n) (Fv F v ⊗[F] E)) :
    f (mLoc _ σ hσ hQ a) = (absEv F E v (Matrix.GeneralLinearGroup.det a) : ℝ) * f 1 := by
  simpa [charAt, npow] using law_of_mem_secFin hf ⟨_, mLoc_mem_upP _ σ hσ hQ a⟩ 1

example (hQ : Q = StdUnn.blk4 0 1 (-1) 0) (ψ : AddChar (AF F) ℂ) (χ : (AF F ⊗[F] E)ˣ →* Circle)
    (JA : Matrix (Fin m) (Fin m) E) (w : InfinitePlace F) (hw : w.IsReal) (f : GArch σ Q w → ℂ)
    (hf : f ∈ secArch σ hQ ψ χ JA w hw) (b : HermR w.Completion σ n) (g : GArch σ Q w) : f (nLoc _ σ hQ b * g) = f g := by
  simpa using law_of_mem_secArch hf ⟨_, nLoc_mem_upP hQ b⟩ g

end GlobalTheory.LocSW

end
end
