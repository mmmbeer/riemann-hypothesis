import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsBis
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace PositivityTheory.ThKW.RealC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_split {R : Type} [CommRing R] [Algebra F R] (a : R) (x : E) :
    a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : R) ⊗ₜ[F] x) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem star_theta_one {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    star (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine (NumberField.InfiniteAdeleRing.denseRange_algebraMap (K := F)).induction_on
    (p := fun b => star (θ (b ⊗ₜ[F] (1 : E))) = θ (b ⊗ₜ[F] (1 : E))) a (isClosed_eq h.2.star h.2) (fun x => ?_)
  have e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show star (θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))) = θ ((algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E))
  rw [e, h.1, ← hτ, σ.commutes]

theorem infPart_tmul (a : AF F) (x : E) : infPartF F E (a ⊗ₜ[F] x) = fstA F a ⊗ₜ[F] x := rfl

theorem theta_inc {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (x : E) :
    θ (infPartF F E (incAF F E x)) = τ x := by
  have : infPartF F E (incAF F E x) = fstA F 1 ⊗ₜ[F] x := rfl
  rw [this, map_one, h.1]

theorem theta_conj {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (z : AEF F E) :
    θ (infPartF F E (cAF σ z)) = star (θ (infPartF F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl
    rw [e, infPart_tmul, infPart_tmul, tmul_split _ (σ x), tmul_split _ x, map_mul, map_mul, h.1, h.1, star_mul',
      star_theta_one hτ h, hτ]
  | add a b ha hb => simp only [map_add, ha, hb, star_add]

theorem continuous_theta {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) :
    Continuous (θ.comp (infPartF F E)) := by
  haveI := isModuleTopology_AE F E
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  exact h.2.comp (continuous_fst (X := Ainf F) (Y := Af F))



theorem herm_map {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, map_apply, map_apply, ← hτ, hJ.1]

theorem unit_map {σ : E →ₐ[F] E} (τ : E →+* ℂ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsUnit (J.map τ).det := by
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [this]
  exact ((map_ne_zero τ).2 hJ.2).isUnit

theorem re_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hσ : σ ξ = -ξ) :
    (τ ξ).re = 0 := by
  have := congrArg Complex.re (hτ ξ)
  rw [hσ, map_neg] at this
  simp at this
  linarith

theorem im_xi {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = star (τ x)) {ξ : E} (hξ : ξ ≠ 0) (hσ : σ ξ = -ξ) :
    (τ ξ).im ≠ 0 := fun h => (map_ne_zero τ).2 hξ (Complex.ext (re_xi hτ hσ) h)

theorem compAt_mul_inv {σ : E →ₐ[F] E} (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    compAtF θ w (mtF σ J g) * compAtF θ w (mtF σ J g⁻¹) = 1 := by
  have : mtF σ J 1 = 1 := by unfold mtF; rw [map_one]; rfl
  unfold compAtF
  rw [← Matrix.map_mul, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_mt (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (mtF σ J) ∧ Continuous fun g : GAF σ J => mtF σ J g⁻¹ := by
  have h : Continuous fun g : GAF σ J => matHomF σ J g := continuous_subtype_val
  refine ⟨Units.continuous_val.comp h, ?_⟩
  have e : (fun g : GAF σ J => mtF σ J g⁻¹) = fun g => ((matHomF σ J g)⁻¹).1 := by
    funext g
    unfold mtF
    rw [map_inv]
  rw [e]
  exact Units.continuous_coe_inv.comp h

end PositivityTheory.ThKW.RealC
