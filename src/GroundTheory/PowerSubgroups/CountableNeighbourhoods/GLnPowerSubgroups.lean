import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

namespace GroundTheory.Variant₂.N1

open NumberField

noncomputable def normOneGL (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Subgroup (GroundTheory.Automorphic.AdelicGLn.AdelicGL K n) :=
  Subgroup.comap (GroundTheory.Automorphic.AdelicGLn.det K n) (GroundTheory.Global.IdeleGroup.normOneSubgroup K)

section Splitting

variable {G P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup P] [TopologicalSpace P]

def centralSplitting (φ : G →* P) (hφ : Continuous φ) (s : P →* G) (hs : Continuous s)
    (hsφ : ∀ p, φ (s p) = p) (hc : ∀ p g, s p * g = g * s p) (H : Subgroup G)
    (hH : ∀ g, g ∈ H ↔ φ g = 1) : G ≃ₜ* H × P where
  toFun g := (⟨g * (s (φ g))⁻¹, (hH _).2 (by rw [map_mul, map_inv, hsφ, mul_inv_cancel])⟩, φ g)
  invFun x := (x.1 : G) * s x.2
  left_inv g := by simp
  right_inv x := by
    obtain ⟨⟨h, hh⟩, p⟩ := x
    have h1 : φ h = 1 := (hH h).1 hh
    have h2 : φ (h * s p) = p := by rw [map_mul, h1, hsφ, one_mul]
    refine Prod.ext (Subtype.ext ?_) h2
    simp [h2]
  map_mul' g g' := by
    have hci : ∀ p g, (s p)⁻¹ * g = g * (s p)⁻¹ := fun p g => by
      rw [← map_inv]; exact hc p⁻¹ g
    refine Prod.ext (Subtype.ext ?_) (map_mul φ g g')
    simp only [map_mul, mul_inv_rev]
    rw [hci (φ g') (s (φ g))⁻¹]
    calc g * g' * ((s (φ g))⁻¹ * (s (φ g'))⁻¹)
        = g * (g' * (s (φ g))⁻¹) * (s (φ g'))⁻¹ := by simp only [mul_assoc]
      _ = g * ((s (φ g))⁻¹ * g') * (s (φ g'))⁻¹ := by rw [hci]
      _ = g * (s (φ g))⁻¹ * (g' * (s (φ g'))⁻¹) := by simp only [mul_assoc]
  continuous_toFun :=
    (Continuous.subtype_mk (continuous_id.mul ((hs.comp hφ).inv)) _).prodMk hφ
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)

end Splitting

section Section

variable {K : Type*} [Field K]

open Classical in

noncomputable def realToCompletion (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if h : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp Complex.ofRealHom

theorem norm_realToCompletion (w : InfinitePlace K) (t : ℝ) :
    ‖realToCompletion w t‖ = |t| := by
  unfold realToCompletion
  split_ifs with h
  · set y := (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm t
    have hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal h y = t :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal h).apply_symm_apply t
    have := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero
      (map_zero _) y
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← this, hy, Real.norm_eq_abs]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    set y := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (t : ℂ)
    have hy : InfinitePlace.Completion.extensionEmbedding w y = t :=
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).apply_symm_apply t
    have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, Complex.ofRealHom_eq_coe]
    rw [← this, hy, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_realToCompletion (w : InfinitePlace K) : Continuous (realToCompletion w) := by
  unfold realToCompletion
  split_ifs with h
  · refine (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).isEmbedding.isInducing.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal h) ∘
        ⇑((InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom)) = id := by
      funext t; exact (InfinitePlace.Completion.ringEquivRealOfIsReal h).apply_symm_apply t
    rw [this]; exact continuous_id
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbedding w) ∘
        ⇑(((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toRingHom).comp Complex.ofRealHom))
        = fun t : ℝ => (t : ℂ) := by
      funext t; exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).apply_symm_apply t
    rw [this]; exact Complex.continuous_ofReal

noncomputable def posUnit (w : InfinitePlace K) (c : ℝ) : {r : ℝ // 0 < r} →* w.Completionˣ where
  toFun r := Units.mk0 (realToCompletion w ((r : ℝ) ^ c))
    ((map_ne_zero _).2 (Real.rpow_pos_of_pos r.2 c).ne')
  map_one' := by ext; simp
  map_mul' r r' := by
    ext
    simp [Positive.val_mul, Real.mul_rpow r.2.le r'.2.le]

theorem norm_posUnit (w : InfinitePlace K) (c : ℝ) (r : {r : ℝ // 0 < r}) :
    ‖((posUnit w c r : w.Completionˣ) : w.Completion)‖ = (r : ℝ) ^ c := by
  show ‖realToCompletion w ((r : ℝ) ^ c)‖ = _
  rw [norm_realToCompletion, abs_of_pos (Real.rpow_pos_of_pos r.2 c)]

theorem continuous_posUnit (w : InfinitePlace K) (c : ℝ) : Continuous (posUnit w c) := by
  have hv : Continuous fun r : {r : ℝ // 0 < r} => realToCompletion w ((r : ℝ) ^ c) :=
    (continuous_realToCompletion w).comp
      (continuous_subtype_val.rpow_const fun r => Or.inl r.2.ne')
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have : (fun r => (((posUnit w c r)⁻¹ : w.Completionˣ) : w.Completion)) =
      fun r : {r : ℝ // 0 < r} => (realToCompletion w ((r : ℝ) ^ c))⁻¹ := by
    funext r; simp [posUnit]
  rw [this]
  exact hv.inv₀ fun r => (map_ne_zero _).2 (Real.rpow_pos_of_pos r.2 c).ne'

variable [NumberField K]

variable (K) in

noncomputable def basePlace : InfinitePlace K := Classical.arbitrary _

variable (K) in

noncomputable def idelePos (n : ℕ) : {r : ℝ // 0 < r} →* GroundTheory.Global.IdeleGroup K :=
  (GroundTheory.Global.IdeleGroup.infiniteEmbedding (basePlace K)).comp
    (posUnit (basePlace K) (1 / ((n : ℝ) * (basePlace K).mult)))

variable (K) in

noncomputable def scalarSection (n : ℕ) :
    {r : ℝ // 0 < r} →* GroundTheory.Automorphic.AdelicGLn.AdelicGL K n :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).comp (idelePos K n)

variable (K) in

noncomputable def detNorm (n : ℕ) : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} :=
  (GroundTheory.Global.IdeleGroup.ideleModule K).comp (GroundTheory.Automorphic.AdelicGLn.det K n)

end Section

end GroundTheory.Variant₂.N1
