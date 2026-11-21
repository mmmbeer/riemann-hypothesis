import Mathlib
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.AutomorphicForms.HermitianWitt
import GroundTheory.AutomorphicForms.UnitaryGroupScheme
import GroundTheory.LocalFields.HerbrandLocal
import GroundTheory.LocalFields.UnramifiedHensel

section
noncomputable section

namespace GroundTheory.Automorphic

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

theorem exists_isotropic_partner (h : HermitianForm F E V) (U : Submodule E V) {r : V}
    (hrU : r ∈ U) (hr : ∀ u ∈ U, h.toSesq r u = 0) (μ : U →ₗ[E] E) (hμ : μ ⟨r, hrU⟩ = 1) :
    ∃ s : V, (∀ u : U, h.toSesq s u = μ u) ∧ h.toSesq s s = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend μ
  obtain ⟨s₀, hs₀⟩ := h.nonsingular.2 g
  have hs₀u : ∀ u : U, h.toSesq s₀ u = μ u := fun u => by
    rw [hs₀, ← hg]
    rfl
  obtain ⟨e₀, he₀⟩ := h.toSesq_self_mem_range s₀
  obtain ⟨c, hc⟩ := exists_trace_eq_one (F := F) (E := E)
  have hc1 : c + conj F E c = 1 := by rw [add_conj, hc, map_one]
  refine ⟨s₀ + (-(c * algebraMap F E e₀)) • r, fun u => ?_, ?_⟩
  · rw [map_add, LinearMap.add_apply, h.toSesq_smul_left, hr u u.2, mul_zero, add_zero, hs₀u]
  · have h1 : h.toSesq s₀ r = 1 := by rw [← hμ, ← hs₀u]
    have h2 : h.toSesq r s₀ = 1 := by rw [← h.conj_toSesq, h1, map_one]
    have h3 : h.toSesq r r = 0 := hr r hrU
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, h1, h2, h3]
    rw [← he₀, map_neg, map_mul, conj_algebraMap]
    linear_combination (-(algebraMap F E e₀)) * hc1

theorem exists_extend [FiniteDimensional E V] (h : HermitianForm F E V) (U : Submodule E V)
    (f : U →ₗ[E] V) (hf : Function.Injective f)
    (hfh : ∀ x y : U, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U, g x = f x := by
  suffices key : ∀ d : ℕ, ∀ (U : Submodule E V) (f : U →ₗ[E] V),
      finrank E V - finrank E U = d → Function.Injective f →
      (∀ x y : U, h.toSesq (f x) (f y) = h.toSesq x y) →
      ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U, g x = f x from
    key _ U f rfl hf hfh
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro U f hd hf hfh
  by_cases hU : ∀ u ∈ U, (∀ u' ∈ U, h.toSesq u u' = 0) → u = 0
  · obtain ⟨g, hg, hgf⟩ := h.exists_extend_of_nondegenerate hU (LinearEquiv.ofInjective f hf)
      (fun x y => by simp only [LinearEquiv.ofInjective_apply]; exact hfh x y)
    exact ⟨g, hg, fun x => by rw [hgf, LinearEquiv.ofInjective_apply]⟩
  push Not at hU
  obtain ⟨r, hrU, hr, hr0⟩ := hU

  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual E U, φ ⟨r, hrU⟩ ≠ 0 := by
    by_contra H
    push Not at H
    exact hr0 (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff E _).1 H))
  set μ : U →ₗ[E] E := (φ ⟨r, hrU⟩)⁻¹ • φ with hμ_def
  have hμ : μ ⟨r, hrU⟩ = 1 := by
    rw [hμ_def, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  obtain ⟨s, hs, hss⟩ := h.exists_isotropic_partner U hrU hr μ hμ

  set e := LinearEquiv.ofInjective f hf with he_def
  have he : ∀ x : U, ((e x : LinearMap.range f) : V) = f x := fun x =>
    LinearEquiv.ofInjective_apply _ _
  have hr₂ : ∀ u ∈ LinearMap.range f, h.toSesq (f ⟨r, hrU⟩) u = 0 := by
    rintro _ ⟨u, rfl⟩
    rw [hfh]
    exact hr u u.2
  have hrr : (⟨f ⟨r, hrU⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f) = e ⟨r, hrU⟩ :=
    Subtype.ext (he _).symm
  obtain ⟨s', hs', hss'⟩ := h.exists_isotropic_partner (LinearMap.range f)
    (LinearMap.mem_range_self f ⟨r, hrU⟩) hr₂ (μ ∘ₗ (e.symm : LinearMap.range f →ₗ[E] U))
    (by rw [LinearMap.comp_apply, hrr, LinearEquiv.coe_coe, e.symm_apply_apply, hμ])
  have hs'' : ∀ x : U, h.toSesq s' (f x) = μ x := by
    intro x
    have := hs' (e x)
    rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, he] at this

  have hsU : s ∉ U := by
    intro hsU
    have h1 := hr s hsU
    have h2 : h.toSesq s r = 1 := by rw [← hμ, ← hs]
    rw [← h.conj_toSesq, h2, map_one] at h1
    exact one_ne_zero h1

  set ψ : (U × E) →ₗ[E] V := U.subtype.coprod (LinearMap.toSpanSingleton E V s) with hψ_def
  have hψ : ∀ (u : U) (a : E), ψ (u, a) = u + a • s := fun u a => by
    simp [hψ_def]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, a⟩ hp
    rw [hψ] at hp
    by_cases ha : a = 0
    · subst ha
      rw [zero_smul, add_zero] at hp
      rw [Submodule.coe_eq_zero.1 hp]
      rfl
    · exfalso
      apply hsU
      have h2 : a • s = -(u : V) := eq_neg_of_add_eq_zero_right hp
      have : s = a⁻¹ • -(u : V) := by rw [← h2, smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [this]
      exact U.smul_mem _ (U.neg_mem u.2)
  set f₀ : (U × E) →ₗ[E] V := f.coprod (LinearMap.toSpanSingleton E V s') with hf₀_def
  have hf₀ : ∀ (u : U) (a : E), f₀ (u, a) = f u + a • s' := fun u a => by
    simp [hf₀_def]
  have hL : ∀ (u v : U) (a b : E), h.toSesq (f u + a • s') (f v + b • s') =
      h.toSesq u v + b * conj F E (μ u) + conj F E a * μ v := by
    intro u v a b
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, hfh, hss']
    rw [← h.conj_toSesq s' (f u), hs'' u, hs'' v]
    ring
  have hR : ∀ (u v : U) (a b : E), h.toSesq ((u : V) + a • s) ((v : V) + b • s) =
      h.toSesq u v + b * conj F E (μ u) + conj F E a * μ v := by
    intro u v a b
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, hss]
    rw [← h.conj_toSesq s (u : V), hs u, hs v]
    ring
  have hf₀inj : Function.Injective f₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, a⟩ hp
    rw [hf₀] at hp
    have ha : a = 0 := by
      have h1 := congrArg (h.toSesq (f ⟨r, hrU⟩)) hp
      rw [map_add, h.toSesq_smul_right, hfh, hr u u.2, zero_add, map_zero,
        ← h.conj_toSesq s', hs'', hμ, map_one, mul_one] at h1
      exact h1
    subst ha
    rw [zero_smul, add_zero] at hp
    have hu : u = 0 := hf (by rw [hp, map_zero])
    rw [hu]
    rfl
  set e' := LinearEquiv.ofInjective ψ hψinj with he'_def
  have he' : ∀ p : U × E, ((e' p : LinearMap.range ψ) : V) = ψ p := fun p =>
    LinearEquiv.ofInjective_apply _ _
  set f' : LinearMap.range ψ →ₗ[E] V := f₀ ∘ₗ (e'.symm : LinearMap.range ψ →ₗ[E] U × E)
  have hf'inj : Function.Injective f' := hf₀inj.comp e'.symm.injective
  have hf'h : ∀ x y : LinearMap.range ψ, h.toSesq (f' x) (f' y) = h.toSesq x y := by
    intro x y
    obtain ⟨⟨u, a⟩, rfl⟩ := e'.surjective x
    obtain ⟨⟨v, b⟩, rfl⟩ := e'.surjective y
    simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe, e'.symm_apply_apply]
    rw [he', he', hf₀, hf₀, hψ, hψ, hL, hR]
  have hdim : finrank E (LinearMap.range ψ) = finrank E U + 1 := by
    rw [LinearMap.finrank_range_of_inj hψinj, Module.finrank_prod, Module.finrank_self]
  have hle : finrank E (LinearMap.range ψ) ≤ finrank E V := Submodule.finrank_le _
  obtain ⟨g, hg, hgf⟩ := ih (finrank E V - finrank E (LinearMap.range ψ)) (by omega)
    (LinearMap.range ψ) f' rfl hf'inj hf'h
  refine ⟨g, hg, fun u => ?_⟩
  have h1 := hgf (e' (u, 0))
  rw [he', hψ, zero_smul, add_zero] at h1
  rw [h1]
  simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe, e'.symm_apply_apply, hf₀, zero_smul,
    add_zero]

end HermitianForm

end GroundTheory.Automorphic

end
end

section
namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable (F : Type*) [Field F]

instance isQuadraticExtension_prod : Algebra.IsQuadraticExtension F (F × F) where
  finrank_eq_two' := by rw [Module.finrank_prod, Module.finrank_self]

variable {F}

theorem trace_prod (x : F × F) : Algebra.trace F (F × F) x = x.1 + x.2 := by
  rw [Algebra.trace_eq_matrix_trace (Basis.finTwoProd F), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Basis.finTwoProd_zero,
    Basis.finTwoProd_one, Basis.coe_finTwoProd_repr, Basis.coe_finTwoProd_repr]
  simp

theorem conj_prod (x : F × F) : conj F (F × F) x = (x.2, x.1) := by
  rw [conj_apply, trace_prod]
  ext <;> simp

section Split

variable (F) (R : Type*) [CommRing R] [Algebra F R]

noncomputable def splitEquiv : R ⊗[F] (F × F) ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.prodRight F R R F F).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid F R R) (Algebra.TensorProduct.rid F R R))

variable {F R}

@[simp]
theorem splitEquiv_tmul (r : R) (x : F × F) : splitEquiv F R (r ⊗ₜ x) = (x.1 • r, x.2 • r) := rfl

variable (F R) in

noncomputable def splitFst : R ⊗[F] (F × F) →+* R :=
  (RingHom.fst R R).comp ((splitEquiv F R : R ⊗[F] (F × F) ≃ₐ[R] R × R) : R ⊗[F] (F × F) →+* R × R)

variable (F R) in

noncomputable def splitSnd : R ⊗[F] (F × F) →+* R :=
  (RingHom.snd R R).comp ((splitEquiv F R : R ⊗[F] (F × F) ≃ₐ[R] R × R) : R ⊗[F] (F × F) →+* R × R)

theorem splitFst_apply (z : R ⊗[F] (F × F)) : splitFst F R z = (splitEquiv F R z).1 := rfl

theorem splitSnd_apply (z : R ⊗[F] (F × F)) : splitSnd F R z = (splitEquiv F R z).2 := rfl

theorem splitEquiv_conjBase (z : R ⊗[F] (F × F)) :
    splitEquiv F R (conjBase F (F × F) R z) = (splitEquiv F R z).swap := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [conj_prod]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Prod.swap_add]

theorem splitFst_conjBase (z : R ⊗[F] (F × F)) :
    splitFst F R (conjBase F (F × F) R z) = splitSnd F R z := by
  rw [splitFst_apply, splitEquiv_conjBase]; rfl

theorem splitSnd_conjBase (z : R ⊗[F] (F × F)) :
    splitSnd F R (conjBase F (F × F) R z) = splitFst F R z := by
  rw [splitSnd_apply, splitEquiv_conjBase]; rfl

theorem splitFst_includeRight (x : F × F) :
    splitFst F R (Algebra.TensorProduct.includeRight x) = algebraMap F R x.1 := by
  simp [splitFst_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]

theorem splitSnd_includeRight (x : F × F) :
    splitSnd F R (Algebra.TensorProduct.includeRight x) = algebraMap F R x.2 := by
  simp [splitSnd_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]

theorem splitFst_tensorMap {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (z : R ⊗[F] (F × F)) : splitFst F S (tensorMap (F × F) f z) = f (splitFst F R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [splitFst_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem split_matrix_ext {X Y : Matrix ι ι (R ⊗[F] (F × F))}
    (h1 : X.map (splitFst F R) = Y.map (splitFst F R)) (h2 : X.map (splitSnd F R) = Y.map (splitSnd F R)) :
    X = Y := by
  ext i j
  apply (splitEquiv F R).injective
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

omit [Fintype ι] [DecidableEq ι] in
theorem map_unitaryExpr_of_comp {A B : Type*} [CommRing A] [CommRing B] [Fintype ι]
    (φ ψ : A →+* B) (s : A →+* A) (hs : ∀ x, φ (s x) = ψ x) (H M : Matrix ι ι A) :
    ((M.map s)ᵀ * H * M).map φ = (M.map ψ)ᵀ * H.map φ * M.map φ := by
  have hc : (φ : A → B) ∘ s = ψ := funext hs
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hc]

variable (H : Matrix ι ι (F × F))

variable (R) in

noncomputable def splitHom : unitaryPoints F (F × F) H R →* GL ι R :=
  (Matrix.GeneralLinearGroup.map (splitFst F R)).comp (unitaryPoints F (F × F) H R).subtype

theorem splitHom_apply (g : unitaryPoints F (F × F) H R) :
    ((splitHom R H g : GL ι R) : Matrix ι ι R) =
      ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem map_splitFst_H :
    (H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F))).map (splitFst F R) =
      H.map fun x => algebraMap F R x.1 := by
  ext i j; exact splitFst_includeRight _

omit [Fintype ι] [DecidableEq ι] in
theorem map_splitSnd_H :
    (H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F))).map (splitSnd F R) =
      H.map fun x => algebraMap F R x.2 := by
  ext i j; exact splitSnd_includeRight _

omit [Fintype ι] [DecidableEq ι] in
theorem hermitian_split (hH : IsHermitianFor (conjHom F (F × F)) H) :
    (H.map fun x => algebraMap F R x.2) = (H.map fun x => algebraMap F R x.1)ᵀ := by
  ext i j
  have := congrFun (congrFun hH i) j
  simp only [transpose_apply, map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_toAlgHom, conj_prod] at this
  simp [← this]

theorem splitHom_bijective (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det) :
    Function.Bijective (splitHom R H) := by
  set HR := H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)) with hHR
  set H₁ := H.map fun x => algebraMap F R x.1 with hH₁
  have h21 := hermitian_split (R := R) H hH
  have hU : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hU₁ : IsUnit H₁ := hU.map (RingHom.mapMatrix ((algebraMap F R).comp (RingHom.fst F F)))
  have hUR : IsUnit HR := hU.map (RingHom.mapMatrix
    (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)).toRingHom)
  have hdetR : IsUnit HR.det := (Matrix.isUnit_iff_isUnit_det HR).1 hUR
  have hR1 : HR.map (splitFst F R) = H₁ := map_splitFst_H H
  have hR2 : HR.map (splitSnd F R) = H₁ᵀ := (map_splitSnd_H H).trans h21

  have eq₁ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)),
      ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitFst F R) =
        (X.map (splitSnd F R))ᵀ * H₁ * X.map (splitFst F R) := fun X => by
    rw [map_unitaryExpr_of_comp _ _ _ splitFst_conjBase, hR1]
  have eq₂ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)),
      ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitSnd F R) =
        (X.map (splitFst F R))ᵀ * H₁ᵀ * X.map (splitSnd F R) := fun X => by
    rw [map_unitaryExpr_of_comp _ _ _ splitSnd_conjBase, hR2]
  constructor
  · intro g g' hgg'
    have h1 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) =
        ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := by
      rw [← splitHom_apply, ← splitHom_apply, hgg']
    have hg := congrArg (fun M => M.map (splitFst F R))
      (show (((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map
        (conjBase F (F × F) R))ᵀ * HR * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F)))
          = HR from g.2)
    have hg' := congrArg (fun M => M.map (splitFst F R))
      (show (((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map
        (conjBase F (F × F) R))ᵀ * HR * ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F)))
          = HR from g'.2)
    simp only [eq₁, hR1] at hg hg'
    have hunit : IsUnit (H₁ * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R)) := by
      refine hU₁.mul ?_
      rw [← splitHom_apply]
      exact Units.isUnit _
    have h2 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) =
        ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) := by
      apply Matrix.transpose_injective
      apply (hunit.mul_left_inj).1
      rw [← Matrix.mul_assoc, hg, h1, ← Matrix.mul_assoc, hg']
    exact Subtype.ext (Units.ext (split_matrix_ext h1 h2))
  · intro m
    set m₁ : Matrix ι ι R := (↑m : Matrix ι ι R)
    set g₂ : Matrix ι ι R := (H₁ * (↑m⁻¹ : Matrix ι ι R) * H₁⁻¹)ᵀ
    let X : Matrix ι ι (R ⊗[F] (F × F)) := fun i j => (splitEquiv F R).symm (m₁ i j, g₂ i j)
    have hX1 : X.map (splitFst F R) = m₁ := by
      ext i j
      show splitFst F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = m₁ i j
      rw [splitFst_apply, AlgEquiv.apply_symm_apply]
    have hX2 : X.map (splitSnd F R) = g₂ := by
      ext i j
      show splitSnd F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = g₂ i j
      rw [splitSnd_apply, AlgEquiv.apply_symm_apply]
    have hdet₁ : IsUnit H₁.det := (Matrix.isUnit_iff_isUnit_det H₁).1 hU₁
    have key₁ : g₂ᵀ * H₁ * m₁ = H₁ := by
      simp only [g₂, transpose_transpose]
      rw [Matrix.mul_assoc (H₁ * _), Matrix.nonsing_inv_mul _ hdet₁, Matrix.mul_one,
        Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    have hXeq : (X.map (conjBase F (F × F) R))ᵀ * HR * X = HR := by
      apply split_matrix_ext
      · rw [eq₁, hR1, hX1, hX2, key₁]
      · rw [eq₂, hR2, hX1, hX2]
        conv_rhs => rw [← key₁]
        rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    obtain ⟨u, hu, hux⟩ := (exists_mem_unitaryGroupMatrix_iff _ hdetR X).2 hXeq
    refine ⟨⟨u, hu⟩, Units.ext ?_⟩
    rw [splitHom_apply]
    simp only [hux, hX1, m₁]

variable (R) in

noncomputable def unitaryPointsSplitEquiv (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hdet : IsUnit H.det) : unitaryPoints F (F × F) H R ≃* GL ι R :=
  MulEquiv.ofBijective (splitHom R H) (splitHom_bijective H hH hdet)

theorem unitaryPointsSplitEquiv_apply (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hdet : IsUnit H.det) (g : unitaryPoints F (F × F) H R) :
    ((unitaryPointsSplitEquiv R H hH hdet g : GL ι R) : Matrix ι ι R) =
      ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := rfl

theorem unitaryPointsSplitEquiv_natural {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det)
    (g : unitaryPoints F (F × F) H R) :
    unitaryPointsSplitEquiv S H hH hdet (unitaryMap F (F × F) H f g) =
      Matrix.GeneralLinearGroup.map (f : R →+* S) (unitaryPointsSplitEquiv R H hH hdet g) := by
  apply Units.ext
  rw [unitaryPointsSplitEquiv_apply, unitaryMap_apply]
  ext i j
  simp [unitaryPointsSplitEquiv_apply, Matrix.GeneralLinearGroup.map, splitFst_tensorMap]

end Split

section SplitFunctor

open CategoryTheory

universe u

variable (F : Type u) [Field F] (ι : Type u) [Fintype ι] [DecidableEq ι]

noncomputable def generalLinearFunctor : CommAlgCat.{u} F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (GL ι R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map (f.hom : _ →+* _))
  map_id R := by
    rw [CommAlgCat.hom_id]
    exact congrArg GrpCat.ofHom Matrix.GeneralLinearGroup.map_id
  map_comp f g := by
    rw [CommAlgCat.hom_comp]
    exact congrArg GrpCat.ofHom (Matrix.GeneralLinearGroup.map_comp _ _)

variable {F ι}

end SplitFunctor

end GroundTheory.Automorphic
end

section
namespace GroundTheory.Automorphic

open Module Matrix

variable {F : Type*} [Field F]
variable {V V' : Type*} [AddCommGroup V] [Module (F × F) V] [AddCommGroup V'] [Module (F × F) V']



end GroundTheory.Automorphic
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

theorem mem_or_mul_inv_mem_of_natCard_eq_two {G : Type*} [CommGroup G] {N : Subgroup G}
    (hN : Nat.card (G ⧸ N) = 2) {t : G} (ht : t ∉ N) (u : G) : u ∈ N ∨ u * t⁻¹ ∈ N := by
  by_contra H
  push Not at H
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ N)).1 hN
  have h1 : (QuotientGroup.mk t : G ⧸ N) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk u : G ⧸ N) ≠ 1 := by rw [Ne, QuotientGroup.eq_one_iff]; exact H.1
  have h3 := QuotientGroup.eq.1 ((hy _ h1).trans (hy _ h2).symm)
  apply H.2
  rwa [mul_comm]

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem norm_algebraMap_quadratic (t : F) : Algebra.norm F (algebraMap F E t) = t ^ 2 := by
  rw [Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem norm_inv_quadratic (z : E) : Algebra.norm F z⁻¹ = (Algebra.norm F z)⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, Algebra.norm_zero, inv_zero]
  · exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])

theorem mem_range_normUnits_iff (u : Fˣ) :
    u ∈ (normUnits F E).range ↔ ∃ z : E, Algebra.norm F z = u := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (coe_normUnits w).symm⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [Algebra.norm_zero] at hz; exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [coe_normUnits, Units.val_mk0, hz])⟩

theorem exists_norm_add_norm_ne (hN : Nat.card (Fˣ ⧸ (normUnits F E).range) = 2)
    (hsq : ∃ m : ℕ, 0 < m ∧ ∃ s : F, s ^ 2 = -(m : F)) :
    ∃ x y : E, ∀ z : E, Algebra.norm F x + Algebra.norm F y ≠ Algebra.norm F z := by
  by_contra H
  push Not at H

  have hmul : ∀ a b : F, (∃ z : E, Algebra.norm F z = a) → (∃ z : E, Algebra.norm F z = b) →
      ∃ z : E, Algebra.norm F z = a * b := by
    rintro a b ⟨z, rfl⟩ ⟨w, rfl⟩
    exact ⟨z * w, map_mul _ _ _⟩
  have hinv : ∀ a : F, (∃ z : E, Algebra.norm F z = a) → ∃ z : E, Algebra.norm F z = a⁻¹ := by
    rintro a ⟨z, rfl⟩
    exact ⟨z⁻¹, norm_inv_quadratic z⟩
  have hadd : ∀ a b : F, (∃ z : E, Algebra.norm F z = a) → (∃ z : E, Algebra.norm F z = b) →
      ∃ z : E, Algebra.norm F z = a + b := by
    rintro a b ⟨z, rfl⟩ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := H z w
    exact ⟨u, hu.symm⟩
  by_cases hm1 : ∃ w : E, Algebra.norm F w = -1
  ·
    obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : Fˣ ⧸ (normUnits F E).range)).1 hN
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    have ht : t ∉ (normUnits F E).range := by rwa [Ne, QuotientGroup.eq_one_iff] at hy1
    have htR : ¬ ∃ z : E, Algebra.norm F z = t := fun H' => ht ((mem_range_normUnits_iff t).2 H')
    have h1t : (1 : F) + t ≠ 0 := by
      intro h0
      apply htR
      obtain ⟨w, hw⟩ := hm1
      exact ⟨w, by rw [hw]; linear_combination -h0⟩
    rcases mem_or_mul_inv_mem_of_natCard_eq_two hN ht (Units.mk0 _ h1t) with h | h
    · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
      apply htR
      obtain ⟨z', hz'⟩ := hadd _ _ ⟨z, hz⟩ hm1
      exact ⟨z', by rw [hz', Units.val_mk0]; ring⟩
    · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
      rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val] at hz
      obtain ⟨z', hz'⟩ := hadd _ _ ⟨z, hz⟩ hm1
      obtain ⟨z'', hz''⟩ := hinv _ ⟨z', hz'⟩
      apply htR
      refine ⟨z'', ?_⟩
      rw [hz'']
      have ht0 : (t : F) ≠ 0 := t.ne_zero
      field_simp
      ring
  ·
    have hk : ∀ k : ℕ, ∃ z : E, Algebra.norm F z = ((k + 1 : ℕ) : F) := by
      intro k
      induction k with
      | zero => exact ⟨1, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := hadd _ _ ih ⟨1, map_one _⟩
        exact ⟨z, by rw [hz]; push_cast; ring⟩
    obtain ⟨m, hm, s, hs⟩ := hsq
    apply hm1
    by_cases hm0 : (m : F) = 0
    · have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m; simp at hm0
        · exact h
      obtain ⟨z, hz⟩ := hk (m - 2)
      refine ⟨z, ?_⟩
      rw [hz]
      have : ((m - 2 + 1 : ℕ) : F) = (m : F) - 1 := by
        rw [show m - 2 + 1 = m - 1 by omega, Nat.cast_sub (by omega), Nat.cast_one]
      rw [this, hm0, zero_sub]
    · obtain ⟨z, hz⟩ := hk (m - 1)
      rw [show m - 1 + 1 = m by omega] at hz
      obtain ⟨w, hw⟩ := hinv _ ⟨z, hz⟩
      refine ⟨algebraMap F E s * w, ?_⟩
      rw [map_mul, norm_algebraMap_quadratic, hs, hw]
      field_simp

end General

section Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_sq_eq_neg_natCast : ∃ m : ℕ, 0 < m ∧ ∃ s : F, s ^ 2 = -(m : F) := by
  set p := ringChar 𝓀[F]
  have hp : p ≠ 0 := CharP.char_ne_zero_of_finite 𝓀[F] p
  have hpm : (p : 𝒪[F]) ∈ 𝓂[F] := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  set P : 𝒪[F][X] := X ^ 2 + X + C (p : 𝒪[F])
  have hP : P.Monic := by
    simp only [P]
    monicity!
  have h1 : P.eval 0 ∈ 𝓂[F] := by simpa [P] using hpm
  have h2 : IsUnit (P.derivative.eval 0) := by
    simp [P]
  obtain ⟨x, hx, -⟩ := HenselianLocalRing.is_henselian P hP 0 h1 h2
  have hx' : (x : F) ^ 2 + x + p = 0 := by
    have := congrArg (fun y : 𝒪[F] => (y : F)) hx.eq_zero
    simpa [P] using this
  refine ⟨4 * p - 1, by omega, 2 * x + 1, ?_⟩
  rw [Nat.cast_sub (by omega)]
  push_cast
  linear_combination 4 * hx'

variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]

theorem natCard_quotient_range_normUnits_eq_two :
    Nat.card (Fˣ ⧸ (normUnits F E).range) = 2 := by
  obtain ⟨_, _, _, _⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F E
  rw [natCard_units_quotient_range_normUnits, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem exists_mul_norm_add_mul_norm_eq (a b c : Fˣ) :
    ∃ x y : E, (a : F) * Algebra.norm F x + b * Algebra.norm F y = c := by
  have hN := natCard_quotient_range_normUnits_eq_two (F := F) (E := E)
  set N := (normUnits F E).range
  obtain ⟨x₀, y₀, hxy⟩ := exists_norm_add_norm_ne hN (exists_sq_eq_neg_natCast F)
  obtain ⟨f, hf⟩ : ∃ f, f = Algebra.norm F x₀ + Algebra.norm F y₀ := ⟨_, rfl⟩
  have hf0 : f ≠ 0 := fun h0 => hxy 0 (by rw [Algebra.norm_zero, ← hf]; exact h0)
  have hfN : Units.mk0 f hf0 ∉ N := fun h => by
    obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
    exact hxy z (by rw [← hf, hz, Units.val_mk0])
  by_cases hca : c * a⁻¹ ∈ N
  · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 hca
    refine ⟨z, 0, ?_⟩
    rw [hz, Algebra.norm_zero, mul_zero, add_zero, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  by_cases hcb : c * b⁻¹ ∈ N
  · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 hcb
    refine ⟨0, z, ?_⟩
    rw [hz, Algebra.norm_zero, mul_zero, zero_add, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

  have hba : b * a⁻¹ ∈ N := by
    rcases mem_or_mul_inv_mem_of_natCard_eq_two hN hca (c * b⁻¹) with h | h
    · exact absurd h hcb
    · have h' : c * b⁻¹ * (c * a⁻¹)⁻¹ = (b * a⁻¹)⁻¹ := by
        apply Units.ext
        have := a.ne_zero
        have := b.ne_zero
        have := c.ne_zero
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
      rw [h'] at h
      simpa using N.inv_mem h
  have hcaf : c * a⁻¹ * (Units.mk0 f hf0)⁻¹ ∈ N :=
    (mem_or_mul_inv_mem_of_natCard_eq_two hN hfN (c * a⁻¹)).resolve_left hca
  obtain ⟨t, ht⟩ := (mem_range_normUnits_iff _).1 hba
  obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 hcaf
  have ht0 : t ≠ 0 := by
    rintro rfl; rw [Algebra.norm_zero] at ht; exact (Units.ne_zero _) ht.symm
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at ht hz
  refine ⟨x₀ * z, y₀ * z * t⁻¹, ?_⟩
  rw [map_mul, map_mul, map_mul, norm_inv_quadratic, hz, ht]
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  have key : (a : F) * (Algebra.norm F x₀ * ((c : F) * (a : F)⁻¹ * f⁻¹)) +
      (b : F) * (Algebra.norm F y₀ * ((c : F) * (a : F)⁻¹ * f⁻¹) * ((b : F) * (a : F)⁻¹)⁻¹) =
      c * f⁻¹ * (Algebra.norm F x₀ + Algebra.norm F y₀) := by
    field_simp
  rw [key, ← hf, mul_assoc, inv_mul_cancel₀ hf0, mul_one]

namespace HermitianForm

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

theorem exists_toSesq_self_eq [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : 2 ≤ finrank E V) (c : Fˣ) : ∃ v, h.toSesq v v = algebraMap F E c := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨v₁, hv₁⟩ := h.exists_apply_self_ne_zero
  obtain ⟨a, ha⟩ := h.toSesq_self_mem_range v₁
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hv₁ ha.symm
  obtain ⟨W, h₀, ⟨e, he⟩, hW⟩ := h.exists_isometric_prod_ofUnit (a := Units.mk0 a ha0) ha.symm
  have hW' := hW inferInstance
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨w, hw⟩ := h₀.exists_apply_self_ne_zero
  obtain ⟨b, hb⟩ := h₀.toSesq_self_mem_range w
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact hw hb.symm
  obtain ⟨x, y, hxy⟩ := exists_mul_norm_add_mul_norm_eq (E := E) (Units.mk0 a ha0)
    (Units.mk0 b hb0) c
  refine ⟨e (x, y • w), ?_⟩
  rw [he, prod_apply, ofUnit_apply, h₀.toSesq_smul_left, h₀.toSesq_smul_right, ← hb, ← hxy]
  simp only [Units.val_mk0, map_add, map_mul]
  rw [← mul_conj (F := F) x, ← mul_conj (F := F) y]
  ring

theorem disc_eq_of_isometric_prod_ofUnit [FiniteDimensional E V] (h : HermitianForm F E V)
    {W : Submodule E V} {h₀ : HermitianForm F E W} {a : Fˣ}
    (H : Isometric ((ofUnit (E := E) a).prod h₀) h) :
    h.disc = QuotientGroup.mk a * h₀.disc := by
  rw [← H.disc_eq, disc_prod, disc_ofUnit]

theorem isometric_iff [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') :
    Isometric h h' ↔ finrank E V = finrank E V' ∧ h.disc = h'.disc := by
  refine ⟨fun H => ⟨H.finrank_eq, H.disc_eq⟩, fun ⟨hdim, hdisc⟩ => ?_⟩
  suffices key : ∀ n : ℕ, ∀ (U : Type _) (U' : Type _) [AddCommGroup U] [Module E U]
      [FiniteDimensional E U] [AddCommGroup U'] [Module E U'] [FiniteDimensional E U'],
      finrank E U = n → finrank E U' = n → ∀ (k : HermitianForm F E U)
      (k' : HermitianForm F E U'), k.disc = k'.disc → Isometric k k' from
    key _ V V' rfl hdim.symm h h' hdisc
  intro n
  induction n with
  | zero =>
    intro U U' _ _ _ _ _ _ hU hU' k k' _
    have : Subsingleton U := Module.finrank_zero_iff.1 hU
    refine ⟨LinearEquiv.ofFinrankEq U U' (hU.trans hU'.symm), fun x y => ?_⟩
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | succ n ih =>
    intro U U' _ _ _ _ _ _ hU hU' k k' hkk

    obtain ⟨c, ⟨v, hv⟩, ⟨v', hv'⟩⟩ : ∃ c : Fˣ, (∃ v, k.toSesq v v = algebraMap F E c) ∧
        (∃ v', k'.toSesq v' v' = algebraMap F E c) := by
      rcases Nat.lt_or_ge n 1 with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        have : Nontrivial U := Module.nontrivial_of_finrank_eq_succ hU
        have : Nontrivial U' := Module.nontrivial_of_finrank_eq_succ hU'
        obtain ⟨v, hv⟩ := k.exists_apply_self_ne_zero
        obtain ⟨a, ha⟩ := k.toSesq_self_mem_range v
        have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hv ha.symm
        obtain ⟨v', hv'⟩ := k'.exists_apply_self_ne_zero
        obtain ⟨a', ha'⟩ := k'.toSesq_self_mem_range v'
        have ha0' : a' ≠ 0 := by rintro rfl; rw [map_zero] at ha'; exact hv' ha'.symm
        obtain ⟨W, k₀, Hk, hW⟩ := k.exists_isometric_prod_ofUnit (a := Units.mk0 a ha0) ha.symm
        obtain ⟨W', k₀', Hk', hW'⟩ :=
          k'.exists_isometric_prod_ofUnit (a := Units.mk0 a' ha0') ha'.symm
        have d1 : k.disc = QuotientGroup.mk (Units.mk0 a ha0) := by
          rw [k.disc_eq_of_isometric_prod_ofUnit Hk,
            k₀.disc_of_finrank_eq_zero (by have := hW inferInstance; omega)]
          exact mul_one (M := Fˣ ⧸ (normUnits F E).range) _
        have d2 : k'.disc = QuotientGroup.mk (Units.mk0 a' ha0') := by
          rw [k'.disc_eq_of_isometric_prod_ofUnit Hk',
            k₀'.disc_of_finrank_eq_zero (by have := hW' inferInstance; omega)]
          exact mul_one (M := Fˣ ⧸ (normUnits F E).range) _
        rw [d1, d2] at hkk
        obtain ⟨u, hu⟩ := QuotientGroup.eq.1 hkk.symm
        refine ⟨Units.mk0 a ha0, ⟨v, ha.symm⟩, ⟨(u : E) • v', ?_⟩⟩
        rw [k'.toSesq_smul_left, k'.toSesq_smul_right, ← ha', ← mul_assoc,
          mul_comm (conj F E (u : E)), mul_conj, ← map_mul, ← coe_normUnits, hu]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp
      · refine ⟨1, k.exists_toSesq_self_eq (by omega) 1, k'.exists_toSesq_self_eq (by omega) 1⟩
    obtain ⟨W, k₀, Hk, hW⟩ := k.exists_isometric_prod_ofUnit hv
    obtain ⟨W', k₀', Hk', hW'⟩ := k'.exists_isometric_prod_ofUnit hv'
    have hWn : finrank E W = n := by have := hW inferInstance; omega
    have hWn' : finrank E W' = n := by have := hW' inferInstance; omega
    have hd : k₀.disc = k₀'.disc := by
      have d1 := k.disc_eq_of_isometric_prod_ofUnit Hk
      have d2 := k'.disc_eq_of_isometric_prod_ofUnit Hk'
      rw [d1, d2] at hkk
      have := congrArg ((QuotientGroup.mk c : Fˣ ⧸ (normUnits F E).range)⁻¹ * ·) hkk
      simpa only [inv_mul_cancel_left] using this
    exact (Hk.symm.trans ((Isometric.refl _).prod (ih W W' hWn hWn' k₀ k₀' hd))).trans Hk'

end HermitianForm

end Local

end GroundTheory.Automorphic

end
end
