import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatTest

open Module NumberField TensorProduct

section Norms

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

theorem latNorm_span (hv : v.Integers O) {g : V} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  apply IsLeast.csInf_eq
  refine ⟨⟨c, rfl, g, Submodule.mem_span_singleton_self g, rfl⟩, ?_⟩
  rintro r ⟨a, rfl, y, hy, h⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [← IsScalarTower.algebraMap_smul C o g, smul_smul] at h
  have h2 := smul_left_injective C hg h
  rw [h2, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one o)


theorem grLat_diag {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n) :
    grLat (Submodule.span O (Set.range fun j => c j • b j)) b i = Submodule.span O {c i} := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    change b.coord i x ∈ _
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨j, rfl⟩ := h
      by_cases hj : j = i
      · subst hj; simp
      · simp [Finsupp.single_apply, hj]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨c i • b i, ⟨Submodule.subset_span ⟨i, rfl⟩, ?_⟩, by simp⟩
    exact Submodule.smul_mem (b.flag i.succ) _ (b.self_mem_flag Fin.castSucc_lt_succ)



end Norms

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem mem_eigSp {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
    ← integralBasis_apply, trace_dualInt]
  simp

theorem eigProj_mem (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    eigProj ρ σ x ∈ eigSp ρ σ := by
  classical
  haveI : CharZero K := (RingHom.charZero_iff σ.injective).1 inferInstance
  rw [mem_eigSp]
  intro a
  set b := RingOfIntegers.basis E
  have e1 : ∀ k, ρ a (ρ (b k) x) =
      ∑ j, σ ((Algebra.trace ℚ E (dualInt E j * (a : E) * integralBasis E k) : ℚ) : E) • ρ (b j) x := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul, ← b.sum_repr (a * b k), map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := repr_eq_trace (a * b k) j
    rw [map_zsmul, mul_assoc, integralBasis_apply]
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul (algebraMap (𝓞 E) E)] at this
    rw [RingOfIntegers.coe_eq_algebraMap, ← this]
    simp [Int.cast_smul_eq_zsmul, b]
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  change ∑ k, σ (dualInt E k) • ρ a (ρ (b k) x) = _
  simp only [e1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← map_mul, mul_comm (a : E), expand_dual (dualInt E j * (a : E)), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← expand_dual, ← map_mul, Rat.smul_def, mul_comm]

theorem sum_dualInt_mul : ∑ k, dualInt E k * integralBasis E k = 1 := by
  classical
  rw [← sub_eq_zero]
  apply (traceForm_nondegenerate ℚ E).1
  intro y
  rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, mul_assoc, mul_comm _ y]
  generalize y * integralBasis E k = z
  conv_lhs => rw [← (integralBasis E).sum_repr z]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, trace_dualInt]
  simp

theorem eigProj_of_mem {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} (hx : x ∈ eigSp ρ σ) :
    eigProj ρ σ x = x := by
  rw [mem_eigSp] at hx
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ, ← sum_dualInt_mul, map_sum]
    simp
  rw [this, one_smul]

theorem eigProj_of_ne {ρ : 𝓞 E →+* Module.End K V} {σ σ' : E →+* K} (h : σ ≠ σ') {x : V}
    (hx : x ∈ eigSp ρ σ') : eigProj ρ σ x = 0 := by
  have h1 := eigProj_mem ρ σ x
  have h2 : eigProj ρ σ x ∈ eigSp ρ σ' := by
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, mem_eigSp.1 hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  by_contra hne
  apply h
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  have := (mem_eigSp.1 h1 a).symm.trans (mem_eigSp.1 h2 a)
  exact smul_left_injective K hne this


def regAct (K : Type) [Field K] (E : Type) [Field E] [NumberField E] :
    𝓞 E →+* Module.End K (K ⊗[ℤ] 𝓞 E) :=
  (Algebra.lmul K (K ⊗[ℤ] 𝓞 E)).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := K) (B := 𝓞 E)).toRingHom

theorem regAct_basis (k) :
    regAct K E (RingOfIntegers.basis E k) 1 =
      Algebra.TensorProduct.basis K (RingOfIntegers.basis E) k := by
  simp [regAct, Algebra.TensorProduct.basis_apply]





end Eigen

section Further

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]



end Further

section FurtherEigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [Algebra A K] [IsScalarTower A K V] in

theorem isFreeOn_zero {ρ : 𝓞 E →+* Module.End K V} {X : Submodule A V} {t : Fin 0 → V}
    (h : IsFreeOn ρ X t) : Subsingleton V := by
  have h1 := h.2.1
  rw [h.2.2, Set.range_eq_empty, Submodule.span_empty] at h1
  refine subsingleton_of_forall_eq 0 fun y => ?_
  have : y ∈ (⊤ : Submodule K V) := trivial
  rw [← h1] at this
  simpa using this







end FurtherEigen

end GlobalTheory.CompanionTheory.Ar.HT.LatTest
