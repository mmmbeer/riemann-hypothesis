import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLast
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.DualFormInverse

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_one {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p : ι} {α : K}
    (hα : α ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p := by
  refine ⟨fun t => if t = p then α else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    · exact hα
    · exact S.zero_mem
  · rw [Fintype.sum_eq_single p]
    · simp
    · intro t ht
      simp [ht]

theorem exists_two {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p q : ι} (hpq : p ≠ q)
    {α β : K} (hα : α ∈ S) (hβ : β ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p + β * g s q := by
  refine ⟨fun t => if t = p then α else if t = q then β else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    exacts [hα, hβ, S.zero_mem]
  · rw [Fintype.sum_eq_add p q hpq]
    · simp [hpq.symm]
    · rintro t ⟨h1, h2⟩
      simp [h1, h2]

theorem dualF_le_of_inv {ι : Type} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hnd : Nondeg h) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (G : ι → V)
    (hG : Submodule.span K (Set.range G) = ⊤)
    (hinv : ∀ u, ∃ κ : ι → K, (∀ t, κ t ∈ SP K 𝔭) ∧
      ∀ s, ∑ t, κ t * h (G s) (G t) = if s = u then 1 else 0) :
    dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range G))) ≤
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range G)) := by
  choose κ hκS hκ using hinv
  intro x hx
  have hX : ∀ u, h (G u) x ∈ SP K 𝔭 := fun u => by
    rw [mem_SP_iff_locF]
    exact hx (G u) (LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨u, rfl⟩))
  have hyx : ∀ s, h (G s) (x - ∑ t, (∑ u, κ u t * h (G u) x) • G t) = 0 := by
    intro s
    rw [map_sub, map_sum]
    simp only [form_smul_right]
    have e : ∀ t, (∑ u, κ u t * h (G u) x) * h (G s) (G t) =
        ∑ u, h (G u) x * (κ u t * h (G s) (G t)) := fun t => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ]
    simp
  have hxy := eq_zero_of_orth hs hnd G hG hyx
  rw [sub_eq_zero] at hxy
  rw [hxy]
  refine Submodule.sum_mem _ fun t _ => smul_mem_locF_of_SP ?_ (Submodule.subset_span ⟨t, rfl⟩)
  exact (SP K 𝔭).sum_mem fun u _ => (SP K 𝔭).mul_mem (hκS u t) (hX u)

end Formalism.L2.SG.Pf.DualFormInverse
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions Formalism.L2.SG.Pf.GluedFormOrthogonality
  Formalism.L2.SG.Pf.DualFormInverse

end Formalism.L2.SG.Pf.Cnt
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def NU (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (x : K) : Prop :=
  ∃ l : K, l ≠ 0 ∧ x * (l * star l) ∈ SP K 𝔭 ∧ (x * (l * star l))⁻¹ ∈ SP K 𝔭

variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]

theorem NU.of_unit {u : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) : NU 𝔭 u :=
  ⟨1, one_ne_zero, by simpa using h1, by simpa using h2⟩

theorem NU.mul {x y : K} (hx : NU 𝔭 x) (hy : NU 𝔭 y) : NU 𝔭 (x * y) := by
  obtain ⟨a, ha, ha1, ha2⟩ := hx
  obtain ⟨b, hb, hb1, hb2⟩ := hy
  have e : x * y * (a * b * star (a * b)) = (x * (a * star a)) * (y * (b * star b)) := by
    rw [star_mul']
    ring
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · rw [e]
    exact (SP K 𝔭).mul_mem ha1 hb1
  · rw [e, mul_inv]
    exact (SP K 𝔭).mul_mem ha2 hb2

theorem NU.inv {x : K} (hx : NU 𝔭 x) : NU 𝔭 x⁻¹ := by
  obtain ⟨a, ha, h1, h2⟩ := hx
  have hs : star a⁻¹ = (star a)⁻¹ := by
    first | exact star_inv₀ a | exact star_inv' a | simp
  have e : x⁻¹ * (a⁻¹ * star a⁻¹) = (x * (a * star a))⁻¹ := by
    rw [hs, mul_inv, mul_inv]
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · rw [e]
    exact h2
  · rw [e, inv_inv]
    exact h1

theorem NU.of_mul_left {x y : K} (hxy : NU 𝔭 (x * y)) (hy : NU 𝔭 y) (hy0 : y ≠ 0) : NU 𝔭 x := by
  have h := NU.mul hxy (NU.inv hy)
  rwa [mul_assoc, mul_inv_cancel₀ hy0, mul_one] at h

theorem NU.norm_mul {u z : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) (hz : z ≠ 0) :
    NU 𝔭 (star z * u * z) := by
  have hs : star z⁻¹ = (star z)⁻¹ := by
    first | exact star_inv₀ z | exact star_inv' z | simp
  have hsz : star z ≠ 0 := by
    first | exact star_ne_zero.2 hz | simpa using hz
  have e : star z * u * z * (z⁻¹ * star z⁻¹) = u := by
    rw [hs]
    calc star z * u * z * (z⁻¹ * (star z)⁻¹) = u * (z * z⁻¹) * (star z * (star z)⁻¹) := by ring
      _ = u := by rw [mul_inv_cancel₀ hz, mul_inv_cancel₀ hsz, mul_one, mul_one]
  refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e]
    exact h2

theorem NU.prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, NU 𝔭 (f i)) :
    NU 𝔭 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (NU 𝔭) (fun _ _ ha hb => NU.mul ha hb)
    (NU.of_unit (SP K 𝔭).one_mem (by rw [inv_one]; exact (SP K 𝔭).one_mem)) hf

theorem NU.pair {A C : K} (hA : A ≠ 0) (hAs : star A = A) (h1 : C * A⁻¹ ∈ SP K 𝔭)
    (h2 : A * C⁻¹ ∈ SP K 𝔭) : NU 𝔭 (A * C) := by
  have hs : star A⁻¹ = (star A)⁻¹ := by
    first | exact star_inv₀ A | exact star_inv' A | simp
  have e : A * C * (A⁻¹ * star A⁻¹) = C * A⁻¹ := by
    rw [hs, hAs]
    calc A * C * (A⁻¹ * A⁻¹) = C * A⁻¹ * (A * A⁻¹) := by ring
      _ = C * A⁻¹ := by rw [mul_inv_cancel₀ hA, mul_one]
  refine ⟨A⁻¹, inv_ne_zero hA, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e, mul_inv, inv_inv, mul_comm]
    exact h2

section Vec

variable {V : Type} [AddCommGroup V] [Module K V]

theorem linInd_orth {ι : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (g : ι → V)
    (ho : ∀ s t, s ≠ t → h (g s) (g t) = 0) (hn : ∀ s, h (g s) (g s) ≠ 0) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have key := congrArg (h (g i)) hs
  rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, smul_eq_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

end Vec

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem det_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) :
    G.det ∈ SP K 𝔭 := by
  have e : G.det = (SP K 𝔭).subtype
      (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭))) := by
    rw [RingHom.map_det]; rfl
  rw [e]
  exact SetLike.coe_mem _

theorem gram_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) (β : Basis κ K V) :
    (gramK h β).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hy : ∀ x, h x (β.equivFun.symm v) = 0 := by
    intro x
    rw [form_repr h β, LinearEquiv.apply_symm_apply, hGv]
    simp
  have h0 : β.equivFun.symm v = 0 := by
    apply hnd
    intro y
    have := hs.eq y (β.equivFun.symm v)
    rw [← this, hy y, map_zero]
  exact β.equivFun.symm.injective (by rw [h0, map_zero])

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) K) (x : K) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

private lemma star_mem_SP' (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K}
    (ha : a ∈ SP K 𝔭) : star a ∈ SP K 𝔭 := by
  rw [mem_SP_iff_locF] at ha ⊢
  obtain ⟨s, hs', hsa⟩ := (mem_locF_lemma 𝔭 _ a).mp ha
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsa
  obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range z
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨s, hs', Submodule.mem_one.mpr ⟨r, ?_⟩⟩
  rw [hr, hz, Algebra.smul_def, Algebra.smul_def, star_mul', star_fix_lemma_2 hF hs']

theorem det_unit_of_selfdual (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) (β : Basis κ K V) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
    (hsd : dualF h 𝔭 (locF 𝔭 (spanO β)) = locF 𝔭 (spanO β)) :
    (gramK h β).det ∈ SP K 𝔭 ∧ (gramK h β).det⁻¹ ∈ SP K 𝔭 := by
  have hdet := gram_det_ne_zero hs hnd β
  have hunit : IsUnit (gramK h β).det := isUnit_iff_ne_zero.mpr hdet
  have hmemL : ∀ x, x ∈ locF 𝔭 (spanO β) ↔ ∀ i, β.equivFun x i ∈ SP K 𝔭 :=
    fun x => mem_locF_iff_repr β x
  have hβ : ∀ i, β i ∈ locF 𝔭 (spanO β) := fun i => by
    simpa using smul_basis_mem β (SP K 𝔭).one_mem i
  have hdual : ∀ x ∈ locF 𝔭 (spanO β), ∀ y ∈ locF 𝔭 (spanO β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hsd] at hx
    exact hx
  have hG : Ent (SP K 𝔭) (gramK h β) := fun i j =>
    mem_SP_iff_locF.mpr (hdual _ (hβ j) _ (hβ i))
  have hinv : gramK h β * (gramK h β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcol : ∀ k l, (gramK h β)⁻¹ l k ∈ SP K 𝔭 := by
    intro k l
    obtain ⟨x, hxdef⟩ : ∃ x : V, β.equivFun x = (gramK h β)⁻¹ *ᵥ Pi.single k (1 : K) :=
      ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    have hx : x ∈ locF 𝔭 (spanO β) := by
      rw [← hsd]
      change ∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
      intro y hy
      rw [← mem_SP_iff_locF, form_repr h β, hxdef, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      convert star_mem_SP' hF ((hmemL y).mp hy k) using 1
      simp [dotProduct, Pi.single_apply]
    have hc := (hmemL x).mp hx l
    rw [hxdef] at hc
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hc
  have hdi : ((gramK h β)⁻¹).det = (gramK h β).det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨det_mem_SP hG, ?_⟩
  rw [← hdi]
  exact det_mem_SP fun l k => hcol k l

theorem gram_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    gramK h γ = (β.toMatrix γ)ᴴ * gramK h β * β.toMatrix γ := by
  ext i j
  have e : gramK h γ i j = h (γ i) (γ j) := rfl
  rw [e, form_repr h β, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]

theorem gram_det_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    (gramK h γ).det = star (β.toMatrix γ).det * (gramK h β).det * (β.toMatrix γ).det := by
  rw [gram_change h β γ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

theorem gram_det_orth (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : Basis κ K V)
    (ho : ∀ s t, s ≠ t → h (γ s) (γ t) = 0) : (gramK h γ).det = ∏ s, h (γ s) (γ s) := by
  have e : gramK h γ = Matrix.diagonal fun s => h (γ s) (γ s) := by
    ext s t
    by_cases hst : s = t
    · subst hst; simp [gramK]
    · simp [gramK, Matrix.diagonal_apply_ne _ hst, ho s t hst]
  rw [e, Matrix.det_diagonal]

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
  Formalism.L2.SG.Pf.GluedFormOrthogonality Formalism.L2.SG.Pf.NormUnitsOrthogonality

theorem last_unit_holds : LastUnit := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hCM hFix h hS hN U hUc _ hΛ M _ _ 𝔭 h𝔭 b a hJ _ π w c τ hG j hj
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hwU, hwo, hwn, hτinj, ⟨s₀, hU0⟩, hpair, hτlt, hfree⟩ := hG
  obtain ⟨hbU, hbloc, hbo, hbn, ha0⟩ := hJ
  obtain ⟨Λ₀, hΛlat, hΛu⟩ := hΛ
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast ha0 i
  have hC0 : ∀ k, algebraMap F K (c k) ≠ 0 := fun k => by
    rw [map_ne_zero]
    exact (hwn k).2
  have hπ0 : π ≠ 0 := fun e => hU0.notMem (e ▸ Submodule.zero_mem _)
  have hP0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have hSPπ : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := mem_SP_of_inP (K := K) hU0 (inP_of_mem_pow (K := K) (k := 0) (t := π) (by simp))
    simpa using this
  have hcard : Fintype.card (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) = finrank K V := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Submodule.finrank_add_eq_of_isCompl hUc]
  haveI : Nonempty (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) := ⟨Sum.inr j⟩
  let g : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → V := Sum.elim b w
  have horth : ∀ s t, s ≠ t → h (g s) (g t) = 0 := by
    rintro (i|i) (k|k) hst
    · exact hbo i k (fun e => hst (congrArg Sum.inl e))
    · exact form_U_orth (hbU i) (hwU k)
    · exact form_orth_U hS (hbU k) (hwU i)
    · exact hwo i k (fun e => hst (congrArg Sum.inr e))
  have hnorm : ∀ s, h (g s) (g s) ≠ 0 := by
    rintro (i|i)
    · show h (b i) (b i) ≠ 0
      rw [hbn i]
      exact hA0 i
    · show h (w i) (w i) ≠ 0
      rw [(hwn i).1]
      exact hC0 i
  have hli : LinearIndependent K g := linInd_orth g horth hnorm
  let γ := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hγ : ∀ s, γ s = g s := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s
  have hdetγ : (gramK h γ).det =
      (∏ i, algebraMap F K (a i : F)) * ∏ k, algebraMap F K (c k) := by
    rw [gram_det_orth h γ (fun s t hst => by rw [hγ, hγ]; exact horth s t hst), Fintype.prod_sum_type]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hγ]; exact hbn i)
    · exact Finset.prod_congr rfl (fun k _ => by rw [hγ]; exact (hwn k).1)
  obtain ⟨β, -, hβ⟩ := LocalSpans.exists_basis_locF hΛlat h𝔭
  let e : Fin (finrank K V) ≃ Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  let β' := β.reindex e
  have hsp : spanO β' = Submodule.span (𝓞 K) (Set.range β) := by
    show Submodule.span (𝓞 K) (Set.range ⇑(β.reindex e)) = _
    rw [Basis.range_reindex]
  have hsd : dualF h 𝔭 (locF 𝔭 (spanO β')) = locF 𝔭 (spanO β') := by
    rw [hsp, hβ, ← G7.locF_dual hFix h hΛlat.fg h𝔭.isPrime, (hΛu : HermitianLatticesTheory.dual h Λ₀ = Λ₀)]
  obtain ⟨hu1, hu2⟩ := det_unit_of_selfdual hFix hS hN β' hsd
  have hd : (β'.toMatrix γ).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip β' γ)
  have hNUγ : NU 𝔭 (gramK h γ).det := by
    rw [gram_det_change h β' γ]
    exact NU.norm_mul hu1 hu2 hd
  have hunitA : ∀ i, vF 𝔭 (a i) = 0 → NU 𝔭 (algebraMap F K (a i : F)) := by
    intro i hv
    apply NU.of_unit
    · have := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
      rw [hv] at this
      simpa using this
    · have := unit_part hCM hFix h𝔭 hU0 (ha0 i)
      rw [hv] at this
      simpa using this
  have hunitC : ∀ k : Fin (finrank K (orthK h U)), (k : ℕ) + 1 < finrank K (orthK h U) →
      (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ k) → NU 𝔭 (algebraMap F K (c k)) := by
    intro k hk hk'
    obtain ⟨h1, h2⟩ := hfree k hk hk'
    apply NU.of_unit
    · simpa using mem_SP_of_inP (K := K) hU0 h1
    · simpa using mem_SP_of_inP (K := K) hU0 h2
  have hpairNU : ∀ i, vF 𝔭 (a i) ≠ 0 →
      NU 𝔭 (algebraMap F K (a i : F) * algebraMap F K (c (τ i))) := by
    intro i hv
    obtain ⟨-, hCu⟩ := unit_part_c hCM hFix h𝔭 hU0 (ha0 i) hv (hpair i hv)
    have hAu := unit_part hCM hFix h𝔭 hU0 (ha0 i)
    have hAd := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
    have hs := mem_SP_of_inP (K := K) hU0 (hpair i hv)
    rw [map_add] at hs
    set A := algebraMap F K (a i : F)
    set C := algebraMap F K (c (τ i))
    set P := algebraMap F K (π : F)
    set v := vF 𝔭 (a i)
    have e1 : P ^ v * P⁻¹ ^ v = 1 := by rw [← mul_pow, mul_inv_cancel₀ hP0, one_pow]
    have hCd : P⁻¹ ^ v * C ∈ SP K 𝔭 := by
      have e2 : P⁻¹ ^ v * C = P ^ v * (P⁻¹ ^ (2 * v) * (A + C)) - P⁻¹ ^ v * A := by
        rw [two_mul, pow_add]
        linear_combination (-(P⁻¹ ^ v * (A + C))) * e1
      rw [e2]
      exact sub_mem (mul_mem (pow_mem hSPπ _) hs) hAd
    apply NU.pair (hA0 i) (star_fix hFix _)
    · have e3 : C * A⁻¹ = (P⁻¹ ^ v * C) * (A⁻¹ * P ^ v) := by
        linear_combination (-(C * A⁻¹)) * e1
      rw [e3]
      exact mul_mem hCd hAu
    · have e3 : A * C⁻¹ = (P⁻¹ ^ v * A) * (C⁻¹ * P ^ v) := by
        linear_combination (-(A * C⁻¹)) * e1
      rw [e3]
      exact mul_mem hAd hCu
  let T := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0)
  let S := T.image τ
  have hSj : S ⊆ Finset.univ.erase j := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro e
    have := hτlt i (Finset.mem_filter.mp hi).2
    rw [e] at this
    omega
  have hinjT : Set.InjOn τ T := fun i hi k hk e =>
    hτinj i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2 e
  have hCprod : ∏ k, algebraMap F K (c k) = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (c (τ i))) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => algebraMap F K (c k)) (Finset.mem_univ j),
      ← Finset.prod_sdiff hSj, Finset.prod_image hinjT]
    ring
  have hAprod : ∏ i, algebraMap F K (a i : F) = (∏ i ∈ T, algebraMap F K (a i : F)) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have htot : (gramK h γ).det = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [hdetγ, hAprod, hCprod, Finset.prod_mul_distrib]
    ring
  have hX : NU 𝔭 ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    refine NU.mul (NU.mul ?_ ?_) ?_
    · exact NU.prod _ _ fun i hi => hpairNU i (Finset.mem_filter.mp hi).2
    · exact NU.prod _ _ fun i hi => hunitA i (by simpa using (Finset.mem_filter.mp hi).2)
    · refine NU.prod _ _ fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk1).1
      apply hunitC k
      · have h1 := k.isLt
        have h2 := Fin.val_ne_of_ne hkj
        omega
      · intro i hi e
        exact hk2 (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e⟩)
  have hX0 : (∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    · exact mul_ne_zero (hA0 i) (hC0 _)
    · exact hA0 i
    · exact hC0 i
  rw [htot] at hNUγ
  exact NU.of_mul_left hNUγ hX hX0

end Formalism.L2.SG.Pf.Cnt
end
end

section
namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_holds : GlueExists :=
  glueExists_of_last last_unit_holds

end Formalism.L2.SG.Pf.Cnt
end
