import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunIffRowSlopeBound

noncomputable section

open Module NumberField IsDedekindDomain Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions
open scoped Matrix InnerProductSpace ComplexOrder

namespace GlobalTheory.Mem.RowSides

section Semi

variable {K : Type} [Field K] {σ : K →+* ℂ} {U V W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]



theorem semi_injective_of_basis {ι : Type} [Fintype ι] (b : Basis ι K U) (g : U →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun i => g (b i)) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← b.sum_repr x, map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h (fun i => σ (b.repr x i)) hx
  refine b.repr.injective (Finsupp.ext fun i => σ.injective ?_)
  simpa using this i

end Semi

section Polar

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem majAt_expand {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + a • y) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 + Formalism.HermitianLatticesTheory.normAt b X v (a • y) ^ 2 +
      2 * (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  have hs : Formalism.HermitianLatticesTheory.fcoord b X v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v y := by
    have : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    rw [Formalism.HermitianLatticesTheory.fcoord, this, Matrix.mulVec_smul]; rfl
  simp only [normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, hs, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Complex.star_def, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_eq_of_normAt [IsTotallyComplex K] {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (e : V →ₗ[K] W)
    (h : ∀ x, Formalism.HermitianLatticesTheory.normAt b' X' v (e x) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have key : ∀ a : K, (v.embedding a * Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y)).re =
      (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := fun a => by
    have h1 := majAt_expand b X v a x y
    have h2 := majAt_expand b' X' v a (e x) (e y)
    rw [← map_smul, ← map_add, h, h, h] at h2
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hn
    push Not at hn
    have hc := IsTotallyComplex.isComplex v
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (hn x)
  have h1 := key 1
  have h2 := key a
  simp only [map_one, one_mul] at h1
  simp only [Complex.mul_re, h1] at h2
  refine Complex.ext h1 (mul_left_cancel₀ ha ?_)
  linarith

end Polar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

def goodForm : (Fin (B.nV ℓ) → K) →ₗ[K] B.S.Forms :=
  (B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin

theorem goodForm_apply (u : Fin (B.nV ℓ) → K) : goodForm B ℓ u = B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) := rfl





theorem csum_eq_dot (f g : B.S.Forms) :
    B.S.csum f g = star (B.S.basis.equivFun f) ⬝ᵥ B.S.H.mulVec (B.S.basis.equivFun g) := by
  have h := B.S.csum_sum (B.S.basis.equivFun f) (B.S.basis.equivFun g)
  rw [CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
  rw [h]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

variable {B ℓ} {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)

include hv0 h hX in

theorem csum_perp {Z : Submodule K B.S.Forms} (hZ : ∀ g, ∀ z ∈ Z, B.r g z ∈ Z) {z : B.S.Forms} (hz : z ∈ Z)
    {u : Fin (B.nV ℓ) → K} (hu : (B.Pq ℓ Z).mulVec u = 0) : B.S.csum z (goodForm B ℓ u) = 0 := by
  have hU : u ∈ B.U ℓ Z := by rw [← BlockDat.ker_Pq hv0 h hX]; exact hu
  set a := goodAt ℓ.X ℓ.P ℓ.ψ with ha
  have hp := good_at_spec K v0 hv0 G ℓ.X hX ℓ.P ℓ.ψ
  have hez : B.S.gaOp B.r a z ∈ Z := by
    unfold CSD.gaOp
    rw [LinearMap.sum_apply]
    exact Z.sum_mem fun t _ => Z.smul_mem _ (hZ t z hz)
  obtain ⟨w, hw⟩ := B.exists_vE_of_fix ℓ (φ := B.S.gaOp B.r a z) (by rw [← B.gaOp_mul, hp.idem])
  have hw0 : w ∈ B.Z0 ℓ Z := (B.mem_goodPart_iff ℓ Z w).2 (hw ▸ hez)
  have h0 := hU w hw0
  rw [RationalHermitianForm.hform_eq_dot] at h0
  have hH : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  have hc : ((Nat.card ℓ.P : K)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hH, Matrix.smul_mulVec, dotProduct_smul, smul_eq_zero, or_iff_right hc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h0
  have hfix := B.gaOp_fix ℓ hp.idem u
  have hadj := group_action_matrix_adjoint K B.S G B.r h.act a
  rw [hp.selfAdj] at hadj
  have hw' : (B.vE ℓ).mulVec w = (B.S.gaMat B.r a).mulVec (B.S.basis.equivFun z) := by
    rw [CSD.gaMat_mulVec_equivFun, ← hw, LinearEquiv.apply_symm_apply]
  rw [csum_eq_dot, goodForm_apply, ← hfix, ← CSD.gaMat_mulVec_equivFun, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
    ← hadj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← hw']
  exact h0

include hv0 h hX in

theorem map_goodForm {Z : Submodule K B.S.Forms} (hZ : ∀ g, ∀ z ∈ Z, B.r g z ∈ Z) {σ : K →+* ℂ} {H E : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (j : B.S.Forms →ₛₗ[σ] H) (hj : ∀ f g, ⟪j f, j g⟫_ℂ = σ (B.S.csum f g)) (Θ : H →ₗ[ℂ] E)
    (hΘ : Submodule.span ℂ (j '' (Z : Set B.S.Forms)) = LinearMap.range (LinearMap.adjoint Θ)) (u : Fin (B.nV ℓ) → K) :
    Θ (j (goodForm B ℓ u)) = Θ (j (B.toF ℓ Z ((B.Pq ℓ Z).mulVec u))) := by
  set u' := u - (B.zE ℓ Z).mulVec ((B.Pq ℓ Z).mulVec u) with hu'
  have hu0 : (B.Pq ℓ Z).mulVec u' = 0 := by
    rw [hu', Matrix.mulVec_sub, Matrix.mulVec_mulVec _ (B.Pq ℓ Z), (BlockDat.Pq_orth hv0 h hX).1, Matrix.one_mulVec, sub_self]
  have h0 : Θ (j (goodForm B ℓ u')) = 0 := by
    have hm : LinearMap.adjoint Θ (Θ (j (goodForm B ℓ u'))) ∈ Submodule.span ℂ (j '' (Z : Set B.S.Forms)) := by
      rw [hΘ]; exact ⟨_, rfl⟩
    have hle : Submodule.span ℂ (j '' (Z : Set B.S.Forms)) ≤ (ℂ ∙ j (goodForm B ℓ u'))ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, hj, csum_perp hv0 h hX hZ hz hu0, map_zero]
    have := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hm)
    rw [LinearMap.adjoint_inner_left] at this
    exact inner_self_eq_zero.1 this
  rw [hu', map_sub, map_sub, map_sub, sub_eq_zero] at h0
  exact h0

include hv0 h hX in

theorem normAt_goodForm (v : InfinitePlace K) (u : Fin (B.nV ℓ) → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K _) (stdFrame (B.HV ℓ)) v u ^ 2 =
      (Nat.card ℓ.P : ℝ)⁻¹ * Formalism.HermitianLatticesTheory.normAt B.S.basis (stdFrame B.S.H) v (goodForm B ℓ u) ^ 2 := by
  have h1 : Formalism.HermitianLatticesTheory.normAt B.S.basis (stdFrame B.S.H) v (goodForm B ℓ u) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K _) (stdFrame B.S.H) v ((B.vE ℓ).mulVec u) := by
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    congr 2
    funext i
    rw [goodForm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hH : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  have hE : ((B.vE ℓ)ᴴ).map v.embedding = ((B.vE ℓ).map v.embedding)ᴴ :=
    map_conjTranspose' _ _ fun i a => isCMSub_cmMax' K _ _ (BlockDat.vE_rat hv0 h hX i a)
  have hm : (B.HV ℓ).map v.embedding =
      (((Nat.card ℓ.P : ℝ)⁻¹ : ℝ) : ℂ) • (((B.vE ℓ).map v.embedding)ᴴ * B.S.H.map v.embedding * (B.vE ℓ).map v.embedding) := by
    rw [← hE, ← Matrix.map_mul, ← Matrix.map_mul, hH]
    ext i k
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
    push_cast
    rfl
  rw [h1, normAt_sq_eq_majAt, normAt_sq_eq_majAt, Formalism.L2.DIV.majAt_eq, Formalism.L2.DIV.majAt_eq, stdFrame, stdFrame,
    (frameOfSpec _ _ (BlockDat.HV_pos hv0 h hX v)).2, (frameOfSpec _ _ (h.hpos v)).2, hm, emb_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

end Block

end GlobalTheory.Mem.RowSides

end
