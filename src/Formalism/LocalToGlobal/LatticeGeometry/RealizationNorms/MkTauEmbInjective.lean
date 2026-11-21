import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

section
open Matrix
open scoped ComplexOrder

namespace Formalism.L2.Geo.Rec.TraceQuadraticBound

variable {n : Type} [Fintype n] [DecidableEq n]

theorem exists_star_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, hB⟩

theorem frame_exists {A : Matrix n n ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) :
    ∃ X : Matrix n n ℂ, X * Xᴴ = A ∧ IsUnit X.det := by
  obtain ⟨B, rfl⟩ := exists_star_mul_self hA
  refine ⟨Bᴴ, by rw [conjTranspose_conjTranspose], ?_⟩
  rw [det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd)

theorem re_star_dot_self (v : n → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem norm_sum_sq_le (a w : n → ℂ) : ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖w k‖ ^ 2 := by
  have h1 : ‖∑ k, a k * w k‖ ≤ ∑ k, ‖a k‖ * ‖w k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖w k‖)
  have h0 : 0 ≤ ‖∑ k, a k * w k‖ := norm_nonneg _
  calc ‖∑ k, a k * w k‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖w k‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2



theorem trace_nonneg {b : Matrix n n ℂ} (hb : b.PosSemidef) (Y : Matrix n n ℂ) :
    0 ≤ (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [e2, hH]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity

theorem trace_pos {b : Matrix n n ℂ} (hb : b.PosSemidef) (hb0 : b ≠ 0) (Y : Matrix n n ℂ)
    (hY : IsUnit Y.det) : 0 < (b * (Y * Yᴴ)).trace.re := by
  obtain ⟨H, hH⟩ := exists_star_mul_self (hb.conjTranspose_mul_mul_same Y)
  have e2 : (b * (Y * Yᴴ)).trace = (Yᴴ * b * Y).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have e3 : (Hᴴ * H).trace.re = ∑ j, ∑ k, ‖H k j‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']; norm_cast
  rw [e2, hH, e3]
  by_contra hle
  have hs : ∑ j, ∑ k, ‖H k j‖ ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity)
  have hH0 : H = 0 := by
    ext k j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => by positivity)).1 hs j
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h1 k (Finset.mem_univ _)
    simpa using h2
  apply hb0
  have hYi : IsUnit Yᴴ.det := by rw [det_conjTranspose]; exact hY.star
  have hz : Yᴴ * b * Y = 0 := by rw [hH, hH0]; simp
  calc b = (Yᴴ⁻¹ * Yᴴ) * b * (Y * Y⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hYi, Matrix.mul_nonsing_inv _ hY]; simp
    _ = Yᴴ⁻¹ * (Yᴴ * b * Y) * Y⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz]; simp

section Dense

variable {K : Type} [Field K]

theorem denseRange_emb (σ : K →+* ℂ) (z : K) (hz : (σ z).im ≠ 0) : DenseRange σ := by
  let g : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * σ z
  have hg : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    intro w
    refine ⟨(w.re - w.im / (σ z).im * (σ z).re, w.im / (σ z).im), ?_⟩
    apply Complex.ext
    · simp [g]
    · simp [g]; field_simp
  have hq : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h := hgs.denseRange.comp hq hg
  refine h.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(a : K) + (b : K) * z, by simp [g]⟩

theorem psd_map {m : ℕ} (cj : K → K) (σ : K →+* ℂ) (hσ : ∀ z, σ (cj z) = star (σ z)) (hd : DenseRange σ)
    (A : Matrix (Fin m) (Fin m) K) (hH : ∀ i k, A k i = cj (A i k))
    (hP : ∀ l : Fin m → K, l ≠ 0 → 0 < (σ (∑ i, ∑ k, l i * A i k * cj (l k))).re) :
    (A.map σ).PosSemidef ∧ (A.map σ).det ≠ 0 := by
  have hHm : (A.map σ).IsHermitian := by
    ext i k
    simp only [conjTranspose_apply, map_apply]
    rw [hH, hσ, star_star]
  have key : ∀ l : Fin m → K, σ (∑ i, ∑ k, l i * A i k * cj (l k)) =
      star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k))) := by
    intro l
    simp only [map_sum, map_mul, hσ, dotProduct, mulVec, map_apply, Pi.star_apply, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hden : DenseRange (fun l : Fin m → K => fun k => star (σ (l k))) := by
    have h1 : DenseRange (fun z : K => star (σ z)) :=
      (Function.RightInverse.surjective (f := (star : ℂ → ℂ)) (g := star) star_star).denseRange.comp hd
        continuous_star
    exact DenseRange.piMap (f := fun _ : Fin m => fun z : K => star (σ z)) (fun _ => h1)
  have hre : ∀ x : Fin m → ℂ, 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re := by
    intro x
    refine hden.induction_on (p := fun x => 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re) x ?_ ?_
    · apply isClosed_le continuous_const
      simp only [dotProduct, mulVec, Pi.star_apply]
      fun_prop
    · intro l
      show 0 ≤ (star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k)))).re
      by_cases hl : l = 0
      · subst hl
        rw [show (fun k : Fin m => star (σ ((0 : Fin m → K) k))) = 0 by funext k; simp]
        simp
      · rw [← key]; exact (hP l hl).le
  refine ⟨PosSemidef.of_dotProduct_mulVec_nonneg hHm fun x => ?_, ?_⟩
  · rw [Complex.nonneg_iff]
    exact ⟨hre x, (hHm.im_star_dotProduct_mulVec_self x).symm⟩
  · rw [show (A.map σ).det = σ A.det from (RingHom.map_det σ A).symm]
    intro h0
    apply (map_eq_zero_iff σ σ.injective).not.mpr ?_ h0
    intro hdet
    obtain ⟨l, hl, hlA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have := hP l hl
    have e : ∑ i, ∑ k, l i * A i k * cj (l k) = ∑ k, (l ᵥ* A) k * cj (l k) := by
      simp only [vecMul, dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e, hlA] at this
    simp at this

end Dense

end Formalism.L2.Geo.Rec.TraceQuadraticBound

open NumberField NumberField.InfinitePlace

namespace Formalism.L2.Geo.Rec.TraceSumEmbeddings

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

end Formalism.L2.Geo.Rec.TraceSumEmbeddings
end

section
open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

abbrev Amb (K : Type) [Field K] [NumberField K] (n : ℕ) : Type :=
  EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def fc (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) : Fin n → ℂ :=
  (Xf v)⁻¹ *ᵥ (fun i => v.embedding (x i))

def mkE (c : InfinitePlace K → Fin n → ℂ) : Amb K n :=
  WithLp.toLp 2 (fun p => if p.2.2 = 0 then (c p.1 p.2.1).re else (c p.1 p.2.1).im)

theorem sum_ulift_finset_fin_two_expand (g : Fin 2 → ℝ) : ∑ k, g k = g 0 + g 1 := Fin.sum_univ_two g

theorem inner_mkE (a c : InfinitePlace K → Fin n → ℂ) :
    inner ℝ (mkE a) (mkE c) = ∑ v, ∑ i, (star (a v i) * c v i).re := by
  simp only [mkE, PiLp.inner_apply, PiLp.toLp_apply, Fintype.sum_prod_type, sum_ulift_finset_fin_two_expand]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

theorem norm_sq_mkE (c : InfinitePlace K → Fin n → ℂ) :
    ‖mkE c‖ ^ 2 = ∑ v, ∑ i, ‖c v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_mkE]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

variable [StarRing K]

theorem realize_eq (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = mkE (fun v => fc Xf v x) := by
  ext p
  have h : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) p.1 x = fun i => p.1.embedding (x i) := by
    funext i
    unfold Formalism.HermitianLatticesTheory.vecAt
    simp
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Formalism.HermitianLatticesTheory.fcoord, mkE, fc, h]

def yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → K) : Amb K n :=
  mkE (fun v => (2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i)))))


variable [IsTotallyComplex K]



end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem nPl_mul_two [IsTotallyComplex K] : Fintype.card (InfinitePlace K) * 2 = finrank ℚ K := by
  rw [NumberField.IsTotallyComplex.finrank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  ring


theorem exists_int_smul_mem (X : Submodule (𝓞 K) (Fin n → K))
    (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • v ∈ X := by
  classical
  have hv : v ∈ Submodule.span K (X : Set (Fin n → K)) := by rw [hX]; trivial
  obtain ⟨m, f, g, hg⟩ := (Submodule.mem_span_set' (R := K)).1 hv
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • f i, hi⟩
  have hr : y • (f i • (g i : Fin n → K)) = r • (g i : Fin n → K) := by
    rw [← algebraMap_smul K r, ← smul_assoc]
    rfl
  rw [hr]
  exact X.smul_mem r (g i).2

variable [StarRing K]

def Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K)) :
    Submodule ℤ (Amb K n) :=
  Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf) X




end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]


theorem norm_sq_realize (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x‖ ^ 2 = ∑ v, ∑ i, ‖fc Xf v x i‖ ^ 2 := by
  rw [realize_eq, norm_sq_mkE]


end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
end
end
end
end

section
namespace Formalism.L2.Geo.Rec

open Formalism.BasicNotions

end Formalism.L2.Geo.Rec
end

section
open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

variable (D : D7)

instance totCx : IsTotallyComplex D.host.E :=
  (D.host.isCMField_hostE).to_isTotallyComplex

theorem conjugate_emb (g : D.R.GG) :
    ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  rw [show ((D.host.conj : D.host.E →+* D.host.E) z) = D.host.conj z from rfl, Formalism.MainNotions.WeightFamilies.emb_conj]
  rfl

theorem mk_tauEmb_injective : Function.Injective fun τ : D.what₂.Tau => InfinitePlace.mk (DV.tauEmb D τ) := by
  intro τ τ' h
  simp only at h
  rcases mk_eq_iff.1 h with h1 | h1
  · have h2 := (factEmb D.R D.host).1.1 h1
    exact D.eTau.injective (Subtype.ext h2)
  · exfalso
    unfold DV.tauEmb at h1
    rw [conjugate_emb] at h1
    have h2 := (factEmb D.R D.host).1.1 h1
    have hm := (D.eTau τ).2
    rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem] at hm
    exact hm (h2 ▸ (D.eTau τ').2)

theorem card_places : Fintype.card (InfinitePlace D.host.E) = Fintype.card D.what₂.Tau := by
  have h1 := DualLatticeEmbeddings.nPl_mul_two (K := D.host.E)
  rw [D.host.finrank_cmField] at h1
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.what₂.card_Tau, h2]
  omega

def ePl : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨mk_tauEmb_injective D, (card_places D).symm⟩)

theorem ePl_embedding (τ : D.what₂.Tau) :
    (ePl D τ).embedding = DV.tauEmb D τ ∨ (ePl D τ).embedding = ComplexEmbedding.conjugate (DV.tauEmb D τ) :=
  embedding_mk_eq _

theorem re_ePl (τ : D.what₂.Tau) (z : D.host.E) :
    ((ePl D τ).embedding z).re = (DV.tauEmb D τ z).re := by
  rcases ePl_embedding D τ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem trF_eq (z : D.host.E) : Formalism.MainNotions.WeightFamilies.trF D z = ∑ v : InfinitePlace D.host.E, (v.embedding z).re := by
  unfold Formalism.MainNotions.WeightFamilies.trF
  rw [← (ePl D).sum_comp]
  exact Finset.sum_congr rfl fun τ _ => (re_ePl D τ z).symm

@[instance_reducible] def starE : StarRing D.host.E := starRingOfComm

attribute [local instance] starE

variable {D}

theorem exists_im_ne (v : InfinitePlace D.host.E) : ∃ z, (v.embedding z).im ≠ 0 := by
  have hc : v.IsComplex := IsTotallyComplex.isComplex v
  rw [isComplex_iff] at hc
  by_contra h
  simp only [not_exists, not_not] at h
  apply hc
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h z)

theorem frames {n : ℕ} (χ : Matrix (Fin n) (Fin n) D.host.E) (hH : Formalism.MainNotions.WeightFamilies.IsHerm D χ)
    (hP : Formalism.MainNotions.WeightFamilies.PosDefE D χ) :
    ∃ Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ,
      (∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) ∧ ∀ v, IsUnit (Xf v).det := by
  have h : ∀ v : InfinitePlace D.host.E, ∃ X : Matrix (Fin n) (Fin n) ℂ,
      X * Xᴴ = χ.map v.embedding ∧ IsUnit X.det := by
    intro v
    obtain ⟨z, hz⟩ := exists_im_ne v
    obtain ⟨h1, h2⟩ := TraceQuadraticBound.psd_map (fun z => D.host.conj z) v.embedding
      (Formalism.MainNotions.WeightFamilies.emb_conj D v.embedding) (TraceQuadraticBound.denseRange_emb v.embedding z hz) χ hH
      (fun l hl => hP l hl v.embedding)
    exact TraceQuadraticBound.frame_exists h1 h2
  choose Xf h1 h2 using h
  exact ⟨Xf, h1, h2⟩

theorem star_mulVec_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star (M *ᵥ w) = M.map star *ᵥ star w := by
  funext i
  simp only [Pi.star_apply, mulVec, dotProduct, star_sum, map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul']


end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}





end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}




end Formalism.L2.Geo.Rec.StarEmbeddingNorm
end
end
end
end
