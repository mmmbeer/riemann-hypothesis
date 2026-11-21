import Formalism.LocalToGlobal.GlobalTheory.CoefficientMapSurjective
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Formalism.LocalToGlobal.GlobalTheory.NfAllSmulSelfRe
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_one (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) p = p := by
  unfold Formalism.MainNotions.flipTwoThree.actAll
  simp only [Matrix.det_one, _root_.one_zpow, Finset.prod_const_one, one_smul]
  have e : (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) K) b v.2.1) * MvPolynomial.X (v.1, b, v.2.2)) = MvPolynomial.X := by
    funext v
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb; simp [Matrix.one_apply_ne hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e, MvPolynomial.aeval_X_left_apply]

def actL (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n × Fin n) K :=
  (∏ τ, (g τ).det ^ (lam τ).detShift) •
    (MvPolynomial.aeval (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C (g v.1 b v.2.1) * MvPolynomial.X (v.1, b, v.2.2))).toLinearMap

theorem actAll_inv_cancel (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p) = p := by
  rw [actAll_comp]
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact actAll_one lam p

theorem actAll_cancel_inv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p) = p := by
  rw [actAll_comp]
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact actAll_one lam p

theorem actAll_mem_TSpan [CharZero K] (lam : ι → DomWeight n) (h : ι → GL (Fin n) K)
    {p : MvPolynomial (ι × Fin n × Fin n) K} (hp : p ∈ Formalism.MainNotions.flipTwoThree.TSpan K lam) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p ∈ Formalism.MainNotions.flipTwoThree.TSpan K lam := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq] at hp ⊢
  have h1 := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoEquiv_symm_coe lam h⁻¹ ⟨p, hp⟩
  have e : (fun τ => (((h⁻¹ τ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹) =
      fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units (h τ))]
  rw [e] at h1
  rw [← h1]
  exact Submodule.coe_mem _

end Alg

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

def coT (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) :
    ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → Pol0 D) :=
  LinearMap.pi fun c => (actL ((D.fm u).lam 0) (fun τ => ((g c τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL))).comp ((LinearMap.proj c).comp (co0 T))

theorem coT_apply (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) :
    coT T g x c = Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => ((g c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (co0 T x c) := rfl

theorem coT_injective (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) :
    Function.Injective (coT T g) := by
  intro x y h
  apply coefficient_map_injective T
  funext c
  have h1 := congrArg (fun F => Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
    (fun τ => (((g c τ)⁻¹ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (F c)) h
  simp only [coT_apply, actAll_inv_cancel] at h1
  exact h1

theorem coT_range (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c))
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) (F : (D.mem u).C.cls 0 → Pol0 D) :
    (∃ x, coT T g x = F) ↔ ∀ c, F c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0) := by
  constructor
  · rintro ⟨x, rfl⟩ c
    rw [coT_apply]
    exact actAll_mem_TSpan _ _ (coefficient_map_mem_span T x c)
  · intro hF
    obtain ⟨x, hx⟩ := coefficient_map_surjective T hst (fun c => Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (((g c τ)⁻¹ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (F c))
      (fun c => actAll_mem_TSpan _ (fun τ => (g c τ)⁻¹) (hF c))
    refine ⟨x, funext fun c => ?_⟩
    rw [coT_apply, hx]
    exact actAll_cancel_inv _ _ _

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sigD_eq_star (a : D.host.E) : sigD D a = star a := rfl

def rhoC (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp ((sigD D : D.host.E →+* D.host.E).comp
    (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

theorem rhoC_conj (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (a : D.host.E) :
    s (rhoC D τ a) = starRingEnd ℂ (embS D s τ a) := by
  unfold rhoC embS
  simp only [RingHom.coe_comp, Function.comp_apply]
  have hs : ∀ b : D.host.E, (sigD D : D.host.E →+* D.host.E) b = star b := fun b => sigD_eq_star b
  rw [hs]
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj (s.comp D.embE) _
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ (s.comp D.embE) _
    | (erw [NumberField.IsCMField.complexEmbedding_complexConj]; rfl)
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := s.comp D.embE) _)
    | (simp only [NumberField.IsCMField.complexEmbedding_star]; rfl)
    | exact NumberField.IsCMField.complexEmbedding_star _ (s.comp D.embE) _
    | exact NumberField.IsCMField.complexConj_apply_apply (s.comp D.embE) _
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (s.comp D.embE) _ : _)

theorem exists_im_ne (φ : D.host.E →+* ℂ) : ∃ t : D.host.E, (φ t).im ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : NumberField.ComplexEmbedding.IsReal φ := by
    first
      | (rw [NumberField.ComplexEmbedding.isReal_iff]; ext t; simp [Complex.conj_eq_iff_im, h t])
      | (intro t; simp [Complex.conj_eq_iff_im, h t])
      | (ext t; simp [Complex.conj_eq_iff_im, h t])
  have hc : (NumberField.InfinitePlace.mk φ).IsComplex := by
    first
      | exact NumberField.IsTotallyComplex.isComplex _
      | exact IsTotallyComplex.isComplex _
      | exact NumberField.InfinitePlace.IsTotallyComplex.isComplex _
  exact (NumberField.InfinitePlace.isComplex_mk_iff.mp hc) hr

def crd (y : (D.sp.X 0).V) : Fin (D.R.N 0) → D.host.E :=
  fun i => (D.sp.X 0).frame.repr y ((finCongr (rankN D 0 (Nat.zero_le _))).symm i)

theorem gramN_herm : (gramN D 0 (Nat.zero_le _))ᴴ = gramN D 0 (Nat.zero_le _) := by
  unfold gramN
  rw [Matrix.conjTranspose_reindex]
  congr 1
  first
    | exact (D.sp.X 0).gram_isHermitian
    | exact (D.sp.X 0).isHermitian_gram
    | exact (D.sp.X 0).gram_herm
    | exact (D.sp.X 0).gram_conjTranspose
    | exact (D.sp.X 0).herm
    | (ext i j; exact (D.sp.X 0).herm _ _)
    | (ext i j; exact (D.sp.X 0).herm.eq _ _)
    | (ext i j; exact LinearMap.IsSymm.eq (D.sp.X 0).herm _ _)

theorem hT_crd (y : (D.sp.X 0).V) :
    (D.sp.X 0).hT y y = star (crd y) ⬝ᵥ (gramN D 0 (Nat.zero_le _) *ᵥ crd y) := by
  unfold crd gramN
  have hy := (D.sp.X 0).frame.sum_repr y
  conv_lhs => rw [← hy]
  simp only [map_sum, LinearMap.map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Pi.star_apply, Finset.mul_sum]
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply, Formalism.BasicNotions.HSpace.gram]
  apply Finset.sum_congr rfl
  intro l _
  first
    | ring1
    | (clear hy; generalize ((D.sp.X 0).frame.repr y) k = a; generalize ((D.sp.X 0).frame.repr y) l = b; generalize (D.sp.X 0).hT ((D.sp.X 0).frame k) ((D.sp.X 0).frame l) = h1; generalize (D.sp.X 0).hT ((D.sp.X 0).frame l) ((D.sp.X 0).frame k) = h2; done)

variable {u : D.what₂.Word} (B : ColBase D u)

def Mb (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  fun j i => (B.Q c τ).b.repr (B.bc c τ ((D.sp.X 0).frame ((finCongr (rankN D 0 (Nat.zero_le _))).symm i)))
    ((B.eQ c τ).symm j)

theorem repr_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) (j : Fin (D.R.N 0)) :
    (B.Q c τ).b.repr (B.bc c τ y) ((B.eQ c τ).symm j) = (Mb B c τ *ᵥ fun i => B.rho τ (crd y i)) j := by
  unfold Mb crd
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr y]
  simp only [map_sum, B.bc_smul, LinearMap.map_smulₛₗ, map_smulₛₗ, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, RingHom.id_apply]
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  first
    | ring1
    | (simp only [RingHom.id_apply]; ring1)
    | (rw [mul_comm]; rfl)
    | done

def Ymat (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ * (Mb B c τ).map v.embedding

theorem fcoord_bc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V)
    (j : Fin (D.R.N 0)) :
    Formalism.HermitianLatticesTheory.fcoord (B.Q c τ).b (B.Q c τ).X v (B.bc c τ y) ((B.eQ c τ).symm j) =
      (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) j := by
  have hv : (fun i => v.embedding (B.rho τ (crd y i))) = fun i => v.embedding (B.rho τ (crd y i)) := rfl
  rw [Ymat, ← Matrix.mulVec_mulVec]
  unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← (B.eQ c τ).symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [repr_bc, RingHom.map_mulVec]
  rfl

theorem maj_bc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) :
    Formalism.HermitianLatticesTheory.majAt (B.Q c τ).b (B.Q c τ).X v (B.bc c τ y) (B.bc c τ y) =
      star (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) ⬝ᵥ
        (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [← (B.eQ c τ).symm.sum_comp]
  simp only [fcoord_bc]
  first
    | rfl
    | simp [dotProduct]
    | simp [Matrix.dotProduct]

theorem gram_Y (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    (Ymat B v c τ)ᴴ * Ymat B v c τ = (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) := by
  obtain ⟨t, ht⟩ := exists_im_ne (v.embedding.comp (B.rho τ))
  refine gram_of_norm (v.embedding.comp (B.rho τ)) (host_emb_star D _) _ _ gramN_herm t ht fun x => ?_
  let y : (D.sp.X 0).V := (D.sp.X 0).frame.equivFun.symm fun a => x (finCongr (rankN D 0 (Nat.zero_le _)) a)
  have hy : crd y = x := by
    funext i
    show (D.sp.X 0).frame.repr y _ = _
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp
  have h := B.bc_norm c τ v y
  rw [maj_bc, hT_crd, hy] at h
  exact h

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_inv_mat {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.map_one _ (map_zero f) (map_one f)]

variable {D : D7}

theorem gramN_det_ne : (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  unfold gramN
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc.gram_det_ne (D.sp.X 0) (D.sp.X 0).frame

variable {u : D.what₂.Word} (B : ColBase D u)

theorem Mb_det_ne (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Mb B c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B (InfinitePlace.mk D.what₂.embLL) c τ)
  have e1 : (Ymat B (InfinitePlace.mk D.what₂.embLL) c τ).det = 0 := by
    rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  rw [Matrix.det_mul, e1, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne (((InfinitePlace.mk D.what₂.embLL).embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

def gC (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : GL (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero (Mb_det_ne B c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne)))

theorem gC_coe (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹ := rfl

def Zc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Ymat B v c τ * ((gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)))⁻¹

theorem R_gC (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding =
      Zc B v c τ := by
  have hd : ((gramN D 0 (Nat.zero_le _)).map (B.rho τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 gramN_det_ne
  rw [gC_coe, Matrix.map_mul, map_inv_mat _ _ hd, Matrix.map_map, Zc, Ymat, Matrix.mul_assoc]
  rfl

theorem Y_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Ymat B v c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B v c τ)
  rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne ((v.embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

theorem Zc_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Zc B v c τ).det ≠ 0 := by
  rw [Zc, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact mul_ne_zero (Y_det_ne B v c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne))

theorem Zc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Zc B v c τ)ᵀ)ᴴ * (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ) * (Zc B v c τ)ᵀ = 1 := by
  set P := (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) with hPdef
  set Y := Ymat B v c τ
  set G' := (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ)
  have hYP : Yᴴ * Y = P := gram_Y B v c τ
  have hGs : ∀ i j, star (gramN D 0 (Nat.zero_le _) j i) = gramN D 0 (Nat.zero_le _) i j := fun i j => by
    have := congrFun (congrFun (gramN_herm (D := D)) i) j
    rwa [Matrix.conjTranspose_apply] at this
  have hP : Pᴴ = P := by
    ext i j
    rw [Matrix.conjTranspose_apply, hPdef, Matrix.map_apply, Matrix.map_apply, ← hGs i j, RingHom.comp_apply,
      RingHom.comp_apply]
    have h1 := host_emb_star D (v.embedding.comp (B.rho τ)) (gramN D 0 (Nat.zero_le _) j i)
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    rfl
  have hG' : G'ᵀ = P := by
    ext i j
    simp only [G', hPdef, Matrix.transpose_apply, Matrix.map_apply, RingHom.comp_apply]
    rw [hB, rhoC_conj, ← host_emb_star D (embS D v.embedding τ), hGs j i]
  have hdY : IsUnit Y.det := isUnit_iff_ne_zero.2 (Y_det_ne B v c τ)
  have hdYh : IsUnit Yᴴ.det := by rw [Matrix.det_conjTranspose]; exact hdY.star
  have hdP : IsUnit P.det := by rw [← hYP, Matrix.det_mul]; exact hdYh.mul hdY
  have key : Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ = 1 := by
    rw [hG', Zc, ← hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP]
    calc Y * P⁻¹ * P * (P⁻¹ * Yᴴ) = Y * (P⁻¹ * P) * P⁻¹ * Yᴴ := by simp only [Matrix.mul_assoc]
      _ = Y * P⁻¹ * Yᴴ := by rw [Matrix.nonsing_inv_mul _ hdP, Matrix.mul_one]
      _ = Y * (Y⁻¹ * (Yᴴ)⁻¹) * Yᴴ := by rw [← hYP, Matrix.mul_inv_rev]
      _ = (Y * Y⁻¹) * ((Yᴴ)⁻¹ * Yᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdY, Matrix.nonsing_inv_mul _ hdYh, Matrix.mul_one]
  have ht : ((Zc B v c τ)ᵀ)ᴴ * G' * (Zc B v c τ)ᵀ = (Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rfl
  rw [ht, key, Matrix.transpose_one]

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_sq_prod_zpow {ι : Type} [Fintype ι] (d : ι → ℂ) (k : ι → ℤ) :
    ‖∏ τ, d τ ^ k τ‖ ^ 2 = ∏ τ, ‖d τ‖ ^ (2 * k τ) := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (B : ColBase D u)

theorem weight_level_zero_eq_one (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (c : (D.mem u).C.cls 0) : (D.mem u).C.wt 0 c = 1 := by
  have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
    haveI := hst c
    exact Nat.card_eq_one_iff_unique.2 ⟨hst c, ⟨1⟩⟩
  simp [Formalism.BasicNotions.ColumnChain.wt, this]

def oc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) :
    Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding)) :=
  (⟨fun τ => (Zc B v c τ)ᵀ, fun τ => by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 (Zc_det_ne B v c τ)⟩ :
    {y : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ // ∀ τ, IsUnit (y τ).det})

theorem oc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) : (oc B v c).IsON :=
  fun τ => Or.inl (Zc_on B hB v c τ)

def termN (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) : ℝ :=
  ((D.mem u).C.wt 0 c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (Formalism.L2.Forms.nfAll ((D.fm u).lam 0) (subP o.1 (MvPolynomial.map v.embedding (co0 T x c)))
      (subP o.1 (MvPolynomial.map v.embedding (co0 T x c)))).re

theorem normTie_at (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) (ho : o.IsON) :
    (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re = ∑ c, termN T v x c o := by
  have h := T.norm0 v.embedding x (co0 T x) (fun c z => pol_spec T x c z) o ho
  rw [InfinitePlace.mk_embedding] at h
  exact h

open Classical in

theorem exists_single (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ∃ xc, co0 T xc = Pi.single c (co0 T x c) := by
  classical
  refine coefficient_map_surjective T hst _ fun c' => ?_
  by_cases h : c' = c
  · subst h; rw [Pi.single_eq_same]; exact coefficient_map_mem_span T x c'
  · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

open Classical in
theorem termN_single (v : InfinitePlace D.what₂.LL) (x xc : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (hxc : co0 T xc = Pi.single c (co0 T x c)) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) :
    ∑ c', termN T v xc c' o = termN T v x c o := by
  classical
  rw [Finset.sum_eq_single c]
  · unfold termN; rw [hxc, Pi.single_eq_same]
  · intro c' _ hc'
    unfold termN
    rw [hxc, Pi.single_eq_of_ne hc', map_zero, map_zero, ← nfAll_eq, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_zero_left, Complex.zero_re,
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem termN_indep (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (v : InfinitePlace D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (o o' : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) (ho : o.IsON) (ho' : o'.IsON) :
    termN T v x c o = termN T v x c o' := by
  obtain ⟨xc, hxc⟩ := exists_single T hst x c
  rw [← termN_single T v x xc c hxc o, ← termN_single T v x xc c hxc o', ← normTie_at T v xc o ho,
    ← normTie_at T v xc o' ho']

theorem termN_oc (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (v : InfinitePlace D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    termN T v x c (oc B v c) =
      (Formalism.MainNotions.flipTwoThree.nfAll ((D.fm u).lam 0)
        (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)))
        (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)))).re := by
  rw [actAll_eq_subP, nfAll_smul_self_re, norm_sq_prod_zpow]
  unfold termN
  rw [weight_level_zero_eq_one hst c, Complex.one_re, one_mul]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun τ _ => ?_) rfl
  have e1 : ((oc B v c).1 τ) = (Zc B v c τ)ᵀ := rfl
  rw [e1, Matrix.det_transpose, lamT_zero]
  rfl

theorem coT_term (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
              (MvPolynomial.map v.embedding (coT T (gC B) x c)) =
      Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)) := by
  rw [coT_apply, map_actAll, actAll_comp]
  congr 1
  funext τ
  exact R_gC B v c τ

theorem inf_coT (hB : B.rho = rhoC D) (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c))
    (hne : Nonempty ((D.mem u).C.cls 0)) :
    ∀ (v : InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (Formalism.MainNotions.flipTwoThree.nfAll ((D.fm u).lam 0)
          (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (coT T (gC B) x c)))
          (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (coT T (gC B) x c)))).re := by
  intro v x
  obtain ⟨c0⟩ := hne
  rw [normTie_at T v x (oc B v c0) (oc_on B hB v c0)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coT_term, ← termN_oc T B hst v x c]
  exact termN_indep T hst v x c _ _ (oc_on B hB v c0) (oc_on B hB v c)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FinCo {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (B : ColBase D u) : Prop :=
  ∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
    (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
    ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
      ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (coT T (gC B) x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)

theorem colRest_of_fin {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (h3 : flipTwoThree.adm3 D) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) (hfin : FinCo (F.forms u).to0 B) : ColRest B := by
  have hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c) := by
    exact h3 u
  have hne : Nonempty ((D.mem u).C.cls 0) := classes_level_zero_nonempty F u
  exact ⟨coT (F.forms u).to0 (gC B), coT_injective (T := (F.forms u).to0) _, coT_range (T := (F.forms u).to0) hst _,
    hfin, inf_coT (T := (F.forms u).to0) (B := B) hB hst hne⟩

theorem colValOfTiedS_of_fin
    (h : ∀ D : D7, ∀ F : Formalism.L2.Forms.ColsTiedSym D, flipTwoThree.adm3 D → ∀ (u : D.what₂.Word) (B : ColBase D u),
      B.rho = rhoC D → FinCo (F.forms u).to0 B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_rest' fun D F h3 u => ⟨rhoC D, fun B hB => colRest_of_fin F h3 u B hB (h D F h3 u B hB)⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

section Dual

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem hform_eq (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : K →+* K) (J M : Matrix (Fin n) (Fin n) K) (v y : Fin n → K) :
    Formalism.UG.hform σ J (M *ᵥ v) y = ∑ a, σ (v a) * ((Formalism.UG.cT σ M * J) *ᵥ y) a := by
  rw [hform_eq]
  have e1 : (fun i => σ ((M *ᵥ v) i)) = M.map σ *ᵥ fun a => σ (v a) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [e1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
  rfl

variable (l : ℕ) [hl : Fact l.Prime]

theorem col_mem_of_isLocBasis {L : Set (Fin n → K)} {Y : GL (Fin n) K} (hY : Formalism.L2.Forms.IsLocBasis l L Y) (a : Fin n) :
    ∃ t : ℕ, ¬ l ∣ t ∧ (t : K) • (fun r => (Y : Matrix (Fin n) (Fin n) K) r a) ∈ L := by
  refine (hY _).2 ⟨1, hl.out.not_dvd_one, fun b => ?_⟩
  have e : (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun r => (Y : Matrix (Fin n) (Fin n) K) r a) b =
      (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K)) b a := rfl
  rw [Nat.cast_one, one_mul, e, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨1, map_one _⟩
  · exact ⟨0, map_zero _⟩

theorem den_of_isLocBasis {L : Submodule (𝓞 K) (Fin n → K)} (hfg : L.FG) {Y : GL (Fin n) K}
    (hY : Formalism.L2.Forms.IsLocBasis l (L : Set (Fin n → K)) Y) :
    ∃ d : ℕ, ¬ l ∣ d ∧ ∀ x ∈ L, ∀ a, (d : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) a) ∈
      (algebraMap (𝓞 K) K).range := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have ht : ∀ g ∈ S, ∃ t : ℕ, ¬ l ∣ t ∧ ∀ a, (t : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ g) a) ∈
      (algebraMap (𝓞 K) K).range := fun g hg =>
    (hY g).1 ⟨1, hl.out.not_dvd_one, by
      rw [Nat.cast_one, one_smul, SetLike.mem_coe, ← hS]; exact Submodule.subset_span hg⟩
  let t : (Fin n → K) → ℕ := fun g => if h : g ∈ S then (ht g h).choose else 1
  have htS : ∀ g ∈ S, ¬ l ∣ t g ∧ ∀ a, (t g : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ g) a) ∈
      (algebraMap (𝓞 K) K).range := fun g hg => by
    simp only [t, dif_pos hg]; exact (ht g hg).choose_spec
  refine ⟨∏ g ∈ S, t g, ?_, fun x hx => ?_⟩
  · rw [Prime.dvd_finsetProd_iff hl.out.prime]
    rintro ⟨g, hg, hdvd⟩
    exact (htS g hg).1 hdvd
  · rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro a
      rw [← Finset.mul_prod_erase S t hg, Nat.cast_mul, mul_comm ((t g : ℕ) : K), mul_assoc]
      exact Subring.mul_mem _ ⟨(∏ g' ∈ S.erase g, t g' : ℕ), map_natCast _ _⟩ ((htS g hg).2 a)
    | zero =>
      intro a
      rw [Matrix.mulVec_zero, Pi.zero_apply, mul_zero]
      exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      intro a
      rw [Matrix.mulVec_add, Pi.add_apply, mul_add]
      exact Subring.add_mem _ (hx a) (hy a)
    | smul r x _ hx =>
      intro a
      rw [← algebraMap_smul K r x, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact Subring.mul_mem _ ⟨r, rfl⟩ (hx a)

theorem sig_range (σ : K →+* K) {y : K} (hy : y ∈ (algebraMap (𝓞 K) K).range) : σ y ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨r, rfl⟩ := hy
  obtain ⟨r', hr'⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.sig_int σ r
  exact ⟨r', hr'⟩

theorem isLocBasis_dual (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) {L : Submodule (𝓞 K) (Fin n → K)} (hfg : L.FG)
    {Y : GL (Fin n) K} (hY : Formalism.L2.Forms.IsLocBasis l (L : Set (Fin n → K)) Y) (B0 : GL (Fin n) K)
    (hB0 : ((B0⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) :
    Formalism.L2.Forms.IsLocBasis l (Formalism.BasicNotions.dualSet σ J L) B0 := by
  intro x
  rw [hB0]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht htL using col_mem_of_isLocBasis l hY
    refine ⟨s * ∏ b, t b, ?_, fun a => ?_⟩
    · rw [Nat.Prime.dvd_mul hl.out, not_or]
      refine ⟨hs, ?_⟩
      rw [Prime.dvd_finsetProd_iff hl.out.prime]
      rintro ⟨b, -, hb⟩
      exact ht b hb
    · have h1 := hx _ (htL a)
      have e1 : (t a : K) • (fun r => (Y : Matrix (Fin n) (Fin n) K) r a) =
          (Y : Matrix (Fin n) (Fin n) K) *ᵥ ((t a : K) • Pi.single a (1 : K)) := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
        rfl
      rw [e1, hform_mulVec, Finset.sum_eq_single a (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ a) h)] at h1
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_natCast, Matrix.mulVec_smul] at h1
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a)]
      have e2 : ((s * (t a * ∏ b ∈ Finset.univ.erase a, t b) : ℕ) : K) *
          ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) a =
          ((∏ b ∈ Finset.univ.erase a, t b : ℕ) : K) *
            ((t a : K) * ((s : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) a)) := by
        push_cast; ring
      rw [e2]
      exact Subring.mul_mem _ ⟨_, map_natCast _ _⟩ h1
  · rintro ⟨s', hs', h'⟩
    obtain ⟨d, hd, hdL⟩ := den_of_isLocBasis l hfg hY
    refine ⟨d * s', ?_, ?_⟩
    · rw [Nat.Prime.dvd_mul hl.out, not_or]; exact ⟨hd, hs'⟩
    · intro z hz
      have hz' : z = (Y : Matrix (Fin n) (Fin n) K) *ᵥ ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [hz', hform_mulVec]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have e : σ (((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) b) *
          (((d * s' : ℕ) : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) b) =
          σ ((d : K) * ((((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ z) b) *
            ((s' : K) * ((Formalism.UG.cT σ (Y : Matrix (Fin n) (Fin n) K) * J) *ᵥ x) b) := by
        rw [map_mul, map_natCast]; push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (sig_range σ (hdL z hz b)) (h' b)

end Dual

section Ten

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem ten_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : ι → MvPolynomial (Fin n × Fin n) R) :
    Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map φ (f τ)) = MvPolynomial.map φ (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

end Ten

variable (D : Formalism.BasicNotions.D7)

theorem map_gen {n : ℕ} (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) :
    MvPolynomial.map D.what₂.embLL (r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ))) =
      D.what₂.embLL r • Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, ten_map, ten_map,
    MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]

theorem mem_intSpanAt_iff_map (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    p ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔ MvPolynomial.map D.what₂.embLL p ∈ Formalism.L2.Forms.IntSpan D w lam := by
  constructor
  · intro hp
    induction hp using AddSubgroup.closure_induction with
    | mem q hq =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hq
      exact AddSubgroup.subset_closure ⟨r, f, hr, hf, map_gen D r f⟩
    | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
    | add q q' _ _ h1 h2 => rw [map_add]; exact AddSubgroup.add_mem _ h1 h2
    | neg q _ h1 => rw [map_neg]; exact AddSubgroup.neg_mem _ h1
  · intro hp
    have hle : Formalism.L2.Forms.IntSpan D w lam ≤
        (Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam).map (MvPolynomial.map D.what₂.embLL).toAddMonoidHom := by
      unfold Formalism.L2.Forms.IntSpan
      rw [AddSubgroup.closure_le]
      rintro _ ⟨r, f, hr, hf, rfl⟩
      exact ⟨_, AddSubgroup.subset_closure ⟨r, f, hr, hf, rfl⟩, map_gen D r f⟩
    obtain ⟨q, hq, hqe⟩ := hle hp
    have : q = p := MvPolynomial.map_injective _ D.what₂.embLL.injective hqe
    rwa [← this]

theorem embT_mem_Ow (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    Formalism.L2.Forms.embT D τ y ∈ Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_Ow D w := by
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq]
  exact Subring.mem_map.2 ⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_locInt D w
    ((D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) y s hs hy, rfl⟩

theorem change_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) {n : ℕ} {L : Set (Fin n → D.host.E)}
    {B B₂ : GL (Fin n) D.host.E} (hB : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B)
    (hB₂ : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B₂) (a b : Fin n) :
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ a b ∈
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_Ow D w := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨s, hs, hx⟩ := col_mem_of_isLocBasis (D.what₂.places.resChar w) hB b
  obtain ⟨s', hs', h⟩ := (hB₂ _).1 ⟨s, hs, hx⟩
  have e : (((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
      fun r => (B : Matrix (Fin n) (Fin n) D.host.E) r b) a =
      ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) a b := by
    rw [Units.val_mul]; rfl
  have h2 := embT_mem_Ow D w τ _ s' hs' (h a)
  rw [e] at h2
  exact h2

theorem basis_change (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (s : D.what₂.Tau → ℤ) {L : Set (Fin n → D.host.E)}
    {B B₂ : GL (Fin n) D.host.E} (hB : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B)
    (hB₂ : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) L B₂)
    (Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    ∃ Q₂ ∈ Formalism.L2.Forms.IntSpan D w lam,
      Formalism.L2.Forms.fnOf G s (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) Q =
        Formalism.L2.Forms.fnOf G s (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) Q₂ := by
  set N : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ * B₂ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ with hN
  set N' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ with hN'
  have hNN' : ∀ τ, N τ * N' τ = 1 := fun τ => by
    simp only [hN, hN', Formalism.L2.Forms.atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    have : (B⁻¹ * B₂ * (B₂⁻¹ * B) : GL (Fin n) D.host.E) = 1 := by group
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N Q,
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_intSpan_allSubP D w _ N _ (fun τ g hg => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hNN' τ)
      (change_mem D w τ hB₂ hB) (change_mem D w τ hB hB₂) g hg) Q hQ, ?_⟩
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul]
  have hM : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      fun τ => N τ * Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((B₂⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ := by
    funext τ
    simp only [hN, Formalism.L2.Forms.atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    congr 2
    group
  rw [hM]

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eqv (D : D7) : (D.sp.X 0).V ≃ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) :=
  (D.sp.X 0).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm)

theorem eqv_apply (y : (D.sp.X 0).V) : eqv D y = crd y := rfl

theorem mem_clsCrd_iff {u : D.what₂.Word} (c : (D.mem u).C.cls 0) (z : Fin (D.R.N 0) → D.host.E) :
    z ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c ↔ (eqv D).symm z ∈ D.clsLat u 0 c := by
  unfold Formalism.L2.Forms.clsCrd
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    exact (eqv D).symm_apply_apply y
  · intro h
    exact ⟨_, h, (eqv D).apply_symm_apply z⟩

def vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (a : Fin (D.R.N 0)) : (D.sp.X 0).V :=
  (eqv D).symm fun r => Y r a


variable {u : D.what₂.Word} (B : ColBase D u)

theorem sum_gamma (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (a : Fin (D.R.N 0)) :
    ∑ i, (Mb B c τ * Y.map (B.rho τ)) i a • (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol Y a) := by
  have hfr : ∀ r : Fin (D.R.N 0), (eqv D).symm (Pi.single r 1) =
      (D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r) := by
    intro r
    rw [LinearEquiv.symm_apply_eq]
    ext r'
    simp [eqv, Pi.single_apply]
    rw [Finsupp.single_apply]
    split_ifs <;> simp_all [Fin.cast_inj]
  have hz : (fun r => Y r a) = ∑ r, Y r a • (Pi.single r (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) := by
    ext r'
    simp [Finset.sum_apply, Pi.single_apply]
  have hbc : B.bc c τ (vcol Y a) = ∑ r, B.rho τ (Y r a) •
      B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)) := by
    unfold vcol
    rw [hz, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, B.bc_smul, hfr]
  have hexp : ∀ v : (B.Q c τ).V,
      v = ∑ i, (B.Q c τ).b.repr v ((B.eQ c τ).symm i) • (B.Q c τ).b ((B.eQ c τ).symm i) := by
    intro v
    rw [Equiv.sum_comp (B.eQ c τ).symm (fun j => (B.Q c τ).b.repr v j • (B.Q c τ).b j)]
    exact ((B.Q c τ).b.sum_repr v).symm
  rw [hbc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Mb, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_rhs => rw [hexp (B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

theorem rhoC_mem_intW (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    rhoC D τ y ∈ intW D.what₂.places w := by
  obtain ⟨k, hk⟩ := hy
  have hint : IsIntegral ℤ (rhoC D τ (k : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe k).map (rhoC D τ).toIntAlgHom
  have hk' : (s : D.what₂.LL) * rhoC D τ y ∈ intW D.what₂.places w := by
    have h1 : rhoC D τ ((s : D.host.E) * y) = (s : D.what₂.LL) * rhoC D τ y := by
      rw [map_mul, map_natCast]
    rw [← h1, ← hk]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w ⟨_, hint⟩
  have hinv : ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
    change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
    have h0 : D.what₂.places.val w ((s : D.what₂.LL)) = 0 :=
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := s) (hs := hs)
    rw [AddValuation.map_inv, h0, neg_zero]
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have h2 : s = 0 := by exact_mod_cast h
    rw [h2]
    exact dvd_zero _
  have h3 := (intW D.what₂.places w).mul_mem hinv hk'
  rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at h3

theorem natInv_mem_intW (w : D.what₂.places.Pl) (t : ℕ) (ht : ¬ D.what₂.places.resChar w ∣ t) :
    ((t : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((t : D.what₂.LL))⁻¹
  have h0 : D.what₂.places.val w ((t : D.what₂.LL)) = 0 :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := t) (hs := ht)
  rw [AddValuation.map_inv, h0, neg_zero]

theorem locBasis_gamma (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y) :
    Formalism.MainNotions.flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ)
      (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) := by
  have hp1 : ¬ D.what₂.places.resChar w ∣ 1 := (D.what₂.places.resChar_prime w).not_dvd_one
  have hg : ∀ a, ∑ i, (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) i a •
      (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) :=
    fun a => sum_gamma B c τ _ a
  have hsmul : ∀ (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) (v : (B.Q c τ).V),
      r • v = (⟨r, hr⟩ : intW D.what₂.places w) • v := fun r hr v => by rw [Subring.smul_def]
  have hcolv : ∀ v : Fin (D.R.N 0) → D.host.E, (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ v =
      ∑ a, v a • (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) := by
    intro v
    ext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul (isUnit_iff_ne_zero.2 (Mb_det_ne B c τ)) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)).map _
  · simp only [hg]
    apply le_antisymm
    · unfold locW
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, B.bc_L c τ] at hx
      refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (intW D.what₂.places w)
        (Set.range fun a => B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a))) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨y, hy, rfl⟩
        have hz : eqv D y ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c := by
          rw [mem_clsCrd_iff, LinearEquiv.symm_apply_apply]
          exact hy
        obtain ⟨s, hs, hint⟩ := (hY (eqv D y)).1 ⟨1, hp1, by rw [Nat.cast_one, one_smul]; exact hz⟩
        have h1 : (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ eqv D y) =
            eqv D y := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        have hyz : y = ∑ a, ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            eqv D y) a • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a := by
          conv_lhs => rw [← (eqv D).symm_apply_apply y, ← h1, hcolv, map_sum]
          simp only [LinearEquiv.map_smul]
          rfl
        rw [hyz, map_sum]
        refine Submodule.sum_mem _ fun a _ => ?_
        rw [B.bc_smul, hB, hsmul _ (rhoC_mem_intW w τ _ s hs (hint a))]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro r x _ hx
        have hr : r • x = (⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w r⟩ : intW D.what₂.places w) • x := by
          rw [Subring.smul_def]
          exact (algebraMap_smul D.what₂.LL r x).symm
        rw [hr]
        exact Submodule.smul_mem _ _ hx
    · unfold locW
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have hcol : (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) =
          (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ Pi.single a 1 := by
        ext r
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      obtain ⟨s, hs, hsm⟩ := (hY (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a)).2 ⟨1, hp1, fun b => by
        rw [hcol, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]
        by_cases hb : b = a
        · subst hb
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [Pi.single_apply, hb]⟩⟩
      rw [SetLike.mem_coe, mem_clsCrd_iff, LinearEquiv.map_smul] at hsm
      have hQ : B.bc c τ ((s : D.host.E) • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) ∈
          (B.Q c τ).L := by
        rw [B.bc_L c τ]
        exact Submodule.subset_span ⟨_, hsm, rfl⟩
      rw [B.bc_smul, map_natCast] at hQ
      have hs0 : (s : D.what₂.LL) ≠ 0 := by
        intro h
        apply hs
        have h2 : s = 0 := by exact_mod_cast h
        rw [h2]
        exact dvd_zero _
      have h4 : B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) =
          (⟨_, natInv_mem_intW w s hs⟩ : intW D.what₂.places w) •
            ((s : D.what₂.LL) • B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a)) := by
        rw [Subring.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [SetLike.mem_coe]
      beta_reduce
      rw [h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hQ)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem embT_sigD (τ : D.what₂.Tau) (a : D.host.E) :
    Formalism.L2.Forms.embT D τ (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  haveI := D.host.isCMField_hostE
  show D.host.emb (D.eTau τ : D.R.GG) (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (D.host.emb (D.eTau τ : D.R.GG) a)
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ a

theorem embLL_rhoC (τ : D.what₂.Tau) (a : D.host.E) :
    D.what₂.embLL (rhoC D τ a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  rw [rhoC_conj D.what₂.embLL τ a]
  congr 1
  exact (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq D τ a).symm

theorem gramN_sig (i j : Fin (D.R.N 0)) :
    Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j = Formalism.L2.Forms.sigD D (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) j i) := by
  letI := D.host.cmStar
  simp only [Formalism.L2.Forms.gramN, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.BasicNotions.HSpace.gram]
  first
  | exact ((D.sp.X 0).herm _ _).symm
  | exact ((D.sp.X 0).herm.eq _ _).symm

def BaseBlockInverse (Y : GL (Fin (D.R.N 0)) D.host.E) : GL (Fin (D.R.N 0)) D.host.E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
      Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (by
    rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero _).2 (Matrix.isUnits_det_units Y).ne_zero) gramN_det_ne)

theorem B0inv_coe (Y : GL (Fin (D.R.N 0)) D.host.E) :
    ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) := rfl

theorem transpose_base_matrix_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).map
      D.what₂.embLL)ᵀ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  rw [B0inv_coe]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.L2.Forms.atInf, Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [embLL_rhoC, embLL_rhoC, gramN_sig j k, embT_sigD, embT_sigD, starRingEnd_self_apply, mul_comm]

variable {u : D.what₂.Word} (B : ColBase D u)

theorem h_T_mul (hB : B.rho = rhoC D) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : GL (Fin (D.R.N 0)) D.host.E) :
    (((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
        ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL)ᵀ *
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = 1 := by
  have hMb : IsUnit (Mb B c τ).det := isUnit_iff_ne_zero.mpr (Mb_det_ne B c τ)
  have hGY : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul]
    exact (map_ne_zero _).2 (mul_ne_zero gramN_det_ne (Matrix.isUnits_det_units Y).ne_zero)
  have hA : (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (rhoC D τ))⁻¹ *
      (Mb B c τ * ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (rhoC D τ))⁻¹) =
      ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
        (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ))⁻¹ := by
    rw [Matrix.map_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Mb B c τ)⁻¹, Matrix.nonsing_inv_mul _ hMb, Matrix.one_mul]
  rw [gC_coe, hB, hA, ← transpose_base_matrix_infinity Y τ, ← Matrix.transpose_mul, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGY)]
  simp

theorem isUnit_base_inverse_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  unfold Formalism.L2.Forms.atInf
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units (BaseBlockInverse Y)).map _

theorem clause_iff (T0 : Formalism.L2.Forms.Forms0 D u) (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y)
    (x : ((D.fm u).lat 0).V) :
    (∀ Bb : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) Bb →
      ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0),
        ∀ z, (D.fm u).emb 0 x c z =
          Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0))
            (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (Bb⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P (T0.val0.eY z)) ↔
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w ((D.fm u).lam 0) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  set p := co0 T0 x c with hp
  set lam := (D.fm u).lam 0 with hlam
  set Gf := Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) with hGf
  set s0 := Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0) with hs0
  set hh : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL with hhh
  set N0 : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) with hN0
  have hK : (fun τ => (hh τ)ᵀ * N0 τ) = 1 := funext fun τ => h_T_mul B hB c τ Y
  have hs : ∀ τ, s0 τ = (lam τ).detShift := fun τ => by rw [hs0, Formalism.L2.Forms.lamT_zero]; rfl
  have hemb : ∀ z, (D.fm u).emb 0 x c z =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) (T0.val0.eY z) := fun z => pol_spec T0 x c z
  have hRHS : Formalism.MainNotions.flipTwoThree.actAll lam
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔
      Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p) ∈ Formalism.L2.Forms.IntSpan D w lam := by
    rw [coT_apply, actAll_comp, mem_intSpanAt_iff_map, map_actAll]
  have hfn : Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) := by
    have h1 := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul Gf s0 (fun τ => (hh τ)ᵀ) N0 (MvPolynomial.map D.what₂.embLL p)
    rw [hK] at h1
    rw [h1, actAll_eq_subP, MvPolynomial.smul_eq_C_mul]
    congr 3
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose, hs]
  have hB0 : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) (BaseBlockInverse Y)⁻¹ :=
    isLocBasis_dual (D.what₂.places.resChar w) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg hY _
      (by rw [inv_inv]; rfl)
  have hN0' : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((((BaseBlockInverse Y)⁻¹)⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = N0 := by
    rw [inv_inv]
  rw [hRHS]
  constructor
  · intro hAll
    obtain ⟨P, hP, hPz⟩ := hAll _ hB0
    rw [hN0'] at hPz
    have hPe : Formalism.L2.Forms.fnOf Gf s0 N0 P =
        Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) := by
      funext y
      obtain ⟨z, rfl⟩ := T0.val0.eY.surjective y
      rw [hfn, ← hemb, hPz]
    have := Formalism.L2.Col.fnOf_injective Gf s0 N0 (isUnit_base_inverse_infinity Y) (Formalism.MainNotions.Ext.Lw.frOne Gf) hPe
    rw [← this]
    exact hP
  · intro hQ Bb hBb
    obtain ⟨Q₂, hQ₂, hQe⟩ := basis_change D w lam Gf s0 hB0 hBb _ hQ
    rw [hN0'] at hQe
    refine ⟨Q₂, hQ₂, fun z => ?_⟩
    rw [hemb, ← hfn, hQe]

theorem finCo_of (T : ∀ u : D.what₂.Word, Formalism.L2.Forms.Forms0 D u) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) : FinCo (T u) B := by
  intro w
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hex : ∀ c : (D.mem u).C.cls 0, ∃ Y : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y := fun c =>
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (l := D.what₂.places.resChar w) (K := D.host.E) _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).span_eq_top
  choose Y hY using hex
  refine ⟨fun c τ => Mb B c τ * (Y c : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ),
    fun c τ => locBasis_gamma B hB w c τ (Y c) (hY c), fun x => ?_⟩
  rw [Formalism.L2.G.Cmp.locWCrit_proved T u w x]
  exact forall_congr' fun c => clause_iff B (T u) hB w c (Y c) (hY c) x

theorem colValOfTiedS_holds : Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_fin fun _ F _ u B hB => finCo_of (fun u => (F.forms u).to0) u B hB

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end
