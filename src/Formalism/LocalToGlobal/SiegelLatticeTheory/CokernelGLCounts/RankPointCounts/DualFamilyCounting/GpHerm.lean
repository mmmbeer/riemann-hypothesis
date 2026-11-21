import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HTAaLbMem

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev pV (v : InfinitePlace X.B.I.F) (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem hJ_pV (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (pV X v p) (pV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  PI.SchurPlaces.hJ_psiV X v p q

theorem decompY (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ)
    (hye : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.eV X v a) y = 0)
    (hyf : ∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.fV X v a) y = 0) :
    y = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) y • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) y) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  have hy : y ∈ Submodule.span ℂ (Set.range (Formalism.L2.SG.Pf.LsNc5.fam X u v)) := by
    rw [Formalism.L2.SG.Pf.LsNc5.fam_span]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  subst hc

  have pair : ∀ t : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) t (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      (∑ a, c (Sum.inl a) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.eV X v a)) +
        ((∑ a, c (Sum.inr (Sum.inl a)) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.fV X v a)) +
        ((∑ j, c (Sum.inr (Sum.inr (Sum.inl j))) * hJ (X.B.I.ε v) t (X.wfr u v j)) +
          c (Sum.inr (Sum.inr (Sum.inr ()))) * hJ (X.B.I.ε v) t (Formalism.L2.SG.Pf.LsNc5.zV X u v))) := by
    intro t
    rw [PI.SchurPlaces.hJ_sum_r]
    simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  have hcf : ∀ a, c (Sum.inr (Sum.inl a)) = 0 := by
    intro a
    have h := hye a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_ee, Formalism.L2.SG.Pf.LsNc5.fr_ef, Formalism.L2.SG.Pf.LsNc5.fr_ew,
      Formalism.L2.SG.Pf.LsNc5.fr_ez] using h
  have hce : ∀ a, c (Sum.inl a) = 0 := by
    intro a
    have h := hyf a
    rw [pair] at h
    simpa [Formalism.L2.SG.Pf.LsNc5.fr_fe, Formalism.L2.SG.Pf.LsNc5.fr_ff, Formalism.L2.SG.Pf.LsNc5.fr_fw,
      Formalism.L2.SG.Pf.LsNc5.fr_fz, hcf] using h
  have hw : ∀ j, hJ (X.B.I.ε v) (X.wfr u v j) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inl j))) := by
    intro j
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_we, Formalism.L2.SG.Pf.LsNc5.fr_wf, Formalism.L2.SG.Pf.LsNc5.fr_ww,
      Formalism.L2.SG.Pf.LsNc5.fr_wz]
  have hz : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (∑ i, c i • Formalism.L2.SG.Pf.LsNc5.fam X u v i) =
      c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ)) := by
    rw [pair]
    simp [Formalism.L2.SG.Pf.LsNc5.fr_ze, Formalism.L2.SG.Pf.LsNc5.fr_zf, Formalism.L2.SG.Pf.LsNc5.fr_zw,
      Formalism.L2.SG.Pf.LsNc5.frame_z_z_eq_neg_t]
  simp only [hw, hz]
  have hT := Formalism.L2.SG.Pf.LsNc5.T_ne u
  have hcoef : -(c (Sum.inr (Sum.inr (Sum.inr ()))) * -((((D.mem u).A.T : ℕ) : ℂ))) /
      ((((D.mem u).A.T : ℕ) : ℝ) : ℂ) = c (Sum.inr (Sum.inr (Sum.inr ()))) := by
    push_cast; field_simp
  rw [hcoef]
  simp only [Fintype.sum_sum_type, Formalism.L2.SG.Pf.LsNc5.fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    hce, hcf, zero_smul, Finset.sum_const_zero, zero_add]

theorem decompW (v : InfinitePlace X.B.I.F) (x : (VS D).V) (hx : InW X x) :
    pV X v x = ∑ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) • X.wfr u v c +
      (-(hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x)) / ((((D.mem u).A.T : ℕ) : ℝ) : ℂ)) •
        Formalism.L2.SG.Pf.LsNc5.zV X u v := by
  refine decompY X u v _ (fun a => ?_) (fun a => ?_)
  · show hJ (X.B.I.ε v) (pV X v (X.eX a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).1, map_zero]
  · show hJ (X.B.I.ε v) (pV X v (X.fY a)) (pV X v x) = 0
    rw [hJ_pV, (hx a).2, map_zero]

theorem rowV_w (x : (VS D).V) (v : InfinitePlace X.B.I.F) (j : Fin D.R.k) :
    rowV X u x v (Fin.castSucc j) = hJ (X.B.I.ε v) (pV X v x) (X.wfr u v j) := by
  simp [rowV]

theorem rowV_last_eq_hJ (x : (VS D).V) (v : InfinitePlace X.B.I.F) :
    rowV X u x v (Fin.last D.R.k) = hJ (X.B.I.ε v) (pV X v x) (Formalism.L2.SG.Pf.LsNc5.zV X u v) := by
  simp [rowV]
  rfl

theorem rowV_gram (v : InfinitePlace X.B.I.F) (x y : (VS D).V) (hy : InW X y) :
    embS D (X.pl v) ((VS D).hT x y) =
      (∑ j : Fin D.R.k, rowV X u x v (Fin.castSucc j) * star (rowV X u y v (Fin.castSucc j))) -
        rowV X u x v (Fin.last D.R.k) * star (rowV X u y v (Fin.last D.R.k)) / (((D.mem u).A.T : ℕ) : ℂ) := by
  rw [← hJ_pV, decompW X u v y hy, PI.SchurPlaces.hJ_add_r, PI.SchurPlaces.hJ_sum_r, PI.SchurPlaces.hJ_smul_r]
  simp only [rowV_w, rowV_last_eq_hJ]
  have e1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v y) = star (hJ (X.B.I.ε v) (pV X v y) (X.wfr u v c)) :=
    fun c => hJ_conj' _ _ _
  have e2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v y) =
      star (hJ (X.B.I.ε v) (pV X v y) (Formalism.L2.SG.Pf.LsNc5.zV X u v)) := hJ_conj' _ _ _
  simp only [e1, e2]
  push_cast
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun c _ => by ring
  · ring

theorem rowV_inj (x : (VS D).V) (hx : InW X x) (h : rowV X u x = 0) : x = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hp : pV X v x = 0 := by
    rw [decompW X u v x hx]
    have h1 : ∀ c, hJ (X.B.I.ε v) (X.wfr u v c) (pV X v x) = 0 := by
      intro c
      rw [hJ_conj', ← rowV_w, h]; simp
    have h2 : hJ (X.B.I.ε v) (Formalism.L2.SG.Pf.LsNc5.zV X u v) (pV X v x) = 0 := by
      rw [hJ_conj', ← rowV_last_eq_hJ, h]; simp
    simp [h1, h2]
  refine (VS D).nondeg.1 x fun y => ?_
  apply (embS D (X.pl v)).injective
  rw [← hJ_pV, hp, map_zero]
  unfold hJ; simp

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local notation "FIE" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem ddS_ne' : ddS D ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_ne

theorem star_mem_zpow (m : ℤ) {x : D.host.E} (hx : x ∈ ddS D ^ m) : star x ∈ ddS D ^ m := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    obtain ⟨y', hy', e⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_pow n y hy
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y', hy', e⟩
  · rw [_root_.zpow_neg, zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_inv n hx



theorem iQ_eq (b a : Fin D.R.rS) : iQ D b a = ((ddS D ^ ((b : ℤ) - a) : FIE) : Set D.host.E) := by
  unfold iQ aaD
  congr 1
  rw [← _root_.zpow_neg, ← zpow_add₀ ddS_ne']
  congr 1
  push_cast; ring

theorem iP_eq (b a : Fin D.R.rS) :
    iP D b a = ((ddS D ^ (-((D.R.rS : ℤ) - b) - ((D.R.rS : ℤ) - a)) : FIE) : Set D.host.E) := by
  unfold iP aaD
  congr 1
  rw [← zpow_add₀ ddS_ne']
  congr 1

theorem star_mem_iQ {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iQ D b a) : star x ∈ iQ D b a := by
  rw [iQ_eq] at hx ⊢; exact star_mem_zpow _ hx

theorem star_mem_iP {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iP D b a) : star x ∈ iP D b a := by
  rw [iP_eq] at hx ⊢; exact star_mem_zpow _ hx

theorem iP_comm (b a : Fin D.R.rS) : iP D b a = iP D a b := by
  rw [iP_eq, iP_eq]; congr 2; ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

section Inv

variable (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0)
  (hd : ∀ a, X0 a a = 1)

include hup hd

theorem det_one : X0.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
  simp [hd]

theorem inv_mul : X0⁻¹ * X0 = 1 := Matrix.nonsing_inv_mul _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem mul_inv : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem inv_up : ∀ b a : Fin D.R.rS, a < b → X0⁻¹ b a = 0 := by
  have hU : IsUnit X0.det := by rw [det_one X0 hup hd]; exact isUnit_one
  have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
  haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
  exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h

theorem inv_diag : ∀ a, X0⁻¹ a a = 1 := by
  intro a
  have h := congrFun (congrFun (mul_inv X0 hup hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
  have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
    · rw [hup a e h1, zero_mul]
    · rw [inv_up X0 hup hd e a h1, mul_zero]
  rw [hz, add_zero] at h
  exact h

theorem map_inv' {K : Type*} [Field K] (f : D.host.E →+* K) : (X0.map f)⁻¹ = X0⁻¹.map f := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, inv_mul X0 hup hd, Matrix.map_one _ f.map_zero f.map_one]

end Inv

theorem gram_mem (xs : Fin D.R.rS → (VS D).V) (hxs : ∀ b, xs b ∈ aaLb X b) (b c : Fin D.R.rS) :
    Gq D xs b c ∈ aaD D b * aaD D c := by
  show (VS D).hT (xs b) (xs c) ∈ aaD D b * aaD D c
  suffices H : ∀ y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ d ∈ (aaD D c : Set D.host.E), ∃ l ∈ X.Lb, y = d • l},
      (VS D).hT (xs b) y ∈ aaD D b * aaD D c from H _ (hxs c)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, hdm, l, hl, rfl⟩ := hz
    rw [map_smul, smul_eq_mul, mul_comm d]
    exact FractionalIdeal.mul_mem_mul (LatA.hT_aaLb_mem X (hxs b) hl) hdm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [← algebraMap_smul D.host.E o x, map_smul, smul_eq_mul]
    exact LatA.fi_smul_mem hx o

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem Gp_mem (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1)
    (hs : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹) (hxs : ∀ b, xs b ∈ aaLb X b) :
    ∀ b a, Gp D X0 xs b a ∈ aaD D b * aaD D a := by
  have hY := LatA.shape_mul X0⁻¹ (Gq D xs) (inv_up X0 hup hd) (inv_diag X0 hup hd) (LatA.shape_inv X0 hup hd hs)
    (gram_mem X xs hxs)
  intro b a
  unfold Gp
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Matrix.conjTranspose_apply]
  rcases lt_trichotomy e a with h | h | h
  · rw [inv_up X0 hup hd a e h, star_zero, mul_zero]; exact Submodule.zero_mem _
  · subst h; rw [inv_diag X0 hup hd, star_one, mul_one]; exact hY b e
  · have hz : star (X0⁻¹ a e) ∈ aaD D a * (aaD D e)⁻¹ :=
      star_mem_iQ (show X0⁻¹ a e ∈ iQ D a e from LatA.shape_inv X0 hup hd hs a e h)
    have hYe : (X0⁻¹ * Gq D xs) b e ∈ aaD D e * aaD D b := by rw [mul_comm]; exact hY b e
    have key : star (X0⁻¹ a e) * (X0⁻¹ * Gq D xs) b e ∈ aaD D a * aaD D b := by
      rw [← LatA.aa_cancel2 e a b]; exact FractionalIdeal.mul_mem_mul hz hYe
    rw [mul_comm (aaD D b) (aaD D a), mul_comm ((X0⁻¹ * Gq D xs) b e)]
    exact key

theorem Gp_herm (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    (Gp D X0 xs)ᴴ = Gp D X0 xs := by
  have hG : (Gq D xs)ᴴ = Gq D xs := by
    refine Matrix.ext fun b c => ?_
    rw [Matrix.conjTranspose_apply]
    show star ((VS D).hT (xs c) (xs b)) = (VS D).hT (xs b) (xs c)
    rw [Alg.hsw, star_star]
  unfold Gp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

theorem Xc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1) (v : InfinitePlace X.B.I.F) :
    Xc X (blkQ X u X0 xs M) v = X0.map (embS D (X.pl v)) := by
  ext b a
  simp only [Xc, Matrix.map_apply]
  split_ifs with h1 h2
  · rfl
  · subst h2; rw [hd, map_one]
  · have : a < b := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    rw [hup b a this, map_zero]

theorem Gc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hW : ∀ b, InW X (xs b)) (v : InfinitePlace X.B.I.F) :
    Gc X u (blkQ X u X0 xs M) v = (Gq D xs).map (embS D (X.pl v)) := by
  ext b c
  simp only [Gc, Matrix.map_apply]
  rw [show Gq D xs b c = (VS D).hT (xs b) (xs c) from rfl, rowV_gram X u v (xs b) (xs c) (hW c)]
  rfl

theorem Hc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1) (hW : ∀ b, InW X (xs b))
    (v : InfinitePlace X.B.I.F) :
    Hc X u (blkQ X u X0 xs M) v = (Gp D X0 xs).map (embS D (X.pl v)) := by
  unfold Hc
  rw [Xc_blkQ X u X0 xs M hup hd v, Gc_blkQ X u X0 xs M hW v, map_inv' X0 hup hd]
  have hc : ((X0⁻¹).map (embS D (X.pl v)))ᴴ = ((X0⁻¹)ᴴ).map (embS D (X.pl v)) :=
    (Matrix.conjTranspose_map _ fun t => emb_star X v t).symm
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
