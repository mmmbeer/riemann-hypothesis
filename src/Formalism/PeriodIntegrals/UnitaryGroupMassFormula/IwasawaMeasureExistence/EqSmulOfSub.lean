import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq
import Mathlib

section
noncomputable section

namespace PI.IwaMeasEx.LP

open Matrix Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.PD

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  (Fm Fi : Matrix (Fin n) (Fin n) R)

def wc (X : Matrix (Fin n) (Fin n) R) : Matrix ι ι R := (Fi * X * Fm).submatrix e e

def uw (A : Matrix ι ι R) : Matrix (Fin n) (Fin n) R := Fm * A.submatrix e.symm e.symm * Fi

variable {Fm Fi}

theorem wc_mul (hFm : Fm * Fi = 1) (X Y : Matrix (Fin n) (Fin n) R) :
    wc e Fm Fi (X * Y) = wc e Fm Fi X * wc e Fm Fi Y := by
  unfold wc
  rw [submatrix_mul_equiv, show Fi * X * Fm * (Fi * Y * Fm) = Fi * X * (Fm * Fi) * Y * Fm by
    simp only [Matrix.mul_assoc], hFm, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem uw_mul (hFi : Fi * Fm = 1) (A B : Matrix ι ι R) :
    uw e Fm Fi (A * B) = uw e Fm Fi A * uw e Fm Fi B := by
  unfold uw
  rw [(submatrix_mul_equiv A B e.symm e.symm e.symm).symm,
    show Fm * A.submatrix e.symm e.symm * Fi * (Fm * B.submatrix e.symm e.symm * Fi) =
      Fm * A.submatrix e.symm e.symm * (Fi * Fm) * B.submatrix e.symm e.symm * Fi by simp only [Matrix.mul_assoc],
    hFi, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem wc_one (hFi : Fi * Fm = 1) : wc e Fm Fi (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold wc
  rw [Matrix.mul_one, hFi, submatrix_one_equiv]

theorem uw_one (hFm : Fm * Fi = 1) : uw e Fm Fi (1 : Matrix ι ι R) = 1 := by
  unfold uw
  rw [submatrix_one_equiv, Matrix.mul_one, hFm]

theorem blo_of_par (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev) :
    BLo lev (wc e Fm Fi (g : Matrix (Fin n) (Fin n) R)) := by
  intro s r hl
  have h1 : g ∈ Formalism.UG.stabGL (stepLo (cols e Fm) lev (lev r + 1)) := Subgroup.mem_iInf.1 hg (lev r + 1)
  exact entry_zero hFi {t | lev t < lev r + 1} h1 s r (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega)

end Gen

section Form

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  {Fm Fi : Matrix (Fin n) (Fin n) R}

def ALev (a : ℕ) (W : Matrix ι ι R) : Prop := ∀ q r, W q r ≠ 0 → lev q + lev r = 2 * a

theorem cT_apply (σ : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    Formalism.UG.cT σ M i j = σ (M j i) := rfl

theorem cT_submatrix (σ : R →+* R) {m p m' p' : Type} (M : Matrix m p R) (f : m' → m) (g : p' → p) :
    Formalism.UG.cT σ (M.submatrix f g) = (Formalism.UG.cT σ M).submatrix g f := by
  ext i j; rfl

theorem tripleS (σ : R →+* R) (A W : Matrix ι ι R) (p q : ι) :
    (Formalism.UG.cT σ A * W * A) p q = ∑ t, ∑ r, σ (A r p) * W r t * A t q := by
  simp only [Matrix.mul_apply, cT_apply, Finset.sum_mul]

theorem bd_unitaryS (σ : R →+* R) {a : ℕ} {W T : Matrix ι ι R} (hA : ALev lev a W) (hT : BLo lev T)
    (hU : Formalism.UG.cT σ T * W * T = W) : Formalism.UG.cT σ (bd lev T) * W * bd lev T = W := by
  ext p q
  rw [tripleS]
  by_cases hpq : lev p + lev q = 2 * a
  · conv_rhs => rw [← hU, tripleS]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
    by_cases hW : W r t = 0
    · rw [hW, mul_zero, zero_mul, mul_zero, zero_mul]
    have hl := hA r t hW
    simp only [bd]
    by_cases h1 : lev r = lev p
    · rw [if_pos h1, if_pos (show lev t = lev q by omega)]
    · rw [if_neg h1, map_zero, zero_mul, zero_mul]
      rcases Nat.lt_or_ge (lev p) (lev r) with h2 | h2
      · rw [hT r p h2, map_zero, zero_mul, zero_mul]
      · rw [hT t q (by omega), mul_zero]
  · have hW : W p q = 0 := by
      by_contra h; exact hpq (hA p q h)
    rw [hW]
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun r _ => ?_
    simp only [bd]
    by_cases h1 : lev r = lev p
    · by_cases h2 : lev t = lev q
      · have hW' : W r t = 0 := by
          by_contra h; have := hA r t h; omega
        rw [hW', mul_zero, zero_mul]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, map_zero, zero_mul, zero_mul]

theorem wc_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) (hFm : Fm * Fi = 1) {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (X : Matrix (Fin n) (Fin n) R)
    (hX : Formalism.UG.cT σ X * Jx * X = Jx) : Formalism.UG.cT σ (wc e Fm Fi X) * W * wc e Fm Fi X = W := by
  subst hW
  unfold wc
  rw [cT_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  congr 1
  have e1 : Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm = 1 := by rw [← Formalism.UG.cT_mul, hFm, Formalism.UG.cT_one]
  calc Formalism.UG.cT σ (Fi * X * Fm) * (Formalism.UG.cT σ Fm * Jx * Fm) * (Fi * X * Fm)
      = Formalism.UG.cT σ Fm * Formalism.UG.cT σ X * (Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm) * Jx * (Fm * Fi) * X * Fm := by
        simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Fm * (Formalism.UG.cT σ X * Jx * X) * Fm := by
        rw [e1, hFm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hX]

theorem uw_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) (hFm : Fm * Fi = 1) {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (A : Matrix ι ι R) (hA : Formalism.UG.cT σ A * W * A = W) :
    Formalism.UG.cT σ (uw e Fm Fi A) * Jx * uw e Fm Fi A = Jx := by
  have e1 : Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm = 1 := by rw [← Formalism.UG.cT_mul, hFm, Formalism.UG.cT_one]
  have hG : Formalism.UG.cT σ Fm * Jx * Fm = W.submatrix e.symm e.symm := by
    rw [← hW, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  have hA' : Formalism.UG.cT σ (A.submatrix e.symm e.symm) * W.submatrix e.symm e.symm * A.submatrix e.symm e.symm =
      W.submatrix e.symm e.symm := by
    rw [cT_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA]
  unfold uw
  calc Formalism.UG.cT σ (Fm * A.submatrix e.symm e.symm * Fi) * Jx * (Fm * A.submatrix e.symm e.symm * Fi)
      = Formalism.UG.cT σ Fi * (Formalism.UG.cT σ (A.submatrix e.symm e.symm) * (Formalism.UG.cT σ Fm * Jx * Fm) *
          A.submatrix e.symm e.symm) * Fi := by simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm * Jx * (Fm * Fi) := by
        rw [hG, hA', ← hG]; simp only [Matrix.mul_assoc]
    _ = Jx := by rw [e1, hFm, Matrix.one_mul, Matrix.mul_one]

theorem wc_mul_inv (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) :
    wc e Fm Fi (g : Matrix (Fin n) (Fin n) R) * wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← wc_mul e hFm, ← Units.val_mul, mul_inv_cancel, Units.val_one, wc_one e hFi]

theorem wc_inv_mul (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) :
    wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * wc e Fm Fi (g : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← wc_mul e hFm, ← Units.val_mul, inv_mul_cancel, Units.val_one, wc_one e hFi]

def levGL (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) (hg : g ∈ parGL (cols e Fm) lev) :
    GL (Fin n) R :=
  ⟨uw e Fm Fi (bd lev (wc e Fm Fi (g : Matrix (Fin n) (Fin n) R))),
    uw e Fm Fi (bd lev (wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))),
    by rw [← uw_mul e hFi, bd_mul lev (blo_of_par e lev hFi hg) (blo_of_par e lev hFi ((parGL _ lev).inv_mem hg))
      (wc_mul_inv e hFm hFi g), uw_one e hFm],
    by rw [← uw_mul e hFi, bd_mul lev (blo_of_par e lev hFi ((parGL _ lev).inv_mem hg)) (blo_of_par e lev hFi hg)
      (wc_inv_mul e hFm hFi g), uw_one e hFm]⟩

variable (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev)

theorem levGL_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) {a : ℕ} {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (hA : ALev lev a W) (hgU : g ∈ Formalism.UG.UJ σ Jx) :
    levGL e lev hFm hFi g hg ∈ Formalism.UG.UJ σ Jx :=
  uw_unitary e σ Jx hFm hW _ (bd_unitaryS lev σ hA (blo_of_par e lev hFi hg) (wc_unitary e σ Jx hFm hW _ hgU))

end Form

end PI.IwaMeasEx.LP

end
end

section
noncomputable section

namespace PI.IwaMeasEx.AfT

open NumberField Matrix Topology Filter
open scoped TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.WittLeviSubgroups

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

end Alg

section Top

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R] {n : ℕ}

variable {X : Type} [TopologicalSpace X] (m : X → GL (Fin n) R)
  (hm : Continuous fun x => (m x : Matrix (Fin n) (Fin n) R))
  (hmi : Continuous fun x => (((m x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
include hm hmi

variable {ι : Type} [Fintype ι] (b : ι → (Fin n → R)) (lev : ι → ℕ) (e : ι ≃ Fin n)
  (P Q : Matrix (Fin n) (Fin n) R) (hQP : Q * P = 1) (hPQ : P * Q = 1) (hb : ∀ r i, b r i = P i (e r))
include hQP hPQ hb

end Top

variable (I : AutInst)

variable {I} {J : ℕ} (Fr : WittFrame I J)

def frF : Matrix (Fin I.n) (Fin I.n) (AEf I) :=
  (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))

def frFi : Matrix (Fin I.n) (Fin I.n) (AEf I) :=
  ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem frFi_mul : frFi Fr * frF Fr = 1 := by
  rw [frFi, frF, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem frF_mul : frF Fr * frFi Fr = 1 := by
  rw [frFi, frF, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

def frVi (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v

theorem frVi_mul (v : InfinitePlace I.F) : frVi Fr v * Fr.frV v = 1 := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [frVi, WittFrame.frV, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem frV_mul (v : InfinitePlace I.F) : Fr.frV v * frVi Fr v = 1 := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [frVi, WittFrame.frV, Matrix.mul_assoc, ← Matrix.mul_assoc ((Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)),
    ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ hP]

variable (c : Composition J)

def parA : Subgroup I.GA :=
  (parGL Fr.colF (levW c)).comap (projF I) ⊓ ⨅ v, (parGL (Fr.colV v) (levW c)).comap (projV I v)

end PI.IwaMeasEx.AfT
end
end

section
noncomputable section

namespace PI.IwaMeasEx.LP

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.PD PI.IwaMeasEx.AfT
open scoped TensorProduct

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

theorem colF_cols : Fr.colF = cols (eW Fr) (frF Fr) := by
  funext r i; rfl

theorem colV_cols (v : InfinitePlace I.F) : Fr.colV v = cols (eW Fr) (Fr.frV v) := by
  funext r i; rfl

theorem cT_star {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem gramF : (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (frF Fr) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
    frF Fr).submatrix (eW Fr) (eW Fr) = (wittJ (J := J) Fr.J0).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  rw [frF, cT_map, ← Matrix.map_mul, ← Matrix.map_mul, submatrix_map]
  congr 1
  exact Gm_sub Fr

theorem gramV (v : InfinitePlace I.F) : (Formalism.UG.cT (starRingEnd ℂ) (Fr.frV v) * Formalism.REAL.Jm (I.ε v) *
    Fr.frV v).submatrix (eW Fr) (eW Fr) = (wittJ (J := J) Fr.J0).map (I.φ v) := by
  have hc : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, (M.map (I.φ v))ᴴ = Mᴴ.map (I.φ v) := fun M =>
    (conjTranspose_map _ (semiconj_phi v)).symm
  have e1 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← conjTranspose_mul, rrg_P_mul_inv, conjTranspose_one]
  have hJm : Formalism.REAL.Jm (I.ε v) = (I.P v)ᴴ * I.J.map (I.φ v) * I.P v := (I.P_spec v).symm
  have key : (Fr.frV v)ᴴ * Formalism.REAL.Jm (I.ε v) * Fr.frV v = (Gm Fr).map (I.φ v) := by
    calc (Fr.frV v)ᴴ * Formalism.REAL.Jm (I.ε v) * Fr.frV v
        = ((Bm Fr).map (I.φ v))ᴴ * (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            (Bm Fr).map (I.φ v) := by
          rw [hJm]; simp only [WittFrame.frV, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Gm Fr).map (I.φ v) := by
          rw [e1, rrg_P_mul_inv, hc]; simp only [Gm, Matrix.map_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  rw [cT_star, key, submatrix_map]
  congr 1
  exact Gm_sub Fr

theorem alevF : ALev (levW (n₀ := nz I J) c) c.length ((wittJ (J := J) Fr.J0).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :=
  fun q r h => antiLev_wittJ c Fr.J0 q r (fun h' => h (by rw [Matrix.map_apply, h', map_zero]))

theorem alevV (v : InfinitePlace I.F) : ALev (levW (n₀ := nz I J) c) c.length ((wittJ (J := J) Fr.J0).map (I.φ v)) :=
  fun q r h => antiLev_wittJ c Fr.J0 q r (fun h' => h (by rw [Matrix.map_apply, h', map_zero]))

variable {Fr c}

theorem parF {x : I.GA} (hx : x ∈ parA Fr c) : projF I x ∈ parGL (cols (eW Fr) (frF Fr)) (levW c) := by
  rw [← colF_cols]; exact (Subgroup.mem_inf.1 hx).1

theorem parV {x : I.GA} (hx : x ∈ parA Fr c) (v : InfinitePlace I.F) :
    projV I v x ∈ parGL (cols (eW Fr) (Fr.frV v)) (levW c) := by
  rw [← colV_cols]; exact Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 v

def levF {x : I.GA} (hx : x ∈ parA Fr c) : I.Gf :=
  ⟨levGL (eW Fr) (levW c) (frF_mul Fr) (frFi_mul Fr) (projF I x) (parF hx),
    levGL_unitary (eW Fr) (levW c) (frF_mul Fr) (frFi_mul Fr) (parF hx) _ _ (gramF Fr) (alevF Fr c) x.2.2⟩

def levV {x : I.GA} (hx : x ∈ parA Fr c) (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨levGL (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (projV I v x) (parV hx v), by
    have hU : projV I v x ∈ Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm (I.ε v)) := by
      show Formalism.UG.cT (starRingEnd ℂ) (uMat (x.1 v)) * Formalism.REAL.Jm (I.ε v) * uMat (x.1 v) = Formalism.REAL.Jm (I.ε v)
      rw [cT_star]; exact (x.1 v).2
    have h := levGL_unitary (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (parV hx v) _ _ (gramV Fr v)
      (alevV Fr c v) hU
    have h' : Formalism.UG.cT (starRingEnd ℂ) ((levGL (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (projV I v x)
        (parV hx v) : GL (Fin I.n) ℂ) : Matrix (Fin I.n) (Fin I.n) ℂ) * Formalism.REAL.Jm (I.ε v) *
        ((levGL (eW Fr) (levW c) (frV_mul Fr v) (frVi_mul Fr v) (projV I v x) (parV hx v) : GL (Fin I.n) ℂ) :
          Matrix (Fin I.n) (Fin I.n) ℂ) = Formalism.REAL.Jm (I.ε v) := h
    rw [cT_star] at h'
    exact h'⟩

def levA {x : I.GA} (hx : x ∈ parA Fr c) : I.GA := (fun v => levV hx v, levF hx)

variable (Fr c)

variable {Fr c}

end PI.IwaMeasEx.LP

end
end

section
noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory Topology Set
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.AfT

variable {X : CData} {n₀ : ℕ} {A : ℝ} {J : ℕ}

theorem map_val_mul' {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (K : Subgroup G) (g : K) (α : Measure K) :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by
  rw [Measure.map_map measurable_subtype_coe (measurable_const_mul g),
    Measure.map_map (measurable_const_mul _) measurable_subtype_coe]
  rfl

structure UnipotentMeasureProperties {J : ℕ} (D : BaseDatum X.I J) (c : Composition J) (μN : Measure X.I.GA) : Prop where
  sfin : SigmaFinite μN
  ne : μN ≠ 0
  supp : μN (D.toWittFrame.uniA c : Set X.I.GA)ᶜ = 0
  cpt : ∀ s : Set X.I.GA, IsCompact s → μN s ≠ ⊤
  inv : ∀ n ∈ D.toWittFrame.uniA c, μN.map (fun x => n * x) = μN

end PI.IwaMeasEx.LP

end
end

section
noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory Topology Set NumberField
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.WittLeviSubgroups Formalism.L2.S.S7.PositiveOrthantChangeOfVariables PI.IwaMeasEx.AfT

section Factors

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

open Classical in

def tF (m : I.GA) (i : Fin c.length) : ℝ :=
  if h : IsUnit (Fr.blkF c m i).det then Formalism.L2.S.S7.GLOne.nrmF I h.unit else 0

end Factors

section Local

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

def uniF : Subgroup I.Gf := (uniGL Fr.colF (levW c)).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def uniV (v : InfinitePlace I.F) : Subgroup (Formalism.REAL.UJ (I.ε v)) :=
  (uniGL (Fr.colV v) (levW c)).comap (Formalism.REAL.UJ (I.ε v)).subtype

structure PNF (μ : Measure I.Gf) : Prop where
  sfin : SigmaFinite μ
  ne : μ ≠ 0
  supp : μ (uniF Fr c : Set I.Gf)ᶜ = 0
  cpt : ∀ s : Set I.Gf, IsCompact s → μ s ≠ ⊤
  inv : ∀ n ∈ uniF Fr c, μ.map (fun x => n * x) = μ

structure PNV (v : InfinitePlace I.F) (μ : Measure (Formalism.REAL.UJ (I.ε v))) : Prop where
  sfin : SigmaFinite μ
  ne : μ ≠ 0
  supp : μ (uniV Fr c v : Set (Formalism.REAL.UJ (I.ε v)))ᶜ = 0
  cpt : ∀ s : Set (Formalism.REAL.UJ (I.ε v)), IsCompact s → μ s ≠ ⊤
  inv : ∀ n ∈ uniV Fr c v, μ.map (fun x => n * x) = μ

end Local

end PI.IwaMeasEx.LP

end
end

section
noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory MeasureTheory.Measure Topology Set NumberField
open scoped ENNReal NNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.AfT

section Uniq

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem exists_coef (H : Subgroup G) (hc : IsClosed (H : Set G)) {μ : Measure G} (hs : μ (H : Set G)ᶜ = 0)
    (hcpt : ∀ s : Set G, IsCompact s → μ s ≠ ⊤) (hi : ∀ h ∈ H, μ.map (fun x => h * x) = μ) :
    haveI : LocallyCompactSpace H := hc.locallyCompactSpace
    ∃ a : ℝ≥0, μ = a • (Measure.haar : Measure H).map Subtype.val := by
  haveI : LocallyCompactSpace H := hc.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) := hc.isClosedEmbedding_subtypeVal.measurableEmbedding
  have hmap : (μ.comap (Subtype.val : H → G)).map Subtype.val = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact restrict_eq_self_of_ae_mem ((ae_iff).2 hs)
  haveI : IsMulLeftInvariant (μ.comap (Subtype.val : H → G)) := ⟨fun h => by
    have e1 := map_val_mul' H h (μ.comap (Subtype.val : H → G))
    rw [hmap, hi (h : G) h.2] at e1
    calc (μ.comap (Subtype.val : H → G)).map (fun x => h * x)
        = (((μ.comap (Subtype.val : H → G)).map (fun x => h * x)).map Subtype.val).comap Subtype.val :=
          (hme.comap_map _).symm
      _ = μ.comap Subtype.val := by rw [e1]⟩
  haveI : IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : H → G)) := ⟨fun K hK => by
    rw [hme.comap_apply]
    exact (hcpt _ (hK.image continuous_subtype_val)).lt_top⟩
  refine ⟨haarScalarFactor (μ.comap (Subtype.val : H → G)) Measure.haar, ?_⟩
  conv_lhs => rw [← hmap, isMulLeftInvariant_eq_smul (μ.comap (Subtype.val : H → G)) Measure.haar]
  rw [Measure.map_smul]


end Uniq



section Prod

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)


end Prod

end PI.IwaMeasEx.LP

end
end
