import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.NormDetInf
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.DegreeFormula.Statement

section
noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder

namespace GlobalTheory.HodgeDomain

variable {p q : ℕ}

def jW (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ -
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁

theorem upq_iff {g : GL (Fin p ⊕ Fin q) ℂ} : g ∈ Upq p q ↔
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Jpq p q * g = Jpq p q := by
  unfold Upq UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  have hc : cT (starRingEnd ℂ) (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by
    ext i j
    simp [cT, conjTranspose_apply]
  rw [hc]

theorem Jpq_sq : Jpq p q * Jpq p q = 1 := by
  unfold Jpq
  rw [fromBlocks_multiply]
  simp

theorem upq_right {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ =
      Jpq p q := by
  have h := upq_iff.mp hg
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have h1 : (Jpq p q * Gᴴ * Jpq p q) * G = 1 := by
    rw [show Jpq p q * Gᴴ * Jpq p q * G = Jpq p q * (Gᴴ * Jpq p q * G) by simp only [Matrix.mul_assoc], h, Jpq_sq]
  have h2 : G * (Jpq p q * Gᴴ * Jpq p q) = 1 := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)
  calc G * Jpq p q * Gᴴ = G * (Jpq p q * Gᴴ * Jpq p q) * Jpq p q := by
        simp only [Matrix.mul_assoc, Jpq_sq, Matrix.mul_one]
    _ = Jpq p q := by rw [h2, Matrix.one_mul]

private lemma Jpq_mul_fromRows {n : Type*} (C : Matrix (Fin p) n ℂ) (D : Matrix (Fin q) n ℂ) :
    Jpq p q * fromRows C D = fromRows C (-D) := by
  ext (i | i) j <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private lemma conjTranspose_fromRows_mul_Jpq_mul_fromRows {n m : Type*} (A : Matrix (Fin p) n ℂ) (B : Matrix (Fin q) n ℂ)
    (C : Matrix (Fin p) m ℂ) (D : Matrix (Fin q) m ℂ) :
    (fromRows A B)ᴴ * Jpq p q * fromRows C D = Aᴴ * C - Bᴴ * D := by
  rw [Matrix.mul_assoc, Jpq_mul_fromRows]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]

private lemma fromCols_mul_Jpq {m : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ) :
    fromCols A B * Jpq p q = fromCols A (-B) := by
  ext i (j | j) <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private lemma fromCols_mul_Jpq_mul_conjTranspose_fromCols {m n : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ)
    (C : Matrix n (Fin p) ℂ) (D : Matrix n (Fin q) ℂ) :
    fromCols A B * Jpq p q * (fromCols C D)ᴴ = A * Cᴴ - B * Dᴴ := by
  rw [fromCols_mul_Jpq]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]

private lemma blocks_mul_fromRows {n : Type*} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (X : Matrix (Fin p) n ℂ) (Y : Matrix (Fin q) n ℂ) :
    M * fromRows X Y = fromRows (M.toBlocks₁₁ * X + M.toBlocks₁₂ * Y) (M.toBlocks₂₁ * X + M.toBlocks₂₂ * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem kapQ_gram {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) (z : Matrix (Fin p) (Fin q) ℂ) :
    (kapQ g z)ᴴ * kapQ g z -
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂)ᴴ *
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) = hQ z := by
  have h := upq_iff.mp hg
  unfold kapQ hQ
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have e1 : (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ)) =
      (fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ) := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc]
  rw [blocks_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows] at e1
  simp only [Matrix.mul_one, conjTranspose_one] at e1
  simpa only [neg_sub] using congrArg Neg.neg e1

theorem kapQ_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (kapQ g z).det := by
  have h1 := kapQ_gram hg z
  have hpd : ((kapQ g z)ᴴ * kapQ g z).PosDef := by
    rw [eq_add_of_sub_eq h1]
    exact Matrix.PosDef.add_posSemidef (by exact hz) (posSemidef_conjTranspose_mul_self _)
  rw [isUnit_iff_ne_zero]
  intro h0
  have := hpd.det_pos
  rw [det_mul, det_conjTranspose, h0, mul_zero] at this
  exact lt_irrefl _ this

theorem moeb_mul_kapQ {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z =
      (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ := by
  have hu := kapQ_isUnit hg hz
  calc moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z =
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z + (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) *
        ((kapQ g z)⁻¹ * kapQ g z) := by
        rw [moeb, Matrix.mul_assoc]; rfl
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem hQ_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z = hQ z := by
  have e := moeb_mul_kapQ hg hz
  have h1 := kapQ_gram hg z
  calc (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z =
      (kapQ g z)ᴴ * kapQ g z - (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z)ᴴ * (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z) := by
        unfold hQ
        rw [conjTranspose_mul]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = hQ z := by rw [e]; exact h1

theorem moeb_mem {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q := by
  have hu : IsUnit (kapQ g z) := (Matrix.isUnit_iff_isUnit_det _).mpr (kapQ_isUnit hg hz)
  have h2 : ((kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z).PosDef := by
    rw [hQ_moeb hg hz]; exact hz
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mp h2

private lemma fromCols_mul_eq_blocks {m : Type*} (X : Matrix m (Fin p) ℂ) (Y : Matrix m (Fin q) ℂ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    fromCols X Y * M = fromCols (X * M.toBlocks₁₁ + Y * M.toBlocks₂₁) (X * M.toBlocks₁₂ + Y * M.toBlocks₂₂) := by
  ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

private lemma mul_fromCols' {m k : Type*} [Fintype m] (N : Matrix k m ℂ) (X : Matrix m (Fin p) ℂ)
    (Y : Matrix m (Fin q) ℂ) : N * fromCols X Y = fromCols (N * X) (N * Y) := by
  ext i (j | j) <;> simp [Matrix.mul_apply]

theorem hP_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    jW g z * hP z * (jW g z)ᴴ = hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) := by
  have h := upq_right hg
  have e := moeb_mul_kapQ hg hz
  unfold jW hP
  unfold kapQ at e
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h e ⊢
  generalize moeb G z = w at e ⊢
  rw [Matrix.mul_add, ← Matrix.mul_assoc] at e
  have k1 : fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G =
      (G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) := by
    rw [fromCols_mul_eq_blocks, mul_fromCols']
    have b1 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₁ + -w * G.toBlocks₂₁ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * 1 := by
      rw [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, sub_eq_add_neg]
    have b2 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₂ + -w * G.toBlocks₂₂ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * -z := by
      rw [Matrix.one_mul, Matrix.neg_mul, eq_sub_of_add_eq' e, Matrix.mul_neg, Matrix.sub_mul]
      abel
    rw [b1, b2]
  have k2 : (G.toBlocks₁₁ - w * G.toBlocks₂₁) *
        (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ) *
        (G.toBlocks₁₁ - w * G.toBlocks₂₁)ᴴ =
      fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w))ᴴ := by
    calc _ = ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z)) * Jpq p q *
          ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G)ᴴ := by
            rw [k1]
      _ = _ := by
            rw [conjTranspose_mul]
            conv_rhs => rw [← h]
            simp only [Matrix.mul_assoc]
  rw [fromCols_mul_Jpq_mul_conjTranspose_fromCols, fromCols_mul_Jpq_mul_conjTranspose_fromCols] at k2
  simpa only [conjTranspose_one, Matrix.mul_one, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using k2

theorem hP_mul_eq_one {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    hP z * (1 + z * (hQ z)⁻¹ * zᴴ) = 1 := by
  have hpd : (hQ z).PosDef := hz
  have hu : IsUnit (hQ z).det := isUnit_iff_ne_zero.mpr hpd.det_pos.ne'
  have key : z * (hQ z * (hQ z)⁻¹) * zᴴ = z * zᴴ := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  generalize (hQ z)⁻¹ = R at key ⊢
  unfold hQ at key
  unfold hP
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc] at key ⊢
  rw [← key]
  abel

theorem hP_inv_posDef {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z)⁻¹.PosDef := by
  have e : (hP z)⁻¹ = 1 + z * (hQ z)⁻¹ * zᴴ := Matrix.inv_eq_right_inv (hP_mul_eq_one hz)
  rw [e]
  have hq : (hQ z).PosDef := hz
  exact Matrix.PosDef.one.add_posSemidef (hq.inv.posSemidef.mul_mul_conjTranspose_same z)

theorem hP_posDef {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z).PosDef := by
  have hu : IsUnit (hP z).det := Matrix.isUnit_det_of_right_inverse (hP_mul_eq_one hz)
  have h := (hP_inv_posDef hz).inv
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at h

theorem jW_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (jW g z).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := (hP_posDef (moeb_mem hg hz)).det_pos
  rw [← hP_moeb hg hz, det_mul, det_mul, det_conjTranspose, h0] at h
  simp at h

theorem hP_inv_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (jW g z)ᴴ * (hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z))⁻¹ * jW g z = (hP z)⁻¹ := by
  have hu := jW_isUnit hg hz
  have hu' : IsUnit (jW g z)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
  rw [← hP_moeb hg hz, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hu',
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

def autE (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks (jW g z) 0 0 (kapQ g z)


theorem mul_frame {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * fromBlocks 1 z 0 1 =
      fromBlocks 1 (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) 0 1 *
        fromBlocks (jW g z) 0 (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ (kapQ g z) := by
  have e := moeb_mul_kapQ hg hz
  unfold jW
  conv_lhs => rw [← fromBlocks_toBlocks (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, sub_add_cancel]
  rfl

def tanAct (g : GL (Fin p ⊕ Fin q) ℂ) (z ξ : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  jW g z * ξ * (kapQ g z)⁻¹

def blkMet (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks A 0 0 B

theorem blkMet_posDef {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef)
    (hB : B.PosDef) : (blkMet A B).PosDef := by
  unfold blkMet
  have hpsd : (fromBlocks A 0 0 B).PosSemidef := by
    let _ := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
    have h0 : (0 : Matrix (Fin q) (Fin p) ℂ) = (0 : Matrix (Fin p) (Fin q) ℂ)ᴴ := by simp
    rw [h0]
    exact (Matrix.PosDef.fromBlocks₁₁ _ _ hA).2 (by simpa using hB.posSemidef)
  refine hpsd.posDef_iff_isUnit.2 ?_
  rw [Matrix.isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
  exact (isUnit_iff_ne_zero.mpr hA.det_pos.ne').mul (isUnit_iff_ne_zero.mpr hB.det_pos.ne')


def hodge (c : ℝ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  blkMet ((c : ℂ) • (hP z)⁻¹) ((c : ℂ) • hQ z)

theorem hodge_posDef {c : ℝ} (hc : 0 < c) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).PosDef := by
  unfold hodge
  have hc' : (0 : ℂ) < (c : ℂ) := Complex.zero_lt_real.mpr hc
  exact blkMet_posDef ((hP_inv_posDef hz).smul hc') ((show (hQ z).PosDef from hz).smul hc')



example (c : ℝ) : hodge c (0 : Matrix (Fin p) (Fin q) ℂ) = (c : ℂ) • 1 := by
  simp [hodge, blkMet, hP, hQ, ← fromBlocks_one, fromBlocks_smul]

end GlobalTheory.HodgeDomain
end
end

section
noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

section Norms

variable {ι n : Type} [Fintype ι] [Fintype n]

def nsq (M : ι → Matrix n n ℂ) (v : ι → n → ℂ) : ℝ := ∑ τ, (star (v τ) ⬝ᵥ M τ *ᵥ v τ).re

theorem nsq_pos {M : ι → Matrix n n ℂ} (hM : ∀ τ, (M τ).PosDef) {v : ι → n → ℂ} (hv : v ≠ 0) : 0 < nsq M v := by
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hv
  have hnn : ∀ σ, 0 ≤ (star (v σ) ⬝ᵥ M σ *ᵥ v σ).re := fun σ =>
    (Complex.nonneg_iff.mp ((hM σ).posSemidef.dotProduct_mulVec_nonneg (v σ))).1
  have hp : 0 < (star (v τ) ⬝ᵥ M τ *ᵥ v τ).re :=
    (Complex.pos_iff.mp ((hM τ).dotProduct_mulVec_pos hτ)).1
  unfold nsq
  exact Finset.sum_pos' (fun σ _ => hnn σ) ⟨τ, Finset.mem_univ _, hp⟩

theorem nsq_smul (M : ι → Matrix n n ℂ) (t : ℝ) (v : ι → n → ℂ) : nsq M (t • v) = t ^ 2 * nsq M v := by
  simp only [nsq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Pi.smul_apply, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  ring

theorem nsq_zero (M : ι → Matrix n n ℂ) : nsq M 0 = 0 := by simp [nsq]

theorem continuous_nsq (M : ι → Matrix n n ℂ) : Continuous (nsq M) := by
  unfold nsq
  refine continuous_finset_sum _ fun τ _ => Complex.continuous_re.comp ?_
  exact ((continuous_apply τ).star).dotProduct (continuous_const.matrix_mulVec (continuous_apply τ))


theorem exists_bounds {M : ι → Matrix n n ℂ} (hM : ∀ τ, (M τ).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ v, a * ‖v‖ ^ 2 ≤ nsq M v ∧ nsq M v ≤ b * ‖v‖ ^ 2 := by
  have hc := continuous_nsq M
  have hpos : ∀ v ∈ Metric.sphere (0 : ι → n → ℂ) 1, 0 < nsq M v := by
    intro v hv
    refine nsq_pos hM ?_
    rintro rfl
    simp at hv
  have hom : ∀ v : ι → n → ℂ, v ≠ 0 → nsq M v = ‖v‖ ^ 2 * nsq M (‖v‖⁻¹ • v) := by
    intro v hv
    rw [nsq_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_pow, one_mul]
  have mem : ∀ v : ι → n → ℂ, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → n → ℂ) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  rcases (Metric.sphere (0 : ι → n → ℂ) 1).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, 1, one_pos, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have h1 := mem v hv
      rw [hE] at h1
      exact h1
    subst hv
    simp [nsq_zero]
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → n → ℂ) 1).exists_isMinOn hne hc.continuousOn
    obtain ⟨w, -, hmax⟩ := (isCompact_sphere (0 : ι → n → ℂ) 1).exists_isMaxOn hne hc.continuousOn
    refine ⟨nsq M u, max (nsq M w) 1, hpos u hu, lt_of_lt_of_le one_pos (le_max_right _ _), fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [nsq_zero]
    · rw [hom v hv]
      have h1 := isMinOn_iff.mp hmin _ (mem v hv)
      have h2 := isMaxOn_iff.mp hmax _ (mem v hv)
      have hn : 0 ≤ ‖v‖ ^ 2 := by positivity
      constructor
      · rw [mul_comm (nsq M u)]
        exact mul_le_mul_of_nonneg_left h1 hn
      · rw [mul_comm (max _ _)]
        exact mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) hn

def ratios (h h0 : ι → Matrix n n ℂ) : Set ℝ := {t | ∃ v, v ≠ 0 ∧ t = nsq h v / nsq h0 v}

def eigLo (h h0 : ι → Matrix n n ℂ) : ℝ := sInf (ratios h h0)

def eigUp (h h0 : ι → Matrix n n ℂ) : ℝ := sSup (ratios h h0)

variable {h h0 : ι → Matrix n n ℂ}

theorem ratios_nonempty [Nonempty ι] [Nonempty n] : (ratios h h0).Nonempty := by
  refine ⟨_, fun _ _ => 1, ?_, rfl⟩
  intro hv0
  have h1 := congrFun (congrFun hv0 (Classical.arbitrary ι)) (Classical.arbitrary n)
  simp at h1

theorem ratios_bounds (hh : ∀ τ, (h τ).PosDef) (hh0 : ∀ τ, (h0 τ).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ ∀ t ∈ ratios h h0, a ≤ t ∧ t ≤ b := by
  obtain ⟨a1, b1, ha1, hb1, H1⟩ := exists_bounds hh
  obtain ⟨a0, b0, ha0, hb0, H0⟩ := exists_bounds hh0
  refine ⟨a1 / b0, b1 / a0, div_pos ha1 hb0, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  have hp0 : 0 < nsq h0 v := nsq_pos hh0 hv
  obtain ⟨l1, u1⟩ := H1 v
  obtain ⟨l0, u0⟩ := H0 v
  constructor
  · rw [div_le_div_iff₀ hb0 hp0]
    nlinarith [mul_le_mul_of_nonneg_left u0 ha1.le, mul_le_mul_of_nonneg_left l1 hb0.le]
  · rw [div_le_div_iff₀ hp0 ha0]
    nlinarith [mul_le_mul_of_nonneg_left u1 ha0.le, mul_le_mul_of_nonneg_left l0 hb1.le]

theorem eigLo_pos [Nonempty ι] [Nonempty n] (hh : ∀ τ, (h τ).PosDef) (hh0 : ∀ τ, (h0 τ).PosDef) :
    0 < eigLo h h0 ∧ eigLo h h0 ≤ eigUp h h0 := by
  obtain ⟨a, b, ha, hab⟩ := ratios_bounds hh hh0
  have hne : (ratios h h0).Nonempty := ratios_nonempty
  have hbb : BddBelow (ratios h h0) := ⟨a, fun t ht => (hab t ht).1⟩
  have hba : BddAbove (ratios h h0) := ⟨b, fun t ht => (hab t ht).2⟩
  unfold eigLo eigUp
  exact ⟨lt_of_lt_of_le ha (le_csInf hne fun t ht => (hab t ht).1), csInf_le_csSup hne hbb hba⟩




end Norms

section Calculus

variable {ι : Type} [Fintype ι] {p q : ℕ}

abbrev Pt (ι : Type) (p q : ℕ) : Type := ι → Matrix (Fin p) (Fin q) ℂ

def dR (f : Pt ι p q → ℂ) (z ξ : Pt ι p q) : ℂ := fderiv ℝ (fun v => f (unflat v)) (flat z) (flat ξ)

def dHol (f : Pt ι p q → ℂ) (z ξ : Pt ι p q) : ℂ := (dR f z ξ - Complex.I * dR f z (Complex.I • ξ)) / 2

def dAnti (f : Pt ι p q → ℂ) (z η : Pt ι p q) : ℂ := (dR f z η + Complex.I * dR f z (Complex.I • η)) / 2

def ddc (f : Pt ι p q → ℝ) (z ξ : Pt ι p q) : ℝ :=
  (dHol (fun w => dAnti (fun u => (f u : ℂ)) w ξ) z ξ).re / Real.pi

def SmoothOn (f : Pt ι p q → ℂ) : Prop := ContDiffOn ℝ ∞ (fun v => f (unflat v)) (DomFlat ι p q)

variable {n : Type} [Fintype n] [DecidableEq n]

def connMat (M : Pt ι p q → ι → Matrix n n ℂ) (z ξ : Pt ι p q) (τ : ι) : Matrix n n ℂ :=
  (M z τ)⁻¹ * Matrix.of fun a b => dHol (fun w => M w τ a b) z ξ

def curvMat (M : Pt ι p q → ι → Matrix n n ℂ) (z ξ η : Pt ι p q) (τ : ι) : Matrix n n ℂ :=
  Matrix.of fun a b => -dAnti (fun w => connMat M w ξ τ a b) z η

def connNorm (h h0 : Pt ι p q → ι → Matrix n n ℂ) (β : Pt ι p q → Pt ι p q → ℝ) (z : Pt ι p q) : ℝ :=
  sSup {t | ∃ ξ v, β z ξ ≤ 1 ∧ nsq (h0 z) v ≤ 1 ∧
    t = Real.sqrt (nsq (h0 z) fun τ => (connMat h z ξ τ - connMat h0 z ξ τ) *ᵥ v τ)}

def curvNorm (h : Pt ι p q → ι → Matrix n n ℂ) (β : Pt ι p q → Pt ι p q → ℝ) (z : Pt ι p q) : ℝ :=
  sSup {t | ∃ ξ η v, β z ξ ≤ 1 ∧ β z η ≤ 1 ∧ nsq (h z) v ≤ 1 ∧
    t = Real.sqrt (nsq (h z) fun τ => curvMat h z ξ η τ *ᵥ v τ)}






end Calculus

section Boundary

variable {ι : Type} [Fintype ι] {p q : ℕ}

structure BdData (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) where

  m : ℕ

  nrm : Fin m → Pt ι p q → ℝ
  nrm_pos : ∀ i, ∀ z ∈ DomI ι p q, 0 < nrm i z
  nrm_le : ∀ i, ∀ z ∈ DomI ι p q, nrm i z ≤ 1
  nrm_smooth : ∀ i, SmoothOn fun z => (nrm i z : ℂ)
  nrm_inv : ∀ i, ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, nrm i (moebI γ z) = nrm i z

  kae : Pt ι p q → Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ
  kae_herm : ∀ z ∈ DomI ι p q, ∀ ξ η, kae z η ξ = starRingEnd ℂ (kae z ξ η)
  kae_pos : ∀ z ∈ DomI ι p q, ∀ ξ, ξ ≠ 0 → 0 < (kae z ξ ξ).re
  kae_smooth : ∀ ξ η, SmoothOn fun z => kae z ξ η
  kae_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ ξ η,
    kae (moebI γ z) (fun τ => tanAct (γ τ) (z τ) (ξ τ)) (fun τ => tanAct (γ τ) (z τ) (η τ)) = kae z ξ η

  cst : ℝ
  cst_pos : 0 < cst
  cst_small : ∀ i, ∀ z ∈ DomI ι p q, ∀ ξ,
    2 * m * cst * |ddc (fun w => Real.exp 1 - Real.log (nrm i w ^ 2)) z ξ| ≤ Real.exp 1 * (kae z ξ ξ).re

  metW : Pt ι p q → ι → Matrix (Fin p) (Fin p) ℂ

  metOm : Pt ι p q → ι → Matrix (Fin q) (Fin q) ℂ
  metW_pos : ∀ z ∈ DomI ι p q, ∀ τ, (metW z τ).PosDef
  metOm_pos : ∀ z ∈ DomI ι p q, ∀ τ, (metOm z τ).PosDef
  metW_smooth : ∀ τ a b, SmoothOn fun z => metW z τ a b
  metOm_smooth : ∀ τ a b, SmoothOn fun z => metOm z τ a b
  metW_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ τ,
    (jW (γ τ) (z τ))ᴴ * metW (moebI γ z) τ * jW (γ τ) (z τ) = metW z τ
  metOm_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ τ,
    (kapQ (γ τ) (z τ))ᴴ * metOm (moebI γ z) τ * kapQ (γ τ) (z τ) = metOm z τ

def hodgeI (c : ι → ℝ) (z : Pt ι p q) (τ : ι) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := hodge (c τ) (z τ)

namespace BdData

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

def ri (i : Fin B.m) (z : Pt ι p q) : ℝ := Real.exp 1 - Real.log (B.nrm i z ^ 2)

def r (z : Pt ι p q) : ℝ := Real.exp 1 - Real.log ((∏ i, B.nrm i z) ^ 2)

def beta (z ξ : Pt ι p q) : ℝ := (B.kae z ξ ξ).re - B.cst * ∑ i, ddc (fun w => Real.log (B.ri i w)) z ξ

def met (z : Pt ι p q) (τ : ι) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := blkMet (B.metW z τ) (B.metOm z τ)

theorem exp_le_ri (i : Fin B.m) {z : Pt ι p q} (hz : z ∈ DomI ι p q) : Real.exp 1 ≤ B.ri i z := by
  unfold ri
  have h1 := B.nrm_pos i z hz
  have h2 := B.nrm_le i z hz
  have h3 : Real.log (B.nrm i z ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (pow_le_one₀ h1.le h2)
  linarith

theorem exp_le_r {z : Pt ι p q} (hz : z ∈ DomI ι p q) : Real.exp 1 ≤ B.r z := by
  unfold r
  have h0 : 0 ≤ ∏ i, B.nrm i z := Finset.prod_nonneg fun i _ => (B.nrm_pos i z hz).le
  have h1 : ∏ i, B.nrm i z ≤ 1 :=
    Finset.prod_le_one (fun i _ => (B.nrm_pos i z hz).le) fun i _ => B.nrm_le i z hz
  have h3 : Real.log ((∏ i, B.nrm i z) ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (pow_le_one₀ h0 h1)
  linarith

theorem r_eq {z : Pt ι p q} (hz : z ∈ DomI ι p q) : B.r z = ∑ i, B.ri i z - (B.m - 1) * Real.exp 1 := by
  unfold r ri
  rw [← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero 2 (B.nrm_pos i z hz).ne',
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


theorem met_posDef {z : Pt ι p q} (hz : z ∈ DomI ι p q) (τ : ι) : (B.met z τ).PosDef := by
  unfold met
  exact blkMet_posDef (B.metW_pos z hz τ) (B.metOm_pos z hz τ)



end BdData

def detNorm (c : ι → ℝ) (s : ℂ) (z : Pt ι p q) (τ : ι) : ℝ := ‖s‖ * Real.sqrt (hodgeI c z τ).det.re


def onQuot {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (f : Pt ι p q → ℝ) (x : XCc ι p q Γ) : ℝ :=
  f (Quot.out x : DomI ι p q)


end Boundary

end GlobalTheory.HodgeDomain
end
end

section
noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem smoothOn_det {n : ℕ} {M : Pt ι p q → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, SmoothOn fun z => M z a b) :
    SmoothOn fun z => (M z).det := by
  unfold SmoothOn at *
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem smoothOn_inv {n : ℕ} {M : Pt ι p q → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, SmoothOn fun z => M z a b)
    (hd : ∀ z ∈ DomI ι p q, (M z).det ≠ 0) (a b : Fin n) : SmoothOn fun z => (M z)⁻¹ a b := by
  have hadj : SmoothOn fun z => (M z).adjugate a b := by
    simp only [adjugate_apply]
    refine smoothOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (smoothOn_det h) fun v hv => hd _ hv) hadj

theorem smoothOn_coord (τ : ι) (a : Fin p) (b : Fin q) : SmoothOn fun z : Pt ι p q => z τ a b :=
  (contDiff_apply ℝ ℂ (τ, a, b)).contDiffOn

theorem smoothOn_star {f : Pt ι p q → ℂ} (h : SmoothOn f) : SmoothOn fun z => star (f z) :=
  Complex.conjCLE.contDiff.comp_contDiffOn h

theorem smoothOn_hP (τ : ι) (a b : Fin p) : SmoothOn fun z : Pt ι p q => hP (z τ) a b := by
  simp only [hP, Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
  exact contDiffOn_const.sub (ContDiffOn.sum fun k _ =>
    ContDiffOn.mul (smoothOn_coord τ a k) (smoothOn_star (smoothOn_coord τ b k)))

theorem smoothOn_hQ (τ : ι) (a b : Fin q) : SmoothOn fun z : Pt ι p q => hQ (z τ) a b := by
  simp only [hQ, Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
  exact contDiffOn_const.sub (ContDiffOn.sum fun k _ =>
    ContDiffOn.mul (smoothOn_star (smoothOn_coord τ k a)) (smoothOn_coord τ k b))

theorem smoothOn_hP_inv (τ : ι) (a b : Fin p) : SmoothOn fun z : Pt ι p q => (hP (z τ))⁻¹ a b :=
  smoothOn_inv (smoothOn_hP τ) (fun _ hz => (hP_posDef (hz τ)).det_pos.ne') a b

theorem smoothOn_hQ_inv (τ : ι) (a b : Fin q) : SmoothOn fun z : Pt ι p q => (hQ (z τ))⁻¹ a b :=
  smoothOn_inv (smoothOn_hQ τ) (fun z hz => (show (hQ (z τ)).PosDef from hz τ).det_pos.ne') a b

def bergman (z : Pt ι p q) : Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun ξ η => ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace)
    (fun _ _ _ => by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [Matrix.mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

theorem bergman_apply (z ξ η : Pt ι p q) :
    bergman z ξ η = ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace := rfl

theorem trace_pos {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (ξ : Matrix (Fin p) (Fin q) ℂ) : 0 ≤ (A * ξ * B * ξᴴ).trace ∧ (ξ ≠ 0 → 0 < (A * ξ * B * ξᴴ).trace) := by
  open MatrixOrder in
  obtain ⟨R, hR, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  open MatrixOrder in
  obtain ⟨S, hS, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self.1 hB.isStrictlyPositive
  have e : (star R * R * ξ * (S * star S) * ξᴴ).trace = ((R * ξ * S) * (R * ξ * S)ᴴ).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  have h0 := (posSemidef_self_mul_conjTranspose (R * ξ * S)).trace_nonneg
  refine ⟨h0, fun hξ => lt_of_le_of_ne h0 fun h => hξ ?_⟩
  have h1 := trace_mul_conjTranspose_self_eq_zero_iff.1 h.symm
  have hR' := (isUnit_iff_isUnit_det _).1 hR
  have hS' := (isUnit_iff_isUnit_det _).1 hS
  have : R⁻¹ * (R * ξ * S) * S⁻¹ = ξ := by
    rw [Matrix.mul_assoc R, nonsing_inv_mul_cancel_left _ _ hR', mul_nonsing_inv_cancel_right _ _ hS']
  rw [← this, h1]; simp

theorem bergman_moeb {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ η : Pt ι p q) :
    bergman (moebI g z) (fun τ => tanAct (g τ) (z τ) (ξ τ)) (fun τ => tanAct (g τ) (z τ) (η τ)) =
      bergman z ξ η := by
  rw [bergman_apply, bergman_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hu : g τ ∈ Upq p q := hg τ (Set.mem_univ _)
  rw [← hP_inv_moeb hu (hz τ), ← hQ_moeb hu (hz τ), Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [tanAct, conjTranspose_mul, Matrix.mul_assoc, conjTranspose_nonsing_inv, moebI]
  rw [trace_mul_comm (jW (g τ) (z τ))ᴴ]
  simp only [Matrix.mul_assoc]

def invariantData {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (hΓ : Γ ≤ UpqI ι p q) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ) :
    BdData ι p q Γ where
  m := 0
  nrm := fun i => i.elim0
  nrm_pos := fun i => i.elim0
  nrm_le := fun i => i.elim0
  nrm_smooth := fun i => i.elim0
  nrm_inv := fun i => i.elim0
  kae := bergman
  kae_herm := fun z hz ξ η => by
    rw [bergman_apply, bergman_apply, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [starRingEnd_apply, ← trace_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, (hP_inv_posDef (hz τ)).isHermitian.eq,
      (show (hQ (z τ)).PosDef from hz τ).inv.isHermitian.eq, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  kae_pos := fun z hz ξ hξ => by
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hξ
    have H := fun σ => trace_pos (hP_inv_posDef (hz σ)) (show (hQ (z σ)).PosDef from hz σ).inv (ξ σ)
    rw [bergman_apply, Complex.re_sum]
    exact Finset.sum_pos' (fun σ _ => (Complex.nonneg_iff.1 (H σ).1).1)
      ⟨τ, Finset.mem_univ _, (Complex.pos_iff.1 ((H τ).2 hτ)).1⟩
  kae_smooth := fun ξ η => by
    simp only [bergman_apply, trace, diag_apply, Matrix.mul_apply]
    exact ContDiffOn.sum fun τ _ => ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => ContDiffOn.mul
      (ContDiffOn.sum fun k _ => ContDiffOn.mul (ContDiffOn.sum fun l _ =>
        ContDiffOn.mul (smoothOn_hP_inv τ a l) contDiffOn_const) (smoothOn_hQ_inv τ k b)) contDiffOn_const
  kae_inv := fun γ hγ z hz ξ η => bergman_moeb (hΓ hγ) hz ξ η
  cst := 1
  cst_pos := one_pos
  cst_small := fun i => i.elim0
  metW := fun z τ => (c τ : ℂ) • (hP (z τ))⁻¹
  metOm := fun z τ => (c τ : ℂ) • hQ (z τ)
  metW_pos := fun z hz τ => (hP_inv_posDef (hz τ)).smul (by exact_mod_cast hc τ)
  metOm_pos := fun z hz τ => PosDef.smul (hz τ) (by exact_mod_cast hc τ)
  metW_smooth := fun τ a b => ContDiffOn.mul contDiffOn_const (smoothOn_hP_inv τ a b)
  metOm_smooth := fun τ a b => ContDiffOn.mul contDiffOn_const (smoothOn_hQ τ a b)
  metW_inv := fun γ hγ z hz τ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, moebI, hP_inv_moeb (hΓ hγ τ (Set.mem_univ _)) (hz τ)]
  metOm_inv := fun γ hγ z hz τ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, moebI, hQ_moeb (hΓ hγ τ (Set.mem_univ _)) (hz τ)]

example (ξ η : Pt ι p q) : bergman 0 ξ η = ∑ τ, (ξ τ * (η τ)ᴴ).trace := by
  simp [bergman_apply, hP, hQ]

end GlobalTheory.HodgeDomain
end
end

section
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def flagConst (r : ℕ) : ℝ := ∏ i ∈ Finset.range r, (i.factorial : ℝ) / Real.pi ^ i

theorem flagConst_pos (r : ℕ) : 0 < flagConst r :=
  Finset.prod_pos fun i _ => div_pos (by exact_mod_cast i.factorial_pos) (pow_pos Real.pi_pos _)

def grassConst (p q : ℕ) : ℝ := (∏ i ∈ Finset.range p, ((q + i).factorial : ℝ) / i.factorial) / Real.pi ^ (p * q)

theorem flagConst_add (p q : ℕ) : flagConst (p + q) = grassConst p q * flagConst p * flagConst q := by
  have hπ := Real.pi_pos.ne'
  induction p with
  | zero => simp [flagConst, grassConst]
  | succ p ih =>
    have h1 : ((p.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    have e1 : flagConst (p + 1 + q) = flagConst (p + q) * (((q + p).factorial : ℝ) / Real.pi ^ (q + p)) := by
      rw [show p + 1 + q = (p + q) + 1 by ring, flagConst, Finset.prod_range_succ, add_comm q p]; rfl
    have e2 : flagConst (p + 1) = flagConst p * ((p.factorial : ℝ) / Real.pi ^ p) := Finset.prod_range_succ _ _
    have e3 : grassConst (p + 1) q = grassConst p q * (((q + p).factorial : ℝ) / p.factorial) / Real.pi ^ q := by
      rw [grassConst, Finset.prod_range_succ, grassConst, add_mul, one_mul, pow_add]
      field_simp
    rw [e1, e2, e3, ih, pow_add]
    field_simp

example : flagConst 2 = 1 / Real.pi := by simp [flagConst, Finset.prod_range_succ]

example : grassConst 1 1 = 1 / Real.pi := by simp [grassConst]

theorem isOrth_x0F (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

theorem muF_fundSet_le (X : Data E r) {x0 x1 : Frame X.Ψ r} (ho : IsOrth X x0) (ho1 : IsOrth X x1)
    {FF CechHodgeFiltration : Set (V (nd X))} (hF : IsFundSet X x0 FF) (hF1 : IsFundSet X x1 CechHodgeFiltration) :
    muF X x0 FF ≤ muF X x1 CechHodgeFiltration := by
  classical
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  have hS1 : MeasurableSet (KU.Sset X x1 CechHodgeFiltration) := KU.meas_S X ho1 hF1.1
  set Bad : Set (Frame X.Ψ r) := ⋂ γ : X.Γ, (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration)ᶜ with hBaddef
  have hBad : MeasurableSet Bad :=
    MeasurableSet.iInter fun γ => ((KU.cont_lact X γ.1⁻¹).measurable hS1).compl
  have hBadB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Bad.indicator 1 x := by
    intro x _ b hb
    have e : rmul x b ∈ Bad ↔ x ∈ Bad := by
      simp only [hBaddef, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage, KU.lact_rmul', KU.rmul_mem_S X hb]
    simp only [Set.indicator_apply, e, Pi.one_apply]
  have hm : ∀ x : Frame X.Ψ r, Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x z) :=
    fun x => (measurable_one.indicator hBad).comp (KU.cont_cpt X x).measurable
  have h1 : ∫⁻ z, Bad.indicator 1 (cpt X x1 z) ∂muF X x1 = 0 := by
    rw [lintegral_eq_zero_iff (hm x1)]
    filter_upwards [KU.cover X hF1] with z ⟨γ, hγ, hSz⟩
    have : cpt X x1 z ∉ Bad := fun h => (Set.mem_iInter.mp h ⟨γ, hγ⟩) hSz
    simp [Set.indicator_of_notMem this]
  rw [← hM r X x0 x1 ho ho1 _ (measurable_one.indicator hBad) hBadB, lintegral_eq_zero_iff (hm x0)] at h1
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1) measurable_const
    (fun _ _ _ _ _ _ => rfl) CechHodgeFiltration hF1.1 hF1.2.1
  have hset : (FF ∩ {z | ∃ y ∈ CechHodgeFiltration, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      cpt X x0 z = lact γ (rmul (cpt X x1 y) b)} : Set (V (nd X))) =ᵐ[muF X x0] FF := by
    filter_upwards [h1] with z hz
    refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have hb : cpt X x0 z ∉ Bad := fun hb => by simp [Set.indicator_of_mem hb] at hz
    simp only [hBaddef, Set.mem_iInter, not_forall, Set.mem_compl_iff, not_not, Set.mem_preimage] at hb
    obtain ⟨γ, ⟨y, b⟩, ⟨hy, hb⟩, e⟩ := hb
    refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
    have e' : rmul (cpt X x1 y) b = lact γ.1⁻¹ (cpt X x0 z) := e
    rw [e', KU.lact_lact, mul_inv_cancel, KU.lact_one]
  rw [setLIntegral_congr hset] at hle
  simpa using hle

def covol (X : Data E r) : ℝ :=
  flagConst r ^ X.Ψ.card * (muF X (x0F X) (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose).toReal

theorem covol_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) :
    muF X x0 FF < ⊤ ∧ covol X = flagConst r ^ X.Ψ.card * (muF X x0 FF).toReal := by
  have h0 := (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
  refine ⟨FundSetMeasStatement_holds r X x0 FF ho hF (GlobalTheory.finMu_all_data E r X), ?_⟩
  rw [covol, le_antisymm (muF_fundSet_le X (isOrth_x0F X) ho h0 hF) (muF_fundSet_le X ho (isOrth_x0F X) hF h0)]

theorem covol_pos (X : Data E r) : 0 < covol X := by
  have h0 := (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
  exact mul_pos (pow_pos (flagConst_pos r) _) (ENNReal.toReal_pos
    (GlobalTheory.MetricWeightTest.fundSet_pos X (isOrth_x0F X) h0) (covol_eq X (isOrth_x0F X) h0).1.ne)

def idx {r j : ℕ} (h : j ≤ r) : Fin r ≃ Fin j ⊕ Fin (r - j) :=
  ((finCongr (Nat.sub_add_cancel h).symm).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _)

theorem idx_symm_inl {r j : ℕ} (h : j ≤ r) (a : Fin j) : ((idx h).symm (Sum.inl a) : ℕ) = r - j + a := by
  simp [idx]

theorem idx_symm_inr {r j : ℕ} (h : j ≤ r) (a : Fin (r - j)) : ((idx h).symm (Sum.inr a) : ℕ) = a := by
  simp [idx]

theorem reindex_sgn {r j : ℕ} (h : j ≤ r) :
    reindex (idx h) (idx h) (diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ)) = -Jpq j (r - j) := by
  have e : Jpq j (r - j) = diagonal (Sum.elim (fun _ => 1) fun _ => -1) := by
    rw [Jpq, ← fromBlocks_diagonal]; simp [← diagonal_neg]
  rw [reindex_apply, submatrix_diagonal_equiv, e, diagonal_neg]
  congr 1
  funext a
  rcases a with a | a
  · simp [sgn, idx_symm_inl]
  · simp [sgn, idx_symm_inr]

omit [NumberField E] [IsCMField E] in
theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x)ᵀ = xᴴ * (G.map τ)ᵀ * x := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, transpose_apply, of_apply, mul_apply, conjTranspose_apply, map_apply,
    Finset.sum_mul, RCLike.star_def]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type} (ι : Tau → X.Ψ)

theorem det_x0F (τ : X.Ψ) : (mat (x0F X) τ).det ≠ 0 := (X.signature τ).choose_spec.1

def frameCo (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ :=
  reindex (idx hj) (idx hj) ((mat (x0F X) τ)⁻¹ * mat x τ)

def baseGL (τ : X.Ψ) : GL (Fin j ⊕ Fin (r - j)) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero (reindex (idx hj) (idx hj) (mat (x0F X) τ))
    (by rw [det_reindex_self]; exact det_x0F X τ)

def toUpq : GL (Fin r) E →* (Tau → GL (Fin j ⊕ Fin (r - j)) ℂ) :=
  embI (fun t => (ι t).1) (fun _ => idx hj) fun t => baseGL X hj (ι t)

theorem toUpq_val (γ : GL (Fin r) E) (t : Tau) :
    (toUpq X hj ι γ t).1 = frameCo X hj (lact γ (x0F X)) (ι t) := by
  show ((baseGL X hj (ι t))⁻¹).1 * reindex (idx hj) (idx hj) (γ.1.map (ι t).1) * ((baseGL X hj (ι t))⁻¹⁻¹).1 = _
  rw [inv_inv, coe_units_inv]
  show (reindex (idx hj) (idx hj) (mat (x0F X) (ι t)))⁻¹ * _ * reindex (idx hj) (idx hj) (mat (x0F X) (ι t)) = _
  rw [inv_reindex]
  simp only [frameCo, reindex_apply, submatrix_mul_equiv, Matrix.mul_assoc]
  rfl

def gammaU : Subgroup (Tau → GL (Fin j ⊕ Fin (r - j)) ℂ) := X.Γ.map (toUpq X hj ι)

theorem frameCo_orth (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (frameCo X hj x τ)ᴴ * Jpq j (r - j) * frameCo X hj x τ = Jpq j (r - j) := by
  have h0 := congrArg transpose (isOrth_x0F X τ)
  have h1 := congrArg transpose (hx τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0 h1
  set M := (mat (x0F X) τ)⁻¹ * mat x τ with hM
  have e : mat x τ = mat (x0F X) τ * M := by
    rw [hM, mul_nonsing_inv_cancel_left _ _ (det_x0F X τ).isUnit]
  have h2 : Mᴴ * (diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ)) * M =
      diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ) := by
    conv_rhs => rw [← h1, e]
    rw [← h0]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have h3 := congrArg (reindex (idx hj) (idx hj)) h2
  have h4 := reindex_sgn hj
  rw [h4] at h3
  rw [← neg_inj, ← h3, ← Matrix.neg_mul, ← Matrix.mul_neg, ← h4]
  simp only [frameCo, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv, ← hM]

theorem gammaU_le [Fintype Tau] (hp : X.p0 = r - j) : gammaU X hj ι ≤ UpqI Tau j (r - j) := by
  rintro _ ⟨γ, hγ, rfl⟩ t -
  refine upq_iff.2 ?_
  rw [toUpq_val]
  exact frameCo_orth X hj hp (KU.isOrth_lact X hγ (isOrth_x0F X)) _

def domPt (x : Frame X.Ψ r) : Pt Tau j (r - j) := fun t => moeb (frameCo X hj x (ι t)) 0

theorem moeb_zero {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    moeb g 0 = g.toBlocks₁₂ * g.toBlocks₂₂⁻¹ := by simp [moeb]

theorem frameCo_rmul_blocks {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (x : Frame X.Ψ r) (τ : X.Ψ) :
    ∃ B : Matrix (Fin (r - j)) (Fin (r - j)) ℂ, IsUnit B.det ∧
      (frameCo X hj (rmul x b) τ).toBlocks₁₂ = (frameCo X hj x τ).toBlocks₁₂ * B ∧
      (frameCo X hj (rmul x b) τ).toBlocks₂₂ = (frameCo X hj x τ).toBlocks₂₂ * B := by
  set B := reindex (idx hj) (idx hj) (mat b τ) with hB
  have h12 : B.toBlocks₁₂ = 0 := by
    ext a c
    refine (hb τ).2 _ _ ?_
    rw [Fin.lt_def, idx_symm_inl, idx_symm_inr]
    have := c.2; omega
  have hd : B.det ≠ 0 := by rw [hB, det_reindex_self]; exact (hb τ).1
  rw [← fromBlocks_toBlocks B, h12, det_fromBlocks_zero₁₂] at hd
  have e : frameCo X hj (rmul x b) τ = frameCo X hj x τ * B := by
    simp only [frameCo, hB, reindex_apply, submatrix_mul_equiv, Matrix.mul_assoc]
    rfl
  refine ⟨B.toBlocks₂₂, (right_ne_zero_of_mul hd).isUnit, ?_, ?_⟩ <;>
  · rw [e]
    conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x τ), ← fromBlocks_toBlocks B, h12, fromBlocks_multiply]
    simp

theorem domPt_rmul {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    domPt X hj ι (rmul x b) = domPt X hj ι x := by
  funext t
  obtain ⟨B, hB, h1, h2⟩ := frameCo_rmul_blocks X hj hb x (ι t)
  simp only [domPt, moeb_zero]
  rw [h1, h2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB]

theorem zero_mem_hcDom (p q : ℕ) : (0 : Matrix (Fin p) (Fin q) ℂ) ∈ hcDom p q := by
  simpa [hcDom] using PosDef.one

theorem exists_upq_of_orth (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    ∃ g ∈ Upq j (r - j), g.1 = frameCo X hj x τ := by
  have h := frameCo_orth X hj hp hx τ
  have hd : (frameCo X hj x τ).det ≠ 0 := by
    intro h0
    have h1 := congrArg det h
    have h2 := congrArg det (Jpq_sq (p := j) (q := r - j))
    rw [det_mul, h0, mul_zero] at h1
    rw [det_mul, ← h1] at h2
    simp at h2
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, upq_iff.2 h, rfl⟩

theorem domPt_mem (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : domPt X hj ι x ∈ DomI Tau j (r - j) := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  rw [domPt_rmul X hj ι hb]
  intro t
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp h1 (ι t)
  have := moeb_mem hg (zero_mem_hcDom _ _)
  rwa [e] at this

theorem frameCo_isUnit₂₂ (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    IsUnit (frameCo X hj x τ).toBlocks₂₂.det := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  obtain ⟨B, hB, -, h2⟩ := frameCo_rmul_blocks X hj hb x1 τ
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp h1 τ
  have := kapQ_isUnit hg (zero_mem_hcDom _ _)
  rw [kapQ, Matrix.mul_zero, zero_add, e] at this
  rw [h2, det_mul]
  exact this.mul hB

theorem domPt_lact [Fintype Tau] (hp : X.p0 = r - j) (γ : GL (Fin r) E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    domPt X hj ι (lact γ x) = moebI (toUpq X hj ι γ) (domPt X hj ι x) := by
  funext t
  have hu := frameCo_isUnit₂₂ X hj hp hx (ι t)
  have e : frameCo X hj (lact γ x) (ι t) = (toUpq X hj ι γ t).1 * frameCo X hj x (ι t) := by
    rw [toUpq_val]
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    congr 1
    show _ * (γ.1.map (ι t).1 * mat x (ι t)) = _ * (γ.1.map (ι t).1 * mat (x0F X) (ι t)) * _
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (det_x0F X (ι t)).isUnit]
  simp only [domPt, moebI, moeb_zero]
  rw [e]
  set g := (toUpq X hj ι γ t).1
  set f := frameCo X hj x (ι t)
  have e1 : (g * f).toBlocks₁₂ = (g.toBlocks₁₁ * (f.toBlocks₁₂ * f.toBlocks₂₂⁻¹) + g.toBlocks₁₂) * f.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks f, fromBlocks_multiply]
    simp [Matrix.add_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu]
  have e2 : (g * f).toBlocks₂₂ = (g.toBlocks₂₁ * (f.toBlocks₁₂ * f.toBlocks₂₂⁻¹) + g.toBlocks₂₂) * f.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks f, fromBlocks_multiply]
    simp [Matrix.add_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu]
  rw [e1, e2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu, moeb]

def hodgeC (t : Tau) : ℝ := Real.pi * X.c (ι t)

theorem hodgeC_pos (t : Tau) : 0 < hodgeC X ι t :=
  mul_pos Real.pi_pos (mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne)))

theorem psi_nonempty : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate τ, by_contra fun h' => h ((X.cmType τ).2 h')⟩⟩

theorem sum_nonempty {r j : ℕ} (hj : j ≤ r) (hr : 0 < r) : Nonempty (Fin j ⊕ Fin (r - j)) := ⟨idx hj ⟨0, hr⟩⟩

section Models

variable {Comp : Type} [Fintype Comp] [Fintype Tau] (Y : Comp → Data E r) (hr : 0 < r)
  (hp : ∀ k, (Y k).p0 = r - j) (κ : ∀ k, Tau ≃ (Y k).Ψ)
  (B : ∀ k, BdData Tau j (r - j) (gammaU (Y k) hj (κ k))) (s : Comp → Tau → ℂˣ)

def cxOfModels : CxPkg Tau r j Comp where
  Γ := fun k => gammaU (Y k) hj (κ k)
  Γ_le := fun k => gammaU_le (Y k) hj (κ k) (hp k)
  volC := fun k => covol (Y k)
  volC_pos := fun k => covol_pos (Y k)
  rfn := fun z => onQuot (B z.1).r z.2
  rfn_ge := fun z => (B z.1).exp_le_r (Quot.out z.2).2
  hLo := fun z => onQuot (fun w => eigLo (hodgeI (hodgeC (Y z.1) (κ z.1)) w) ((B z.1).met w)) z.2
  hUp := fun z => onQuot (fun w => eigUp (hodgeI (hodgeC (Y z.1) (κ z.1)) w) ((B z.1).met w)) z.2
  hLo_le := fun z =>
    haveI : Nonempty Tau := (psi_nonempty (Y z.1)).map (κ z.1).symm
    haveI := sum_nonempty hj hr
    eigLo_pos (fun t => hodge_posDef (hodgeC_pos _ _ t) ((Quot.out z.2).2 t)) ((B z.1).met_posDef (Quot.out z.2).2)
  connN := fun z => onQuot (connNorm (hodgeI (hodgeC (Y z.1) (κ z.1))) (B z.1).met (B z.1).beta) z.2
  curvN := fun z => onQuot (curvNorm (hodgeI (hodgeC (Y z.1) (κ z.1))) (B z.1).beta) z.2
  normDetInf := fun t z => onQuot
    (fun w => detNorm (hodgeC (Y z.1) (κ z.1)) ((s z.1 t : ℂ) / (mat (x0F (Y z.1)) (κ z.1 t)).det) w t) z.2

def ptOfFrame (k : Comp) (x : (Y k).dom) : (cxOfModels hj Y hr hp κ B s).XC :=
  ⟨k, Quot.mk _ ⟨domPt (Y k) hj (κ k) x, domPt_mem (Y k) hj (κ k) (hp k) x.2⟩⟩


def invariantB (k : Comp) : BdData Tau j (r - j) (gammaU (Y k) hj (κ k)) :=
  invariantData (gammaU_le (Y k) hj (κ k) (hp k)) (hodgeC (Y k) (κ k)) (hodgeC_pos _ _)

end Models

section Moduli

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j)

include hU e in
theorem le_of_isUnf : j ≤ r := by have := hU.1; omega

include hU e in
theorem first_index_eq_of_unfolded (k : U.Comp) : (U.X k).p0 = r - j := by
  have := hU.1; have := (hU.2.1 k).1; omega

def cmEquiv (T : Tau ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (k : U.Comp) : Tau ≃ (U.X k).Ψ :=
  T.trans (Equiv.subtypeEquivRight fun τ => ((hU.2.1 k).2 τ).symm)

def letterAt (hσ : GoodEmb c σ) :
    {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} :=
  (Equiv.ofBijective _ (GlobalTheory.Relab.relab_good E H l c σ hσ).1).subtypeEquiv
    fun τ => ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ).symm

variable [Fintype Tau] (hr : 0 < r) (T : Tau ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0})
  (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k))) (s : U.Comp → Tau → ℂˣ)

def cxTrue : CxPkg Tau r j U.Comp :=
  cxOfModels (le_of_isUnf U hU e) U.X hr (first_index_eq_of_unfolded U hU e) (cmEquiv U hU T) B s


end Moduli

end GlobalTheory.TrueCx
end
end
