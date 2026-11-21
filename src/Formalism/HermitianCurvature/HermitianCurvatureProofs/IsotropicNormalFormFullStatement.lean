import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section dpsi

variable {k r : ℕ}

theorem hpk_col_esI (a : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r l (esI k r a) = if l.val = a.val then 1 else 0 := by
  have ha := a.isLt
  have hl := l.isLt
  unfold Hpk esI
  by_cases hla : l.val = a.val
  · rw [if_pos (by simp only [Fin.val_mk]; omega), if_pos hla]
  · rw [if_neg (by simp only [Fin.val_mk]; omega), if_neg (by simp only [Fin.val_mk]; omega),
      if_neg (by simp only [Fin.ext_iff, Fin.val_mk]; omega), if_neg hla]

theorem hpk_W_row (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w p = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2.symm)]

theorem hpk_W_col (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r p w = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2)]

theorem hpk_W_sq (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) : Hpk k r w w * Hpk k r w w = 1 := by
  unfold Hpk
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hw.1, hw.2, rfl⟩]
  split_ifs <;> norm_num

theorem herm_Hpk_bvec_eq_star_mul_diag_of_middle (z' : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    herm (Hpk k r) (bvec p) z' = star (z' p) * Hpk k r p p := by
  have hc : ∀ l, Hpk k r l p = if l = p then Hpk k r p p else 0 := fun l => hpk_W_col p l hp
  unfold herm bvec
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single p]
  · intro l _ hl
    rw [hc l, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem unit_entry (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (i j : Fin (2 * r + k + 1)) :
    (∑ l, star (X l i) * Hpk k r l j) + ∑ l, Hpk k r i l * X l j = 0 := by
  have h := congrFun (congrFun hU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h

theorem unit_a (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (a : Fin r) (ha : a.val + 1 < r) :
    X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) = -star (X (eI k r a) (eI k r ⟨a.val + 1, ha⟩)) := by
  have hcol : ∀ l, Hpk k r l (esI k r a) = if l = eI k r a then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r (eI k r ⟨a.val + 1, ha⟩) l = if l = esI k r ⟨a.val + 1, ha⟩ then 1 else 0 := by
    intro l
    unfold Hpk eI esI
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) | omega | norm_num | simp_all | (simp_all; omega)
  have h := unit_entry X hU (eI k r ⟨a.val + 1, ha⟩) (esI k r a)
  simp only [hcol, hrow, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  linear_combination h

theorem unit_w (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hr : 1 ≤ r) (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w w * X w (esI k r ⟨r - 1, by omega⟩) = -star (X (eI k r ⟨r - 1, by omega⟩) w) := by
  have hcol : ∀ l, Hpk k r l (esI k r ⟨r - 1, by omega⟩) = if l = eI k r ⟨r - 1, by omega⟩ then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r w l = if l = w then Hpk k r w w else 0 := fun l => hpk_W_row w l hw
  have h := unit_entry X hU w (esI k r ⟨r - 1, by omega⟩)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Finset.sum_eq_single w (fun l _ hl => by rw [hrow l, if_neg hl, zero_mul])
    (fun h' => absurd (Finset.mem_univ w) h')] at h
  linear_combination h

end dpsi

theorem dpsi_is_derivation : DpsiDerivation := by
  intro k r z' X hr hz' hU _

  let in1 : Fin (2 * r + k + 1) → ℂ := fun p => if h : p.val + 1 < r then X p ⟨p.val + 1, by omega⟩ else 0
  let in2 : Fin (2 * r + k + 1) → ℂ := fun p => if p.val + 1 = r then (X *ᵥ z') p else 0
  let in3 : Fin (2 * r + k + 1) → ℂ := fun p => -star (X (eI k r ⟨r - 1, by omega⟩) p * z' p)
  let in4 : Fin (2 * r + k + 1) → ℂ := fun p => if h : r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 then X p ⟨p.val + 1, h.2⟩ else 0
  have hrow : ∀ p : Fin (2 * r + k + 1), ∑ q, X p q * dpsiP k r z' p q =
      in1 p + in2 p + (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0)
        + in4 p := by
    intro p
    by_cases h1 : p.val + 1 < r
    · rw [Finset.sum_eq_single ⟨p.val + 1, by omega⟩]
      · rw [dp1 _ _ _ (by omega) (by simp; omega), if_pos (by simp), mul_one]
        simp only [in1, in2, in4, dif_pos h1, if_neg (show ¬ p.val + 1 = r by omega), dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        ring
      · intro q _ hq
        by_cases hq1 : q.val < r
        · rw [dp1 _ _ _ (by omega) hq1, if_neg, mul_zero]; intro h'; apply hq; ext; simp; omega
        · by_cases hq2 : q.val ≤ r + k
          · rw [dp2 _ _ _ (by omega) (by omega) hq2, if_neg (by omega), mul_zero]
          · rw [dp0 _ _ _ (by omega) (by omega), mul_zero]
      · simp
    · by_cases h2 : p.val + 1 = r
      · have hterm : ∀ q, X p q * dpsiP k r z' p q = X p q * z' q := by
          intro q
          by_cases hq1 : q.val < r
          · rw [dp1 _ _ _ (by omega) hq1, if_neg (by omega), hz' q (by omega)]
          · by_cases hq2 : q.val ≤ r + k
            · rw [dp2 _ _ _ (by omega) (by omega) hq2, if_pos h2]
            · rw [dp0 _ _ _ (by omega) (by omega), hz' q (by omega)]
        simp only [hterm, in1, in2, in4, dif_neg h1, if_pos h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        simp [Matrix.mulVec, dotProduct]
      · by_cases h3 : p.val ≤ r + k
        · rw [Finset.sum_eq_single (esI k r ⟨r - 1, by omega⟩)]
          · rw [dp3 _ _ _ (by omega) h3 (by simp [esI]; omega), if_pos (by simp [esI]; omega)]
            simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
              if_pos (show r ≤ p.val ∧ p.val ≤ r + k by omega)]
            ring
          · intro q _ hq
            by_cases hq1 : q.val ≤ r + k
            · have : ¬ (r ≤ q.val ∧ q.val ≤ r + k ∧ r + k < q.val) := by omega
              unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
            · rw [dp3 _ _ _ (by omega) h3 (by omega), if_neg, mul_zero]
              intro h'; apply hq; ext; simp [esI]; omega
          · simp
        · by_cases h4 : p.val + 1 < 2 * r + k + 1
          · rw [Finset.sum_eq_single ⟨p.val + 1, h4⟩]
            · rw [dp4 _ _ _ (by omega) (by simp; omega), if_pos (by simp), mul_one]
              simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_pos (show r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 from ⟨by omega, h4⟩),
                if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _ hq
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, if_neg, mul_zero]; intro h'; apply hq; ext; simp; omega
              · unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
            · simp
          · rw [Finset.sum_eq_zero]
            · simp only [in1, in2, in4, dif_neg h1, if_neg h2, dif_neg (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
                if_neg (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, if_neg (by omega), mul_zero]
              · unfold dpsiP; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]

  have h3eq : ∀ p : Fin (2 * r + k + 1), (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0) =
      in3 p := by
    intro p
    simp only [in3]
    split_ifs with hp
    · rw [herm_Hpk_bvec_eq_star_mul_diag_of_middle z' p hp]
      have hu := unit_w X hU hr p hp
      have hsq := hpk_W_sq (k := k) p hp
      rw [star_mul']
      linear_combination (star (z' p)) * hu
        + (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp) - (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp)
    · rw [hz' p (by omega)]; simp
  simp_rw [hrow, h3eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  set L1 : ℂ := ∑ a : Fin r, if h : a.val + 1 < r then X (eI k r a) (eI k r ⟨a.val + 1, h⟩) else 0 with hL1
  set M2 : ℂ := (X *ᵥ z') (eI k r ⟨r - 1, by omega⟩) with hM2
  have s2 : ∑ p, in2 p = M2 := by
    rw [Finset.sum_eq_single (eI k r ⟨r - 1, by omega⟩)]
    · simp only [in2]; rw [if_pos (show (eI k r ⟨r - 1, by omega⟩).val + 1 = r by simp [eI]; omega)]
    · intro p _ hp; simp only [in2]; rw [if_neg]; intro h'; apply hp; ext; simp [eI]; omega
    · simp
  have s3 : ∑ p, in3 p = -star M2 := by
    simp only [in3, M2, Matrix.mulVec, dotProduct]
    rw [Finset.sum_neg_distrib, star_sum]
  have e1inj : Function.Injective (eI k r) := fun a b h => by
    have := congrArg Fin.val h; simp [eI] at this; exact Fin.ext this
  have s1 : ∑ p, in1 p = L1 := by
    rw [hL1, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨eI k r, e1inj⟩))]
    · rw [Finset.sum_map]; rfl
    · intro p _ hp
      simp only [in1]
      rw [dif_neg]
      intro h'
      apply hp
      exact Finset.mem_map.mpr ⟨⟨p.val, by omega⟩, Finset.mem_univ _, by ext; simp [eI]⟩
  have e4inj : Function.Injective (fun a : Fin r => (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h; have := congrArg Fin.val h; simp at this; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
  have s4 : ∑ p, in4 p = -star L1 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, e4inj⟩))]
    · rw [Finset.sum_map, hL1, star_sum, ← Finset.sum_neg_distrib]
      congr 1; ext a
      have hav := a.isLt
      simp only [in4, Function.Embedding.coeFn_mk]
      by_cases ha : a.val + 1 < r
      · rw [dif_pos ⟨by omega, by omega⟩, dif_pos ha]
        have hu := unit_a X hU a ha
        have e1 : (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1)) = esI k r ⟨a.val + 1, ha⟩ := by
          ext; simp [esI]; omega
        have e2 : (⟨2 * r + k - 1 - a.val + 1, by omega⟩ : Fin (2 * r + k + 1)) = esI k r a := by
          ext; simp [esI]; omega
        have hx : ∀ p q : Fin (2 * r + k + 1), p = esI k r ⟨a.val + 1, ha⟩ → q = esI k r a →
            X p q = X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) := by
          rintro p q rfl rfl; rfl
        rw [hx _ _ e1 e2, hu]
      · rw [dif_neg (by omega), dif_neg ha, star_zero, neg_zero]
    · intro p _ hp
      simp only [in4]
      rw [dif_neg]
      rintro ⟨h1, h2⟩
      apply hp
      exact Finset.mem_map.mpr ⟨⟨2 * r + k - 1 - p.val, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  rw [s1, s2, s3, s4]
  unfold dEll
  rw [← hL1, ← hM2, star_add]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

section N1

variable {k r : ℕ}

theorem tau_val (p : Fin (2 * r + k + 1)) :
    (tau k r p).val = if p.val < r ∨ r + k < p.val then 2 * r + k - p.val else p.val := rfl

theorem sgn_one (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : WeylGroupFacts.sgn k r p = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg h]

theorem mulVec_hpk (v : Fin (2 * r + k + 1) → ℂ) (l : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) l = WeylGroupFacts.sgn k r l * v (tau k r l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (tau k r l)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_row, if_neg hm, zero_mul]
  · simp

theorem herm_expand (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ l, star (w l) * (WeylGroupFacts.sgn k r l * v (tau k r l)) := by
  unfold herm; simp only [dotProduct, mulVec_hpk, Pi.star_apply]

theorem mul_hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p q : Fin (2 * r + k + 1)) :
    (M * Hpk k r) p q = M p (tau k r q) * WeylGroupFacts.sgn k r q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r q)]
  · rw [hpk_symm, hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_symm, hpk_row, if_neg hm, mul_zero]
  · simp

variable (k r) in

def Ym (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => y a (esI k r (Fin.castLE hj b))

variable (k r) in

def Zv (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (b : Fin j) : Fin (2 * r + k + 1) → ℂ :=
  fun p => ∑ a, (Ym k r j hj y)⁻¹ b a * y a p

variable (k r) in

def Cf (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (l q : Fin (2 * r + k + 1)) : ℂ :=
  if h : r + k < q.val ∧ 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h.2⟩ l else 0

variable (k r) in

def Tn (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r then
    (if r ≤ q.val ∧ q.val ≤ r + k then -(WeylGroupFacts.sgn k r q) * star (Cf k r j hj y q (tau k r p))
     else if r + k < q.val then
       (if h : 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h⟩ p
        else if h' : p.val < j then -star (Zv k r j hj y ⟨p.val, h'⟩ (tau k r q)) else 0)
     else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k then Cf k r j hj y p q
  else 0

end N1

section MajorantSquareBound

variable {k r : ℕ}







theorem esI_val (b : Fin r) : (esI k r b).val = 2 * r + k - b.val := rfl





end MajorantSquareBound

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2

variable {k r : ℕ}

theorem sg_esI (b : Fin r) : NFOne.sg k r (esI k r b) = eI k r b := by
  have hb := b.isLt
  ext
  simp only [NFOne.sg, esI, eI]
  omega

theorem pm_col_star (j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (b : Fin r) (hb : b.val < j) :
    (1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b) = V b.val := by
  funext p
  have hb' := b.isLt
  have hq : r + k < (esI k r b).val := by simp only [esI]; omega
  have hsg : (NFOne.sg k r (esI k r b)).val = b.val := by rw [sg_esI]; rfl
  have hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p =
      (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b) := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply, add_mul]
  rw [hcol]
  by_cases hp1 : p.val < r
  · rw [NFOne.P_XS k r j V p _ hp1 hq, hsg, if_pos hb, if_neg (fun e => by rw [e] at hp1; omega), zero_add]
  · by_cases hp2 : p.val ≤ r + k
    · rw [NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, if_neg (fun e => by rw [e] at hp2; omega), zero_add]
    · rw [NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]
      have e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val := by
        rw [Fin.ext_iff]; simp only [NFOne.sg, esI]; omega
      by_cases h1 : p = esI k r b
      · rw [if_pos h1, if_pos (e.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (e.mpr h2))]

theorem one_add_projection_mem_isotropic_set (j : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + NFOne.Pm k r j V) ∈ N0set k r z' := by
  refine ⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a,
    NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · rw [Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]
  · rw [Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]

private theorem mul_mem_n0set {z' : Fin (2 * r + k + 1) → ℂ}
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ N0set k r z') (hh : h ∈ N0set k r z') :
    g * h ∈ N0set k r z' := by
  obtain ⟨gU, gX, gz, gW, gS⟩ := hg
  obtain ⟨hU, hX, hz, hW, hS⟩ := hh

  have col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0 := by
    intro p m hm
    have := congrFun (gX ⟨m.val, hm⟩) p
    simpa [bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val →
      ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) →
      ∀ m, g p m * h m q = if m = q then g p q else 0 := by
    intro p q hp hq m
    have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hm1 : m.val < r
    · rw [col p m hm1, if_neg (fun e => by rw [e] at hp; omega), zero_mul,
        if_neg (fun e => by rw [e] at hm1; omega)]
    · have tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0 := by
        intro hmq
        by_cases e : m = q
        · subst e; simp [hmq]
        · simp [hmq, e]
      by_cases hm2 : m.val ≤ r + k
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · rw [gW p m (by omega) hm2 hp, if_neg (fun e => by rw [e] at hp2; omega), zero_mul,
            if_neg (fun e => by rw [e] at hm2; omega)]
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · exact tail (hS m q hq1 (by omega))
  refine ⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · change (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    change gᴴ * Hpk k r * g = Hpk k r at gU
    change hᴴ * Hpk k r * h = Hpk k r at hU
    rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [Matrix.mul_assoc], gU, hU]
  · rw [← Matrix.mulVec_mulVec, hX, gX]
  · rw [← Matrix.mulVec_mulVec, hz, gz]
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gW p q hq1 hq2 hp
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gS p q hq hp

theorem mul_mem_isotropic_unipotent_set (z' : Fin (2 * r + k + 1) → ℂ) (j1 j2 : ℕ) (V1 V2 : ℕ → Fin (2 * r + k + 1) → ℂ)
    (h1 : (1 + NFOne.Pm k r j1 V1) ∈ N0set k r z') (h2 : (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z') :
    (1 + NFOne.Pm k r j1 V1) * (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z' := by
  exact mul_mem_n0set h1 h2

theorem herm_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  have hrow : ∀ q : Fin (2 * r + k + 1), Hpk k r (esI k r b) q = if q = eI k r b then 1 else 0 := by
    intro q
    have e : q = eI k r b ↔ q.val = b.val := by rw [Fin.ext_iff]; simp only [eI]
    by_cases h1 : q = eI k r b
    · rw [if_pos h1]; have := e.mp h1
      unfold Hpk
      rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1]; have := fun h => h1 (e.mpr h)
      unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨-, h2, -⟩; omega)]
  simp only [herm, bvec, dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul, hrow]
    simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp

end N2

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section SpacedProductLowerBound

variable {k : ℕ}

def pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) : Fin m :=
  ⟨if c < i.val then c else c - 1, by split_ifs <;> omega⟩

theorem succAbove_pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) :
    (i.succAbove (pidx m i c h)).val = c := by
  rw [succAbove_val]; unfold pidx; simp only; split_ifs <;> omega

theorem pidx_succAbove (m : ℕ) (i : Fin (m + 1)) (b : Fin m) (h : (i.succAbove b).val < m + 1 ∧ (i.succAbove b).val ≠ i.val) :
    pidx m i (i.succAbove b).val h = b := by
  ext; unfold pidx; simp only; rw [succAbove_val]; split_ifs <;> omega

theorem herm_add_smul_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w1 w2 : Fin n → ℂ) (a b : ℂ) :
    herm H v (a • w1 + b • w2) = star a * herm H v w1 + star b * herm H v w2 := by
  unfold herm
  simp [star_add, star_smul, add_dotProduct, smul_dotProduct]

def ViF (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ) : Fin (2 * (m + 1) + k + 1) → ℂ :=
  fun p => if p = esI k (m + 1) i then 1
    else if h : p.val < m + 1 ∧ p.val ≠ i.val then -star (Vc (pidx m i p.val h) (eI k (m + 1) i)) else 0

variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem insertion_vector_zero_off_index (p : Fin (2 * (m + 1) + k + 1)) (hp : m + 1 ≤ p.val) (hne : p ≠ esI k (m + 1) i) : ViF m i Vc p = 0 := by
  unfold ViF; rw [if_neg hne, dif_neg (by omega)]

theorem ViF_eI : ViF m i Vc (eI k (m + 1) i) = 0 := by
  unfold ViF
  rw [if_neg, dif_neg]
  · simp [eI]
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega

theorem tau_eI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (eI k (m + 1) c) = esI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by left; simp only [eI]; omega)]; simp only [eI, esI]

theorem tau_esI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (esI k (m + 1) c) = eI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by right; simp only [esI]; omega)]; simp only [esI, eI]; omega

end SpacedProductLowerBound

section N2c

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem sg_val' (q : Fin (2 * (m + 1) + k + 1)) : (NFOne.sg k (m + 1) q).val = 2 * (m + 1) + k - q.val := rfl

theorem ViF_alt (l : Fin (2 * (m + 1) + k + 1)) : ViF m i Vc l = 0 ∨ ViF m i Vc (WeylGroupFacts.tau k (m + 1) l) = 0 := by
  by_cases h1 : l = esI k (m + 1) i
  · right; rw [h1, tau_esI]; exact ViF_eI m i Vc
  by_cases h2 : l = eI k (m + 1) i
  · left; rw [h2]; exact ViF_eI m i Vc
  by_cases h3 : m + 1 ≤ l.val
  · left; exact insertion_vector_zero_off_index m i Vc l h3 h1
  · right
    apply insertion_vector_zero_off_index
    · rw [tau_val]; split_ifs <;> omega
    · intro h; apply h2
      have := congrArg (WeylGroupFacts.tau k (m + 1)) h
      rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this

theorem ViF_iso : herm (Hpk k (m + 1)) (ViF m i Vc) (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  rcases ViF_alt m i Vc l with h | h <;> simp [h]

theorem hermitian_insertion_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') :
    herm (Hpk k (m + 1)) z' (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
  · rw [insertion_vector_zero_off_index m i Vc l hW.1 (by intro h; rw [h] at hW; simp [esI] at hW; omega)]; simp
  · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp

theorem ViF_star (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    ViF m i Vc q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]
    unfold ViF; rw [if_pos h]
  · rw [insertion_vector_zero_off_index m i Vc q (by omega) h, if_neg]
    intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

theorem ViF_Vc (hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0) (c' : Fin m) :
    herm (Hpk k (m + 1)) (ViF m i Vc) (Vc c') = 0 := by
  have hs := (i.succAbove c').isLt
  have hsi : (i.succAbove c').val ≠ i.val := fun h' => Fin.succAbove_ne i c' (Fin.ext h')
  rw [herm_expand, Finset.sum_eq_add (eI k (m + 1) i) (esI k (m + 1) (i.succAbove c'))]
  · rw [tau_eI, tau_esI]
    have e1 : ViF m i Vc (esI k (m + 1) i) = 1 := by unfold ViF; rw [if_pos rfl]
    have e2 : ViF m i Vc (eI k (m + 1) (i.succAbove c')) = -star (Vc c' (eI k (m + 1) i)) := by
      unfold ViF
      rw [if_neg (by intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega),
        dif_pos ⟨by simp only [eI]; omega, by simpa [eI] using hsi⟩]
      congr 3
      have := pidx_succAbove m i c' ⟨hs, hsi⟩
      simpa [eI] using this
    have e3 : Vc c' (esI k (m + 1) (i.succAbove c')) = 1 := by
      rw [hVs c' _ (by simp [esI]; omega), if_pos (by rw [sg_val']; simp [esI]; omega)]
    rw [e1, e2, e3, sgn_one _ (by simp [eI]; omega), sgn_one _ (by simp [esI]; omega)]
    simp
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega
  · intro l _ hl
    by_cases hS : m + 1 + k < l.val
    · rw [hVs c' l hS, if_neg]
      · simp
      · intro h'; apply hl.2; ext; rw [sg_val'] at h'; simp [esI]; omega
    · by_cases hX : l.val < m + 1
      · rw [insertion_vector_zero_off_index m i Vc (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]
        · simp
        · intro h; apply hl.1
          have := congrArg (WeylGroupFacts.tau k (m + 1)) h
          rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this
      · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
        rw [ht, insertion_vector_zero_off_index m i Vc l (by omega) (by intro h; rw [h] at hS; simp [esI] at hS; omega)]; simp
  · simp
  · simp

end N2c

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2d

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (ν : Fin (2 * (m + 1) + k + 1) → ℂ)

def VpF : Fin (2 * (m + 1) + k + 1) → ℂ := fun p =>
  bvec (esI k (m + 1) i) p - ν p + (-(herm (Hpk k (m + 1)) ν ν) / 2) * bvec (eI k (m + 1) i) p

theorem eI_ne_esI (a b : Fin (m + 1)) : eI k (m + 1) a ≠ esI k (m + 1) b := by
  intro h; have := congrArg Fin.val h; simp [eI, esI] at this; have := a.isLt; have := b.isLt; omega

theorem VpF_star (hν : inWb k (m + 1) ν) (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    VpF m i ν q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  unfold VpF
  rw [hν q (Or.inr hq)]
  have hq2 : q ≠ eI k (m + 1) i := by intro h; rw [h] at hq; simp [eI] at hq; omega
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]; simp [bvec, h, Pi.single_apply, hq2, Ne.symm (eI_ne_esI m i i)]
  · rw [if_neg]
    · simp [bvec, Pi.single_apply, h, hq2]
    · intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

theorem VpF_iso (hν : inWb k (m + 1) ν) : herm (Hpk k (m + 1)) (VpF m i ν) (VpF m i ν) = 0 := by
  have hi := i.isLt
  set γ : ℂ := -(herm (Hpk k (m + 1)) ν ν) / 2 with hγ
  have hpt : ∀ l, star (VpF m i ν l) * (WeylGroupFacts.sgn k (m + 1) l * VpF m i ν (WeylGroupFacts.tau k (m + 1) l)) =
      (if l = eI k (m + 1) i then star γ else 0) + (if l = esI k (m + 1) i then γ else 0) +
        star (ν l) * (WeylGroupFacts.sgn k (m + 1) l * ν (WeylGroupFacts.tau k (m + 1) l)) := by
    intro l
    unfold VpF
    rw [← hγ]
    by_cases h1 : l = eI k (m + 1) i
    · subst h1
      rw [tau_eI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)),
        sgn_one _ (by simp [eI]; omega)]
      simp [bvec, Pi.single_apply, eI_ne_esI]
    by_cases h2 : l = esI k (m + 1) i
    · subst h2
      rw [tau_esI, hν (eI k (m + 1) i) (Or.inl (by simp only [eI]; omega)), hν (esI k (m + 1) i) (Or.inr (by simp [esI]; omega)),
        sgn_one _ (by simp [esI]; omega)]
      simp [bvec, Pi.single_apply, Ne.symm (eI_ne_esI m i i)]
    by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
    · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
      rw [ht]
      simp [bvec, Pi.single_apply, h1, h2]
      try ring
    · rw [hν l (by omega)]
      have ha : bvec (esI k (m + 1) i) l = 0 := by simp [bvec, Pi.single_apply, h2]
      have hb : bvec (eI k (m + 1) i) l = 0 := by simp [bvec, Pi.single_apply, h1]
      rw [ha, hb]
      simp [h1, h2]
  rw [herm_expand, Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← herm_expand]
  have hreal : star (herm (Hpk k (m + 1)) ν ν) = herm (Hpk k (m + 1)) ν ν := (herm_swap k (m + 1) ν ν).symm
  rw [hγ, star_div₀, star_neg, hreal]
  simp
  try ring

theorem VpF_esI (hν : inWb k (m + 1) ν) (c : Fin (m + 1)) (hc : c ≠ i) :
    herm (Hpk k (m + 1)) (VpF m i ν) (bvec (esI k (m + 1) c)) = 0 := by
  rw [herm_bvec_esI]
  unfold VpF
  rw [hν _ (Or.inl (by simp only [eI]; omega))]
  have h1 : eI k (m + 1) c ≠ eI k (m + 1) i := by
    intro h; apply hc; ext; have := congrArg Fin.val h; simpa [eI] using this
  simp [bvec, Pi.single_apply, h1, eI_ne_esI]

theorem hermitian_perturbed_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') (hν : inWb k (m + 1) ν)
    (hzν : herm (Hpk k (m + 1)) z' ν = 0) : herm (Hpk k (m + 1)) z' (VpF m i ν) = 0 := by
  have : herm (Hpk k (m + 1)) z' (VpF m i ν) = -herm (Hpk k (m + 1)) z' ν := by
    rw [herm_expand, herm_expand, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
    · unfold VpF
      have h1 : l ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
      have h2 : l ≠ esI k (m + 1) i := by intro h; rw [h] at hW; simp [esI] at hW; omega
      simp [bvec, Pi.single_apply, h1, h2]
    · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp
  rw [this, hzν, neg_zero]

theorem bvec_esI_iso (b c : Fin (m + 1)) :
    herm (Hpk k (m + 1)) (bvec (esI k (m + 1) b)) (bvec (esI k (m + 1) c)) = 0 := by
  rw [herm_bvec_esI]; simp [bvec, Pi.single_apply, Ne.symm (eI_ne_esI m c b)]

theorem bvec_esI_star (c : Fin (m + 1)) (q : Fin (2 * (m + 1) + k + 1)) :
    bvec (esI k (m + 1) c) q = if (NFOne.sg k (m + 1) q).val = c.val then 1 else 0 := by
  have := c.isLt
  simp only [bvec, Pi.single_apply]
  by_cases h : q = esI k (m + 1) c
  · rw [if_pos h, if_pos (by rw [sg_val', h]; simp [esI]; omega)]
  · rw [if_neg h, if_neg]; intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; have := q.isLt; omega

end N2d

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

theorem isotropicNormalFormFull_statement : IsotropicNormalFormFull := by
  intro k m z' i y t hz hZ ht hyi hyi2 hdet hzy hzyi hiso
  have hiv := i.isLt

  set Y' : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun a b : Fin m => y (i.succAbove a) (esI k (m + 1) (i.succAbove b)) with hY'
  have hu : IsUnit Y'.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨N, hN⟩ : ∃ N, N = Y'⁻¹ := ⟨_, rfl⟩
  have hNY : N * Y' = 1 := by rw [hN]; exact Matrix.nonsing_inv_mul _ hu
  have hYN : Y' * N = 1 := by rw [hN]; exact Matrix.mul_nonsing_inv _ hu
  set Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ := fun b => ∑ a, N b a • y (i.succAbove a) with hVcdef
  have hsne : ∀ b : Fin m, (i.succAbove b).val ≠ i.val := fun b h' => Fin.succAbove_ne i b (Fin.ext h')
  have hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0 := by
    intro b q hq
    have hqv := q.isLt
    simp only [Vc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hqi : (NFOne.sg k (m + 1) q).val = i.val
    · have hq' : q = esI k (m + 1) i := by ext; rw [sg_val'] at hqi; simp [esI]; omega
      rw [if_neg (by rw [hqi]; exact (hsne b).symm)]
      apply Finset.sum_eq_zero; intro a _
      rw [hq', hyi _ (Fin.succAbove_ne i a), mul_zero]
    · have hc : (NFOne.sg k (m + 1) q).val < m + 1 ∧ (NFOne.sg k (m + 1) q).val ≠ i.val := ⟨by rw [sg_val']; omega, hqi⟩
      set b'' := pidx m i _ hc with hb''
      have hq' : q = esI k (m + 1) (i.succAbove b'') := by
        ext; have := succAbove_pidx m i _ hc; rw [← hb''] at this; rw [sg_val'] at this; simp [esI]; omega
      have e := congrFun (congrFun hNY b) b''
      rw [Matrix.mul_apply, Matrix.one_apply] at e
      conv_lhs => rw [hq']
      simp only [hY', Matrix.of_apply] at e
      rw [e]
      have hsb := succAbove_pidx m i _ hc
      rw [← hb''] at hsb
      by_cases hbb : b = b''
      · rw [if_pos hbb, if_pos (by rw [hbb]; exact hsb.symm)]
      · rw [if_neg hbb, if_neg]
        intro h'; apply hbb
        have : i.succAbove b = i.succAbove b'' := by ext; rw [← h', hsb]
        exact Fin.succAbove_right_injective this
  set V1 : ℕ → Fin (2 * (m + 1) + k + 1) → ℂ := fun c =>
    if hc : c < m + 1 ∧ c ≠ i.val then Vc (pidx m i c hc) else if c = i.val then ViF m i Vc else 0 with hV1def
  have hV1c : ∀ b : Fin m, V1 (i.succAbove b).val = Vc b := by
    intro b
    simp only [V1]
    rw [dif_pos ⟨(i.succAbove b).isLt, hsne b⟩, pidx_succAbove]
  have hV1i : V1 i.val = ViF m i Vc := by
    simp [V1]
  have hyy' : ∀ a a' : Fin m, herm (Hpk k (m + 1)) (y (i.succAbove a)) (y (i.succAbove a')) = 0 :=
    fun a a' => hiso _ _
  have hVciso : ∀ b c : Fin m, herm (Hpk k (m + 1)) (Vc b) (Vc c) = 0 :=
    fun b c => NFOne.herm_comb k (m + 1) m (fun a => y (i.succAbove a)) hyy' _ _

  have V1_0 : ∀ c, m + 1 ≤ c → V1 c = 0 := by
    intro c hc; simp only [V1]; rw [dif_neg (by omega), if_neg (by omega)]
  have V1_cases : ∀ c, c < m + 1 → (c = i.val ∧ V1 c = ViF m i Vc) ∨
      (∃ b : Fin m, (i.succAbove b).val = c ∧ V1 c = Vc b) := by
    intro c hc
    by_cases hci : c = i.val
    · left; exact ⟨hci, by rw [hci, hV1i]⟩
    · right
      refine ⟨pidx m i c ⟨hc, hci⟩, succAbove_pidx m i c ⟨hc, hci⟩, ?_⟩
      simp only [V1]; rw [dif_pos ⟨hc, hci⟩]
  have V1_s : ∀ b, b < m + 1 → ∀ q : Fin (2 * (m + 1) + k + 1), m + 1 + k < q.val →
      V1 b q = if (NFOne.sg k (m + 1) q).val = b then 1 else 0 := by
    intro b hb q hq
    rcases V1_cases b hb with ⟨hbi, hv⟩ | ⟨b', hb', hv⟩
    · rw [hv, ViF_star m i Vc q hq, hbi]
    · rw [hv, hVs b' q hq, hb']
  have V1_iso : ∀ b c, b < m + 1 → c < m + 1 → herm (Hpk k (m + 1)) (V1 b) (V1 c) = 0 := by
    intro b c hb hc
    rcases V1_cases b hb with ⟨_, hv⟩ | ⟨b', _, hv⟩ <;> rcases V1_cases c hc with ⟨_, hw⟩ | ⟨c', _, hw⟩ <;> rw [hv, hw]
    · exact ViF_iso m i Vc
    · exact ViF_Vc m i Vc hVs c'
    · rw [herm_swap, ViF_Vc m i Vc hVs b', star_zero]
    · exact hVciso b' c'
  have V1_z : ∀ c, herm (Hpk k (m + 1)) z' (V1 c) = 0 := by
    intro c
    by_cases hc : c < m + 1
    · rcases V1_cases c hc with ⟨_, hv⟩ | ⟨b', _, hv⟩ <;> rw [hv]
      · exact hermitian_insertion_vector_orthogonal m i Vc z' hz
      · exact NFOne.herm_Hpk_of_inWb_eq_sum_wI k (m + 1) m (fun a => y (i.succAbove a)) z' (fun a => hzy _ (Fin.succAbove_ne i a)) _
    · rw [V1_0 c (by omega)]; simp [herm]
  have hn1 := one_add_projection_mem_isotropic_set (m + 1) z' hz V1 V1_0 V1_s V1_iso V1_z
  set n1 := 1 + NFOne.Pm k (m + 1) (m + 1) V1 with hn1def
  have hn1col : ∀ b : Fin (m + 1), n1 *ᵥ bvec (esI k (m + 1) b) = V1 b.val :=
    fun b => pm_col_star (m + 1) V1 V1_s b b.isLt

  have hU1 : IsUnit n1.det := WeylGroupFacts.isUnit_of_uh hn1.1
  set u := n1⁻¹ *ᵥ y i with hudef
  have hnu : n1 *ᵥ u = y i := by rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU1, Matrix.one_mulVec]
  have hpres := herm_unitary n1 hn1.1
  have u_star : ∀ p : Fin (2 * (m + 1) + k + 1), m + 1 + k < p.val → u p = 0 := by
    intro p hp
    have hpv := p.isLt
    have hpe : p = esI k (m + 1) ⟨2 * (m + 1) + k - p.val, by omega⟩ := by ext; simp [esI]; omega
    have e := herm_bvec_eI (k := k) u (⟨2 * (m + 1) + k - p.val, by omega⟩ : Fin (m + 1))
    rw [hpe, ← e, ← hpres, hnu, hn1.2.1, herm_bvec_eI]
    exact hyi2 _ (by simp [esI]; omega)
  have u_X : ∀ c : Fin (m + 1), c ≠ i → u (eI k (m + 1) c) = 0 := by
    intro c hc
    have e := herm_bvec_esI (k := k) u c
    rw [← e, ← hpres, hnu, hn1col c]
    rcases V1_cases c.val c.isLt with ⟨hci, _⟩ | ⟨b', _, hv⟩
    · exact absurd (Fin.ext hci) hc
    · rw [hv]; exact NFOne.herm_Hpk_of_inWb_eq_sum_wI k (m + 1) m (fun a => y (i.succAbove a)) (y i) (fun a => hiso _ _) _
  set β := u (eI k (m + 1) i) with hβ
  set yb : Fin (2 * (m + 1) + k + 1) → ℂ := fun p => if m + 1 ≤ p.val ∧ p.val ≤ m + 1 + k then u p else 0 with hybdef
  have hyb : inWb k (m + 1) yb := by intro p hp; simp only [yb]; rw [if_neg (by omega)]
  have u_dec : u = fun p => yb p + β * bvec (eI k (m + 1) i) p := by
    funext p
    simp only [yb]
    by_cases hW : m + 1 ≤ p.val ∧ p.val ≤ m + 1 + k
    · have : p ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
      simp [hW, bvec, Pi.single_apply, this]
    · rw [if_neg hW, zero_add]
      by_cases hX : p.val < m + 1
      · by_cases hpi : p.val = i.val
        · have : p = eI k (m + 1) i := by ext; simp [eI, hpi]
          rw [this]; simp [bvec, hβ]
        · have hpe : p = eI k (m + 1) ⟨p.val, hX⟩ := by ext; simp [eI]
          have hne : (⟨p.val, hX⟩ : Fin (m + 1)) ≠ i := by intro h; apply hpi; rw [← h]
          have hne2 : p ≠ eI k (m + 1) i := by intro h; apply hpi; rw [h]; simp [eI]
          rw [hpe, u_X _ hne]; simp [bvec, Pi.single_apply, ← hpe, hne2]
      · have hne2 : p ≠ eI k (m + 1) i := by intro h; apply hX; rw [h]; simp only [eI]; omega
        rw [u_star p (by omega)]; simp [bvec, Pi.single_apply, hne2]
  have tau_W : ∀ l : Fin (2 * (m + 1) + k + 1), m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k → WeylGroupFacts.tau k (m + 1) l = l := by
    intro l hl; ext; rw [tau_val]; split_ifs <;> omega
  have tau_notW : ∀ l : Fin (2 * (m + 1) + k + 1), ¬ (m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k) →
      (WeylGroupFacts.tau k (m + 1) l).val < m + 1 ∨ m + 1 + k < (WeylGroupFacts.tau k (m + 1) l).val := by
    intro l hl; rw [tau_val]; split_ifs <;> omega
  have yb_iso : herm (Hpk k (m + 1)) yb yb = 0 := by
    have : herm (Hpk k (m + 1)) yb yb = herm (Hpk k (m + 1)) u u := by
      rw [herm_expand, herm_expand]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
      · rw [tau_W l hW]; simp only [yb, if_pos hW]
      · have h1 : yb l = 0 := by simp only [yb, if_neg hW]
        rw [h1]
        by_cases hX : l.val < m + 1
        · rw [u_star (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp
        · rw [u_star l (by omega)]; simp
    rw [this, ← hpres, hnu, hiso]
  have yb_z : herm (Hpk k (m + 1)) z' yb = t := by
    have : herm (Hpk k (m + 1)) z' yb = herm (Hpk k (m + 1)) z' u := by
      rw [herm_expand, herm_expand]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
      · simp only [yb, if_pos hW]
      · rw [hz (WeylGroupFacts.tau k (m + 1) l) (tau_notW l hW)]; simp
    rw [this, ← hpres, hnu, hn1.2.2.1, hzyi]

  set Z := herm (Hpk k (m + 1)) z' z' with hZdef
  set c2 : ℂ := star (β / star t) with hc2
  set c1 : ℂ := star (-(β / star t) * Z / t) with hc1
  set ν : Fin (2 * (m + 1) + k + 1) → ℂ := c1 • yb + c2 • z' with hνdef
  have hst : star t ≠ 0 := star_ne_zero.mpr ht
  have hν : inWb k (m + 1) ν := by
    intro p hp; simp only [ν, Pi.add_apply, Pi.smul_apply, hyb p hp, hz p hp, smul_zero, add_zero]
  have hzν : herm (Hpk k (m + 1)) z' ν = 0 := by
    rw [hνdef, herm_add_smul_right, yb_z, hc1, hc2, star_star, star_star]
    field_simp
    ring
  have hybν : herm (Hpk k (m + 1)) yb ν = β := by
    rw [hνdef, herm_add_smul_right, yb_iso, herm_swap k (m + 1) yb z', yb_z]
    simp only [hc2, star_star, mul_zero, zero_add]
    field_simp

  set V2 : ℕ → Fin (2 * (m + 1) + k + 1) → ℂ := fun c =>
    if hc : c < m + 1 then (if c = i.val then VpF m i ν else bvec (esI k (m + 1) ⟨c, hc⟩)) else 0 with hV2def
  have V2_cases : ∀ c (hc : c < m + 1), (c = i.val ∧ V2 c = VpF m i ν) ∨
      (c ≠ i.val ∧ V2 c = bvec (esI k (m + 1) ⟨c, hc⟩)) := by
    intro c hc
    by_cases hci : c = i.val
    · left; refine ⟨hci, ?_⟩; simp only [V2]; rw [dif_pos hc, if_pos hci]
    · right; refine ⟨hci, ?_⟩; simp only [V2]; rw [dif_pos hc, if_neg hci]
  have V2_0 : ∀ c, m + 1 ≤ c → V2 c = 0 := by intro c hc; simp only [V2]; rw [dif_neg (by omega)]
  have V2_s : ∀ b, b < m + 1 → ∀ q : Fin (2 * (m + 1) + k + 1), m + 1 + k < q.val →
      V2 b q = if (NFOne.sg k (m + 1) q).val = b then 1 else 0 := by
    intro b hb q hq
    rcases V2_cases b hb with ⟨hbi, hv⟩ | ⟨_, hv⟩
    · rw [hv, VpF_star m i ν hν q hq, hbi]
    · rw [hv, bvec_esI_star]
  have V2_iso : ∀ b c, b < m + 1 → c < m + 1 → herm (Hpk k (m + 1)) (V2 b) (V2 c) = 0 := by
    intro b c hb hc
    rcases V2_cases b hb with ⟨hbi, hv⟩ | ⟨hbi, hv⟩ <;> rcases V2_cases c hc with ⟨hci, hw⟩ | ⟨hci, hw⟩ <;> rw [hv, hw]
    · exact VpF_iso m i ν hν
    · exact VpF_esI m i ν hν _ (by intro h; apply hci; rw [← h])
    · rw [herm_swap, VpF_esI m i ν hν _ (by intro h; apply hbi; rw [← h]), star_zero]
    · exact bvec_esI_iso m _ _
  have V2_z : ∀ c, herm (Hpk k (m + 1)) z' (V2 c) = 0 := by
    intro c
    by_cases hc : c < m + 1
    · rcases V2_cases c hc with ⟨_, hv⟩ | ⟨_, hv⟩ <;> rw [hv]
      · exact hermitian_perturbed_vector_orthogonal m i ν z' hz hν hzν
      · rw [herm_bvec_esI]; exact hz _ (Or.inl (by simp only [eI]; omega))
    · rw [V2_0 c (by omega)]; simp [herm]
  have hn2 := one_add_projection_mem_isotropic_set (m + 1) z' hz V2 V2_0 V2_s V2_iso V2_z
  set n2 := 1 + NFOne.Pm k (m + 1) (m + 1) V2 with hn2def
  have hn2col : ∀ b : Fin (m + 1), n2 *ᵥ bvec (esI k (m + 1) b) = V2 b.val :=
    fun b => pm_col_star (m + 1) V2 V2_s b b.isLt

  have hn2yb : n2 *ᵥ yb = u := by
    rw [u_dec, hn2def, Matrix.add_mulVec, Matrix.one_mulVec]
    funext p
    rw [Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    by_cases hp : p.val < m + 1
    · have hterm : ∀ q, NFOne.Pm k (m + 1) (m + 1) V2 p q * yb q =
          if p.val = i.val then star (ν q) * (WeylGroupFacts.sgn k (m + 1) q * yb (WeylGroupFacts.tau k (m + 1) q)) else 0 := by
        intro q
        by_cases hW : m + 1 ≤ q.val ∧ q.val ≤ m + 1 + k
        · rw [NFOne.P_XW k (m + 1) (m + 1) V2 p q hp hW.1 hW.2, tau_W q hW]
          have hdW : NFOne.dW k (m + 1) q = WeylGroupFacts.sgn k (m + 1) q := rfl
          rcases V2_cases p.val hp with ⟨hpi, hv⟩ | ⟨hpi, hv⟩
          · rw [hv, if_pos hpi]
            unfold VpF
            have h1 : q ≠ esI k (m + 1) i := by intro h; rw [h] at hW; simp [esI] at hW; omega
            have h2 : q ≠ eI k (m + 1) i := by intro h; rw [h] at hW; simp [eI] at hW; omega
            simp only [bvec, Pi.single_apply, if_neg h1, if_neg h2, hdW]
            simp; ring
          · rw [hv, if_neg hpi]
            have h1 : q ≠ esI k (m + 1) ⟨p.val, hp⟩ := by intro h; rw [h] at hW; simp [esI] at hW; omega
            simp [bvec, Pi.single_apply, h1]
        · have h0 : yb q = 0 := hyb q (by omega)
          rw [h0, mul_zero]
          split_ifs
          · rw [hyb (WeylGroupFacts.tau k (m + 1) q) (tau_notW q hW)]; simp
          · rfl
      rw [Finset.sum_congr rfl (fun q _ => hterm q)]
      by_cases hpi : p.val = i.val
      · simp only [if_pos hpi]
        rw [← herm_expand, hybν]
        have : p = eI k (m + 1) i := by ext; simp [eI, hpi]
        simp [bvec, this]
      · have : p ≠ eI k (m + 1) i := by intro h; apply hpi; rw [h]; simp [eI]
        simp [hpi, bvec, Pi.single_apply, this]
    · have : p ≠ eI k (m + 1) i := by intro h; apply hp; rw [h]; simp only [eI]; omega
      rw [Finset.sum_eq_zero]
      · simp [bvec, Pi.single_apply, this]
      · intro q _
        by_cases hW : m + 1 ≤ q.val ∧ q.val ≤ m + 1 + k
        · rw [NFOne.P_rowWS_colW k (m + 1) (m + 1) V2 p q (by omega) hW.2, zero_mul]
        · rw [hyb q (by omega), mul_zero]

  set ystar : Fin (m + 1) → Fin (2 * (m + 1) + k + 1) → ℂ := fun a p => if m + 1 + k < p.val then y a p else 0 with hystar
  have hdec : ∀ a'' : Fin m, ystar (i.succAbove a'') =
      ∑ b : Fin m, Y' a'' b • bvec (esI k (m + 1) (i.succAbove b)) := by
    intro a''
    funext p
    simp only [ystar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply]
    by_cases hp : m + 1 + k < p.val
    · rw [if_pos hp]
      have hpv := p.isLt
      by_cases hpi : (NFOne.sg k (m + 1) p).val = i.val
      · have hpe : p = esI k (m + 1) i := by ext; rw [sg_val'] at hpi; simp [esI]; omega
        rw [hpe, hyi _ (Fin.succAbove_ne i a'')]
        symm; apply Finset.sum_eq_zero; intro b _
        rw [if_neg, mul_zero]
        intro h; have := congrArg Fin.val h; simp [esI] at this
        exact hsne b (by have := (i.succAbove b).isLt; omega)
      · have hc : (NFOne.sg k (m + 1) p).val < m + 1 ∧ (NFOne.sg k (m + 1) p).val ≠ i.val := ⟨by rw [sg_val']; omega, hpi⟩
        have hsb := succAbove_pidx m i _ hc
        have hsv : (NFOne.sg k (m + 1) p).val = 2 * (m + 1) + k - p.val := sg_val' m p
        have hpe : p = esI k (m + 1) (i.succAbove (pidx m i _ hc)) := by
          ext; show p.val = 2 * (m + 1) + k - (i.succAbove (pidx m i _ hc)).val; rw [hsb, hsv]; omega
        rw [Finset.sum_eq_single (pidx m i _ hc)]
        · rw [if_pos hpe, mul_one]; exact congrArg (y (i.succAbove a'')) hpe
        · intro b _ hb
          rw [if_neg, mul_zero]
          intro h; apply hb
          rw [hpe] at h
          have hv := congrArg Fin.val h
          simp only [esI] at hv
          have h2 : i.succAbove (pidx m i _ hc) = i.succAbove b := by
            ext; have h3 := (i.succAbove b).isLt; have h4 := (i.succAbove (pidx m i _ hc)).isLt; omega
          exact (Fin.succAbove_right_injective h2).symm
        · simp
    · rw [if_neg hp]
      symm; apply Finset.sum_eq_zero; intro b _
      rw [if_neg, mul_zero]
      intro h; apply hp; rw [h]; simp [esI]; have := (i.succAbove b).isLt; omega
  have hn1y : ∀ a'' : Fin m, n1 *ᵥ ystar (i.succAbove a'') = y (i.succAbove a'') := by
    intro a''
    rw [hdec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hn1col, hV1c, Vc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single a'']
    · have := congrFun (congrFun hYN a'') a''
      rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at this
      rw [this, one_smul]
    · intro a' _ ha'
      have := congrFun (congrFun hYN a'') a'
      rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm ha')] at this
      rw [this, zero_smul]
    · simp
  have hn2y : ∀ a'' : Fin m, n2 *ᵥ ystar (i.succAbove a'') = ystar (i.succAbove a'') := by
    intro a''
    rw [hdec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hn2col]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rcases V2_cases (i.succAbove b).val (i.succAbove b).isLt with ⟨hbi, _⟩ | ⟨_, hv⟩
    · exact absurd hbi (hsne b)
    · rw [hv]
  refine ⟨n1 * n2, mul_mem_isotropic_unipotent_set z' (m + 1) (m + 1) V1 V2 hn1 hn2, fun a => if a = i then yb else ystar a, fun a => ?_⟩
  by_cases ha : a = i
  · subst ha
    simp only [if_true]
    refine ⟨by rw [← Matrix.mulVec_mulVec, hn2yb, hnu], fun h => absurd rfl h, fun _ => ⟨hyb, yb_z⟩⟩
  · simp only [if_neg ha]
    obtain ⟨a'', rfl⟩ := Fin.exists_succAbove_eq ha
    refine ⟨by rw [← Matrix.mulVec_mulVec, hn2y, hn1y], fun _ => ⟨?_, ?_⟩, fun h => absurd h ha⟩
    · intro p hp; simp only [ystar]; rw [if_neg (by omega)]
    · intro p hp; simp only [ystar]; rw [if_pos hp]

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end
