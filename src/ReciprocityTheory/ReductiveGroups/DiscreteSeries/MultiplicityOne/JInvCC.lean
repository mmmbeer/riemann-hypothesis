import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, hpk_row, hpk_row]
  by_cases h : j = tau k r i
  · have h' : i = tau k r j := by rw [h, tau_tau]
    rw [if_pos h', if_pos h, h, sgn_tau]
    unfold sgn; split_ifs <;> simp
  · have h' : ¬ i = tau k r j := fun h' => h (by rw [h', tau_tau])
    rw [if_neg h', if_neg h, star_zero]

theorem isUnit_of_uh {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_mul {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩

lemma wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by
  have := hi
  apply Fin.ext
  simp only [wI, midx]
  omega

lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega

lemma wI_inj {a b : Fin (k + 1)} (h : wI k r a = wI k r b) : a = b := by
  have := congrArg Fin.val h
  simp only [wI] at this
  apply Fin.ext; omega

lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q)
    (hj : mid k r j) : embWb k r μ q j = μ (midx hq) (midx hj) := by
  unfold embWb
  rw [dif_pos ⟨hq, hj⟩]
  rfl

def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0

lemma Em_mul_mid {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hi)]
  · rw [Em, if_pos (wI_midx hi).symm, one_mul]
  · intro b _ hb
    rw [Em, if_neg, zero_mul]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hi, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X)
    (hi : ¬ mid k r i) : (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)

lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X)
    (hj : mid k r j) : (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hj)]
  · rw [Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hj, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X)
    (hj : ¬ mid k r j) : (A * (Em k r)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
  intro h
  exact hj (h ▸ mid_wI b)

lemma EmT_Em : (Em k r)ᵀ * Em k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]
  · simp only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]
  · intro i _ hi
    simp only [Matrix.transpose_apply, Em]
    rw [if_neg hi (c := i = wI k r a), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Em_conjT : (Em k r)ᴴ = (Em k r)ᵀ := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

lemma EmT_conjT : ((Em k r)ᵀ)ᴴ = Em k r := by
  rw [← Em_conjT, Matrix.conjTranspose_conjTranspose]

lemma emb_eq (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hj : mid k r j
  · rw [mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]
    by_cases hi : mid k r i
    · rw [Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero]
    · rw [Em_mul_out _ i _ hi, emb_out_row μ i j hi]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]
  · rw [mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]
    ring

lemma EmT_Q : (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]

lemma Q_Em : (1 - Em k r * (Em k r)ᵀ) * Em k r = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]

lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_eq, emb_eq]
  set E := Em k r with hE
  set Q := 1 - E * Eᵀ with hQ
  have t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ := by
    calc E * a * Eᵀ * M * (E * b * Eᵀ) = E * a * (Eᵀ * M) * E * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * E) * b * Eᵀ := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = E * (a * N * b) * Eᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have t2 : E * a * Eᵀ * M * Q = 0 := by
    calc E * a * Eᵀ * M * Q = E * a * (Eᵀ * M) * Q := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * Q) := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [EmT_Q, Matrix.mul_zero]
  have t3 : Q * M * (E * b * Eᵀ) = 0 := by
    calc Q * M * (E * b * Eᵀ) = Q * (M * E) * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = (Q * E) * N * b * Eᵀ := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Q_Em]; simp only [Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]

lemma emb_one : embWb k r 1 = 1 := by
  rw [emb_eq, Matrix.mul_one, add_sub_cancel]

lemma emb_conjT (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (embWb k r a)ᴴ = embWb k r aᴴ := by
  rw [emb_eq, emb_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, EmT_conjT, Em_conjT,
    Matrix.mul_assoc]

lemma Hb_conjT : (Hb k)ᴴ = Hb k := by
  unfold Hb
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : j = Fin.last k <;> simp [h]

lemma Hpk_Em : Hpk k r * Em k r = Em k r * Hb k := by
  ext i m
  have h1 : (Hpk k r * Em k r) i m = Hpk k r i (wI k r m) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r m)]
    · rw [Em, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Em, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have hm := m.isLt
  have hil := i.isLt
  by_cases hi : mid k r i
  · rw [Em_mul_mid _ i _ hi]
    have h0 := hi
    unfold Hpk Hb
    rw [Matrix.diagonal_apply]
    simp only [wI, midx, Fin.ext_iff, Fin.val_last]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [Em_mul_out _ i _ hi]
    unfold Hpk
    simp only [wI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma EmT_Hpk : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  have h := congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, hpk_conjT, Hb_conjT] at h
  exact h

lemma emb_form (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (embWb k r a)ᴴ * Hpk k r * embWb k r a =
      Em k r * (aᴴ * Hb k * a) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * Hpk k r * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_conjT]
  exact sandwich _ _ _ _ Hpk_Em EmT_Hpk

lemma emb_mem {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : aᴴ * Hb k * a = Hb k) : embWb k r a ∈ GV k r := by
  show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r
  have h1 := emb_form (k := k) (r := r) 1
  rw [emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one] at h1
  rw [emb_form, h, ← h1]

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section Alg

variable {k r : ℕ}

lemma lie_rsmul (t : ℝ) {X : Mat k r} (hX : inLie k r X) : inLie k r ((t : ℂ) • X) := by
  have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  show ((t : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((t : ℂ) • X) = 0
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [hs, ← smul_add, h, smul_zero]

lemma lie_neg {X : Mat k r} (hX : inLie k r X) : inLie k r (-X) := by
  have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

private lemma Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hpk_sq]

private lemma inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_GV hg)

private lemma Hpk_mul_conjTranspose_eq_neg_mul_Hpk_of_inLie {Y : Mat k r} (hY : inLie k r Y) : Hpk k r * Yᴴ = -(Y * Hpk k r) := by
  have h : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  have h1 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left h
  calc Hpk k r * Yᴴ = Hpk k r * Yᴴ * (Hpk k r * Hpk k r) := by rw [hpk_sq, Matrix.mul_one]
    _ = Hpk k r * (Yᴴ * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
    _ = -(Hpk k r * Hpk k r * Y * Hpk k r) := by
      rw [h1]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(Y * Hpk k r) := by rw [hpk_sq, Matrix.one_mul]

lemma lie_conj {P Y : Mat k r} (hP : P ∈ GV k r) (hY : inLie k r Y) : inLie k r (P * Y * P⁻¹) := by
  have key : ∀ Z : Mat k r, Hpk k r * (Yᴴ * Z) = -(Y * (Hpk k r * Z)) := by
    intro Z
    rw [← Matrix.mul_assoc, Hpk_mul_conjTranspose_eq_neg_mul_Hpk_of_inLie hY, Matrix.neg_mul, Matrix.mul_assoc]
  show (P * Y * P⁻¹)ᴴ * Hpk k r + Hpk k r * (P * Y * P⁻¹) = 0
  rw [inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV hP]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_conjT, Matrix.mul_assoc]
  rw [key]
  simp only [Matrix.mul_neg, neg_add_cancel]

private lemma Hpk_map_conj_eq : (Hpk k r).map (starRingEnd ℂ) = Hpk k r := by
  ext i j
  simp only [Matrix.map_apply, Hpk]
  split_ifs <;> simp

lemma lie_map_conj {Y : Mat k r} (hY : inLie k r Y) : inLie k r (Y.map (starRingEnd ℂ)) := by
  have h : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  show (Y.map (starRingEnd ℂ))ᴴ * Hpk k r + Hpk k r * Y.map (starRingEnd ℂ) = 0
  have e1 : (Y.map (starRingEnd ℂ))ᴴ = (Yᴴ).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e1]
  conv_lhs => rw [← Hpk_map_conj_eq (k := k) (r := r)]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  ext i j
  have hij : (Yᴴ * Hpk k r) i j + (Hpk k r * Y) i j = 0 := by
    rw [← Matrix.add_apply, h, Matrix.zero_apply]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.zero_apply, ← map_add, hij, map_zero]

private lemma mul_Hpk_conjTranspose_Hpk_eq_one_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g * (Hpk k r * gᴴ * Hpk k r) = 1 :=
  by
  rw [← inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV hg]
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_GV hg))

private lemma inv_mem_GV' {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  rw [inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV hg]
  show (Hpk k r * gᴴ * Hpk k r)ᴴ * Hpk k r * (Hpk k r * gᴴ * Hpk k r) = Hpk k r
  have h1 := mul_Hpk_conjTranspose_Hpk_eq_one_of_mem_GV hg
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_conjT, Matrix.mul_assoc] at h1 ⊢
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), hpk_sq, Matrix.one_mul, h1, Matrix.mul_one]

private lemma mul_mem_GV_multiplicity_one {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  have e1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have e2 : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e1, e2]

private lemma map_conj_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g.map (starRingEnd ℂ) ∈ GV k r := by
  have e1 : gᴴ * Hpk k r * g = Hpk k r := hg
  show (g.map (starRingEnd ℂ))ᴴ * Hpk k r * g.map (starRingEnd ℂ) = Hpk k r
  have e2 : (g.map (starRingEnd ℂ))ᴴ = (gᴴ).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e2]
  conv_lhs => rw [← Hpk_map_conj_eq (k := k) (r := r)]
  rw [← Matrix.map_mul, ← Matrix.map_mul, e1, Hpk_map_conj_eq]

lemma exp_mem {X : Mat k r} (hX : inLie k r X) : NormedSpace.exp X ∈ GV k r := by
  have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hXH : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [Matrix.inv_eq_left_inv hpk_sq]
    have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
      _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hpk_sq)
  have hc : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  rw [← Matrix.exp_conjTranspose, hXH, Matrix.exp_conj _ _ hU, Matrix.inv_eq_left_inv hpk_sq,
    Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-X)) (Hpk k r) (Hpk k r), hpk_sq, Matrix.mul_one,
    Matrix.mul_assoc, hc, Matrix.mul_one]

section gbar

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det)

private lemma conj_map_add (A B : Mat k r) :
    (A + B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) + B.map (starRingEnd ℂ) := by
  ext i j
  simp

private lemma conj_map_real_smul (t : ℝ) (A : Mat k r) :
    ((t : ℂ) • A).map (starRingEnd ℂ) = (t : ℂ) • A.map (starRingEnd ℂ) := by
  ext i j
  simp

private lemma conj_map_neg (A : Mat k r) : (-A).map (starRingEnd ℂ) = -A.map (starRingEnd ℂ) := by
  ext i j
  simp

private lemma conj_map_conj_map (A : Mat k r) : (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by
  ext i j
  simp

lemma gbar_add (A B : Mat k r) : gbar k r γ (A + B) = gbar k r γ A + gbar k r γ B := by
  simp only [gbar, Matrix.mul_add, Matrix.add_mul, conj_map_add]

lemma gbar_rsmul (t : ℝ) (A : Mat k r) : gbar k r γ ((t : ℂ) • A) = (t : ℂ) • gbar k r γ A := by
  simp only [gbar, Matrix.mul_smul, Matrix.smul_mul, conj_map_real_smul]

lemma gbar_neg (A : Mat k r) : gbar k r γ (-A) = -gbar k r γ A := by
  simp only [gbar, Matrix.mul_neg, Matrix.neg_mul, conj_map_neg]

lemma exp_map_conj (A : Mat k r) :
    NormedSpace.exp (A.map (starRingEnd ℂ)) = (NormedSpace.exp A).map (starRingEnd ℂ) := by
  have h : ∀ B : Mat k r, B.map (starRingEnd ℂ) = (Bᴴ)ᵀ := fun B => by ext i j; simp
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

include hE

lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  simp only [gbar]
  rw [show (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left, hE], Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left, hE]

lemma gbar_one : gbar k r γ 1 = 1 := by
  simp only [gbar, Matrix.mul_one, Matrix.nonsing_inv_mul _ hE]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.mul_nonsing_inv _ hE]

lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  simp only [gbar, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left,
    Matrix.nonsing_inv_mul, Matrix.mul_nonsing_inv, Matrix.mul_one, hE, conj_map_conj_map]

lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul hE, Matrix.mul_nonsing_inv _ hx, gbar_one hE]

lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ := (Matrix.inv_eq_right_inv (gbar_mul_inv hE hx)).symm

lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det := Matrix.isUnit_det_of_right_inverse (gbar_mul_inv hE hx)

lemma th_mul (g h : Mat k r) : th k r γ (g * h) = th k r γ h * th k r γ g := by
  simp only [th, gbar_mul hE, Matrix.mul_inv_rev]

lemma th_th {g : Mat k r} (hg : IsUnit g.det) : th k r γ (th k r γ g) = g := by
  simp only [th]
  rw [gbar_inv hE (gbar_unit hE hg), gbar_gbar hE, Matrix.nonsing_inv_nonsing_inv _ hg]

lemma gbar_exp (A : Mat k r) : gbar k r γ (NormedSpace.exp A) = NormedSpace.exp (gbar k r γ A) := by
  have hU : IsUnit (embWb k r γ) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  simp only [gbar]
  rw [← Matrix.exp_conj' _ A hU, ← exp_map_conj, Matrix.exp_conj _ _ hU]

lemma th_exp (A : Mat k r) : th k r γ (NormedSpace.exp A) = NormedSpace.exp (-(gbar k r γ A)) := by
  simp only [th]
  rw [gbar_exp hE, Matrix.exp_neg]

variable (hEG : embWb k r γ ∈ GV k r)
include hEG

lemma lie_gbar {X : Mat k r} (hX : inLie k r X) : inLie k r (gbar k r γ X) := by
  have hEi : (embWb k r γ)⁻¹ ∈ GV k r := inv_mem_GV' hEG
  have h1 : inLie k r ((embWb k r γ)⁻¹ * X * embWb k r γ) := by
    have h2 := lie_conj hEi hX
    rwa [Matrix.nonsing_inv_nonsing_inv _ hE] at h2
  exact lie_conj hEG (lie_map_conj h1)

lemma gbar_mem {g : Mat k r} (hg : g ∈ GV k r) : gbar k r γ g ∈ GV k r := mul_mem_GV_multiplicity_one (mul_mem_GV_multiplicity_one hEG (map_conj_mem_GV (mul_mem_GV_multiplicity_one (mul_mem_GV_multiplicity_one (inv_mem_GV' hEG) hg) hEG)))
    (inv_mem_GV' hEG)

lemma th_mem {g : Mat k r} (hg : g ∈ GV k r) : th k r γ g ∈ GV k r := inv_mem_GV' (gbar_mem hE hEG hg)

lemma th_eq {g : Mat k r} (hg : g ∈ GV k r) : th k r γ g = Hpk k r * (gbar k r γ g)ᴴ * Hpk k r := inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV (gbar_mem hE hEG hg)

end gbar

end Alg

open Formalism.REAL
open Filter Topology
open scoped ContDiff

section Linfty

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra Matrix.linftyOpNormedSpace

lemma hasDerivAt_exp_linfty {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end Linfty

lemma slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_exp_linfty X).tendsto_slope

lemma slope_curveR {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
  have hm : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => g * M) := continuous_const.mul continuous_id
  refine ((hm.tendsto X).comp (slope_exp X)).congr' ?_
  filter_upwards with t
  simp only [Function.comp_apply, slope_def_module, Matrix.mul_sub, Matrix.mul_smul]

lemma slope_curveL {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) 0) (𝓝[≠] 0) (𝓝 (-(X * g))) := by
  have h := (slope_exp (-X)).mul_const g
  rw [Matrix.neg_mul] at h
  refine h.congr (fun t => ?_)
  simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul, smul_neg]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hasDerivAt_curveR (g X : Mat k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := hasDerivAt_iff_tendsto_slope.mpr (slope_curveR g X)

lemma hasDerivAt_curveL (g X : Mat k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) (-(X * g)) 0 := hasDerivAt_iff_tendsto_slope.mpr (slope_curveL g X)

def mulR (X : Mat k r) : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (X : Mat k r) : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

lemma expL_mem {X : Mat k r} (hX : inLie k r X) (t : ℝ) {g : Mat k r} (hg : g ∈ GV k r) :
    NormedSpace.exp (-((t : ℂ) • X)) * g ∈ GV k r := by
  have h1 : inLie k r (-((t : ℂ) • X)) := lie_neg (lie_rsmul t hX)
  exact mul_mem_GV_multiplicity_one (exp_mem h1) hg

lemma expR_mem {X : Mat k r} (hX : inLie k r X) (t : ℝ) {g : Mat k r} (hg : g ∈ GV k r) :
    g * NormedSpace.exp ((t : ℂ) • X) ∈ GV k r := mul_mem_GV_multiplicity_one hg (exp_mem (lie_rsmul t hX))

lemma LdV_congr {f₁ f₂ : Mat k r → ℂ} (h : ∀ g ∈ GV k r, f₁ g = f₂ g) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hg : g ∈ GV k r) : LdV X f₁ g = LdV X f₂ g := by
  show deriv (fun t : ℝ => f₁ (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 =
    deriv (fun t : ℝ => f₂ (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0
  congr 1
  funext t
  exact h _ (expL_mem hX t hg)

lemma RdV_congr {f₁ f₂ : Mat k r → ℂ} (h : ∀ g ∈ GV k r, f₁ g = f₂ g) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hg : g ∈ GV k r) : RdV X f₁ g = RdV X f₂ g := by
  show deriv (fun t : ℝ => f₁ (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (g * NormedSpace.exp ((t : ℂ) • X))) 0
  congr 1
  funext t
  exact h _ (expR_mem hX t hg)

lemma LdV_eq {f f' : Mat k r → ℂ} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g) (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h)
    {X : Mat k r} (hX : inLie k r X) : LdV X f g = fderiv ℝ f' g (-(X * g)) := by
  have hc := hasDerivAt_curveL g X
  have hc0 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • X)) * g = g := by simp
  have hd' : DifferentiableAt ℝ f' (NormedSpace.exp (-(((0 : ℝ) : ℂ) • X)) * g) := by rw [hc0]; exact hd
  have hcomp := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hev : (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =ᶠ[𝓝 0]
      (f' ∘ fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) := by
    have hU' : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), NormedSpace.exp (-((t : ℂ) • X)) * g ∈ U :=
      hc.continuousAt.preimage_mem_nhds (by
        simp only [Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul]
        exact hU.mem_nhds hgU)
    filter_upwards [hU'] with t ht
    exact hff _ ht (expL_mem hX t hg)
  show deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
  rw [hev.deriv_eq, hcomp.deriv, hc0]
  rfl

lemma RdV_eq {f f' : Mat k r → ℂ} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g) (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h)
    {X : Mat k r} (hX : inLie k r X) : RdV X f g = fderiv ℝ f' g (g * X) := by
  have hc := hasDerivAt_curveR g X
  have hc0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd' : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by rw [hc0]; exact hd
  have hcomp := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (f' ∘ fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := by
    have hU' : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hc.continuousAt.preimage_mem_nhds (by
        simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
        exact hU.mem_nhds hgU)
    filter_upwards [hU'] with t ht
    exact hff _ ht (expR_mem hX t hg)
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hev.deriv_eq, hcomp.deriv, hc0]
  rfl

lemma cast_succ_le (m : ℕ) : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
  norm_cast

lemma one_le_cast_succ (m : ℕ) : (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero m

lemma CkOn_mono {m m' : ℕ} (h : m' ≤ m) {f : Mat k r → ℂ} (hf : CkOn (m : ℕ∞) (GV k r) f) :
    CkOn (m' : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast h), hff⟩

lemma CkOn_LdV {m : ℕ} {f : Mat k r → ℂ} (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) {X : Mat k r}
    (hX : inLie k r X) : CkOn (m : ℕ∞) (GV k r) (LdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, h0, hc, he⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (-(mulL X h)), hU, h0, ?_, ?_⟩
  · have h1 := hc.fderiv_of_isOpen hU (cast_succ_le m)
    have h2 : ContDiffOn ℝ ((m : ℕ∞) : WithTop ℕ∞) (fun h : Mat k r => -(mulL X h)) U :=
      (mulL X).contDiff.neg.contDiffOn
    exact h1.clm_apply h2
  · intro h hh hG
    exact LdV_eq hU hh hG ((hc.differentiableOn (one_le_cast_succ m)).differentiableAt (hU.mem_nhds hh)) he hX

lemma CkOn_RdV {m : ℕ} {f : Mat k r → ℂ} (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) {X : Mat k r}
    (hX : inLie k r X) : CkOn (m : ℕ∞) (GV k r) (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, h0, hc, he⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (mulR X h), hU, h0, ?_, ?_⟩
  · have h1 := hc.fderiv_of_isOpen hU (cast_succ_le m)
    have h2 : ContDiffOn ℝ ((m : ℕ∞) : WithTop ℕ∞) (fun h : Mat k r => mulR X h) U :=
      (mulR X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro h hh hG
    exact RdV_eq hU hh hG ((hc.differentiableOn (one_le_cast_succ m)).differentiableAt (hU.mem_nhds hh)) he hX

lemma LR_comm {f : Mat k r → ℂ} (hf : CkOn ((2 : ℕ) : ℕ∞) (GV k r) f) {X Y : Mat k r} (hX : inLie k r X)
    (hY : inLie k r Y) {g : Mat k r} (hg : g ∈ GV k r) : LdV X (RdV Y f) g = RdV Y (LdV X f) g := by
  obtain ⟨U, f', hU, h0, hc, he⟩ := hf g hg
  have hd1 : ∀ h ∈ U, DifferentiableAt ℝ f' h := fun h hh =>
    (hc.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hh)
  have hc1 := hc.fderiv_of_isOpen (m := 1) hU (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f') g :=
    (hc1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds h0)
  have eφ : ∀ h ∈ U, h ∈ GV k r → RdV Y f h = (fun h => fderiv ℝ f' h (h * Y)) h :=
    fun h hh hG => RdV_eq hU hh hG (hd1 h hh) he hY
  have eψ : ∀ h ∈ U, h ∈ GV k r → LdV X f h = (fun h => fderiv ℝ f' h (-(X * h))) h :=
    fun h hh hG => LdV_eq hU hh hG (hd1 h hh) he hX
  have Dφ : DifferentiableAt ℝ (fun h => fderiv ℝ f' h (h * Y)) g :=
    (hd2.hasFDerivAt.clm_apply (mulR Y).hasFDerivAt).differentiableAt
  have Dψ : DifferentiableAt ℝ (fun h => fderiv ℝ f' h (-(X * h))) g :=
    (hd2.hasFDerivAt.clm_apply (mulL X).hasFDerivAt.neg).differentiableAt
  have hdφ : ∀ W, fderiv ℝ (fun h => fderiv ℝ f' h (h * Y)) g W =
      fderiv ℝ (fderiv ℝ f') g W (g * Y) + fderiv ℝ f' g (W * Y) := by
    intro W
    have H := (hd2.hasFDerivAt.clm_apply (mulR Y).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have hdψ : ∀ W, fderiv ℝ (fun h => fderiv ℝ f' h (-(X * h))) g W =
      fderiv ℝ (fderiv ℝ f') g W (-(X * g)) + fderiv ℝ f' g (-(X * W)) := by
    intro W
    have H := (hd2.hasFDerivAt.clm_apply (mulL X).hasFDerivAt.neg).fderiv
    erw [H]
    exact add_comm _ _
  have hs : IsSymmSndFDerivAt ℝ f' g := (hc.contDiffAt (hU.mem_nhds h0)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  rw [LdV_eq hU h0 hg Dφ eφ hX, RdV_eq hU h0 hg Dψ eψ hY, hdφ, hdψ,
    show -(X * g) * Y = -(X * (g * Y)) by rw [Matrix.neg_mul, Matrix.mul_assoc]]
  erw [hs (-(X * g)) (g * Y)]
  exact rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC
end
end

section
noncomputable section

open Matrix
open scoped ContDiff ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma CkOn_Lw (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X) (m : ℕ) {f : Mat k r → ℂ}
    (hf : CkOn ((m + q.length : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (q.foldr LdV f) := by
  induction q generalizing m with
  | nil => simpa using hf
  | cons X q ih =>
    rw [List.foldr_cons]
    have hq' : ∀ Y ∈ q, inLie k r Y := fun Y hY => hq Y (List.mem_cons_of_mem X hY)
    have h1 : CkOn ((m + 1 + q.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : m + 1 + q.length = m + (X :: q).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact CkOn_LdV (ih hq' (m + 1) h1) (hq X (by simp))

lemma CkOn_Rw (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X) (m : ℕ) {f : Mat k r → ℂ}
    (hf : CkOn ((m + q.length : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (q.foldr RdV f) := by
  induction q generalizing m with
  | nil => simpa using hf
  | cons X q ih =>
    rw [List.foldr_cons]
    have hq' : ∀ Y ∈ q, inLie k r Y := fun Y hY => hq Y (List.mem_cons_of_mem X hY)
    have h1 : CkOn ((m + 1 + q.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : m + 1 + q.length = m + (X :: q).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact CkOn_RdV (ih hq' (m + 1) h1) (hq X (by simp))


lemma comm1 (Y : Mat k r) (hY : inLie k r Y) (q : List (Mat k r)) (hq : ∀ X ∈ q, inLie k r X)
    (f : Mat k r → ℂ) (hf : CkOn ((q.length + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, RdV Y (q.foldr LdV f) g = q.foldr LdV (RdV Y f) g := by
  induction q with
  | nil => intro g _; rfl
  | cons X q ih =>
    intro g hg
    rw [List.foldr_cons, List.foldr_cons]
    have hq' : ∀ Z ∈ q, inLie k r Z := fun Z hZ => hq Z (List.mem_cons_of_mem X hZ)
    have h2 : CkOn ((2 : ℕ) : ℕ∞) (GV k r) (q.foldr LdV f) := by
      apply CkOn_Lw q hq' 2
      have e : 2 + q.length = (X :: q).length + 1 := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    rw [← LR_comm h2 (hq X (by simp)) hY hg]
    exact LdV_congr (ih hq' (CkOn_mono (by simp only [List.length_cons]; omega) hf)) (hq X (by simp)) hg

lemma comm (p q : List (Mat k r)) (hp : ∀ X ∈ p, inLie k r X) (hq : ∀ X ∈ q, inLie k r X)
    (f : Mat k r → ℂ) (hf : CkOn ((p.length + q.length : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, p.foldr RdV (q.foldr LdV f) g = q.foldr LdV (p.foldr RdV f) g := by
  induction p with
  | nil => intro g _; rfl
  | cons Y p ih =>
    intro g hg
    rw [List.foldr_cons, List.foldr_cons]
    have hp' : ∀ Z ∈ p, inLie k r Z := fun Z hZ => hp Z (List.mem_cons_of_mem Y hZ)
    rw [RdV_congr (ih hp' (CkOn_mono (by simp only [List.length_cons]; omega) hf)) (hp Y (by simp)) hg]
    apply comm1 Y (hp Y (by simp)) q hq (p.foldr RdV f) _ g hg
    apply CkOn_Rw p hp' (q.length + 1)
    have e : q.length + 1 + p.length = (Y :: p).length + q.length := by simp only [List.length_cons]; omega
    rw [e]; exact hf

lemma LdV_rsmul (c : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : LdV ((c : ℂ) • X) f = c • LdV X f := by
  funext g
  simp only [LdV, Pi.smul_apply]
  have e : (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • ((c : ℂ) • X))) * g)) =
      fun t => (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X)) * g)) (c * t) := by
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm]
  rw [e]
  exact (deriv_comp_mul_left c (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X)) * g)) 0).trans
    (by rw [mul_zero])

lemma RdV_rsmul (c : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : RdV ((c : ℂ) • X) f = c • RdV X f := by
  funext g
  simp only [RdV, Pi.smul_apply]
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • ((c : ℂ) • X)))) =
      fun t => (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (c * t) := by
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm]
  rw [e]
  exact (deriv_comp_mul_left c (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) 0).trans
    (by rw [mul_zero])

lemma LdV_fsmul (a : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : LdV X (a • f) = a • LdV X f := by
  funext g
  simp only [LdV, Pi.smul_apply]
  exact deriv_const_smul_field (f := fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) a

lemma RdV_fsmul (a : ℝ) (X : Mat k r) (f : Mat k r → ℂ) : RdV X (a • f) = a • RdV X f := by
  funext g
  simp only [RdV, Pi.smul_apply]
  exact deriv_const_smul_field (f := fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) a


lemma Rw_fsmul (a : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) : q.foldr RdV (a • f) = a • q.foldr RdV f := by
  induction q with
  | nil => rfl
  | cons X q ih => simp only [List.foldr_cons, ih, RdV_fsmul]

lemma Lw_scale (c : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) :
    (q.map (fun X => (c : ℂ) • X)).foldr LdV f = c ^ q.length • q.foldr LdV f := by
  induction q with
  | nil => simp
  | cons X q ih =>
    simp only [List.map_cons, List.foldr_cons, ih, LdV_rsmul, LdV_fsmul, List.length_cons, smul_smul,
      pow_succ']
    rw [mul_comm (c ^ q.length) c]

lemma Rw_scale (c : ℝ) (q : List (Mat k r)) (f : Mat k r → ℂ) :
    (q.map (fun X => (c : ℂ) • X)).foldr RdV f = c ^ q.length • q.foldr RdV f := by
  induction q with
  | nil => simp
  | cons X q ih =>
    simp only [List.map_cons, List.foldr_cons, ih, RdV_rsmul, RdV_fsmul, List.length_cons, smul_smul,
      pow_succ']
    rw [mul_comm (c ^ q.length) c]

section th

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det)
include hE

lemma LdV_th (f : Mat k r → ℂ) (X : Mat k r) : LdV X (f ∘ th k r γ) = RdV (gbar k r γ X) f ∘ th k r γ := by
  funext g
  simp only [Function.comp]
  unfold LdV RdV
  congr 1
  funext t
  rw [Function.comp_apply, th_mul hE, th_exp hE, gbar_neg, gbar_rsmul, neg_neg]

lemma RdV_th (f : Mat k r → ℂ) (X : Mat k r) : RdV X (f ∘ th k r γ) = LdV (gbar k r γ X) f ∘ th k r γ := by
  funext g
  simp only [Function.comp]
  unfold LdV RdV
  congr 1
  funext t
  rw [Function.comp_apply, th_mul hE, th_exp hE, gbar_rsmul]

lemma Rw_th (v : List (Mat k r)) (f : Mat k r → ℂ) :
    v.foldr RdV (f ∘ th k r γ) = (v.map (gbar k r γ)).foldr LdV f ∘ th k r γ := by
  induction v with
  | nil => rfl
  | cons X v ih => rw [List.foldr_cons, ih, RdV_th hE, List.map_cons, List.foldr_cons]

lemma Lw_th (u : List (Mat k r)) (f : Mat k r → ℂ) :
    u.foldr LdV (f ∘ th k r γ) = (u.map (gbar k r γ)).foldr RdV f ∘ th k r γ := by
  induction u with
  | nil => rfl
  | cons X u ih => rw [List.foldr_cons, ih, LdV_th hE, List.map_cons, List.foldr_cons]

end th

lemma norm_le_gN (A : Mat k r) : ‖A‖ ≤ gN A := by
  rw [Matrix.norm_le_iff (by unfold gN; exact Real.sqrt_nonneg _)]
  intro i j
  unfold gN
  calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := by
      apply Real.sqrt_le_sqrt
      rw [← Complex.normSq_eq_norm_sq]
      exact (Finset.single_le_sum (f := fun j => Complex.normSq (A i j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (A i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))

lemma gN_le_norm (A : Mat k r) : gN A ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖ := by
  unfold gN
  have hN : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖ := by positivity
  rw [← Real.sqrt_sq hN]
  apply Real.sqrt_le_sqrt
  have hij : ∀ i j, Complex.normSq (A i j) ≤ ‖A‖ ^ 2 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.norm_entry_le_entrywise_sup_norm A) 2
  calc ∑ i, ∑ j, Complex.normSq (A i j)
      ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), ‖A‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * ‖A‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma gN_nonneg (A : Mat k r) : 0 ≤ gN A := by
  unfold gN
  exact Real.sqrt_nonneg _

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  have hne : g ≠ 0 := by
    rintro rfl
    have h := isUnit_of_uh hg
    rw [Matrix.det_zero] at h
    exact not_isUnit_zero h
  exact lt_of_lt_of_le (norm_pos_iff.mpr hne) (norm_le_gN g)

lemma lin_bound (T : Mat k r →ₗ[ℝ] Mat k r) : ∃ C, ∀ z, ‖T z‖ ≤ C * ‖z‖ := by
  obtain ⟨C, -, hC⟩ := (LinearMap.toContinuousLinearMap T).isBoundedLinearMap.bound
  exact ⟨C, fun z => hC z⟩

lemma rpow_cmp {x y C A : ℝ} (hx : 0 < x) (hy : 0 < y) (hC : 1 ≤ C) (h1 : x ≤ C * y) (h2 : y ≤ C * x) :
    x ^ A ≤ C ^ |A| * y ^ A := by
  have hC0 : 0 < C := by linarith
  rcases le_or_gt 0 A with hA | hA
  · rw [abs_of_nonneg hA, ← Real.mul_rpow hC0.le hy.le]
    exact Real.rpow_le_rpow hx.le h1 hA
  · rw [abs_of_neg hA]
    have h3 : y / C ≤ x := by
      rw [div_le_iff₀ hC0]
      linarith
    have hpos : 0 < (y / C) ^ (-A) := Real.rpow_pos_of_pos (div_pos hy hC0) _
    have key : (y / C) ^ (-A) ≤ x ^ (-A) := Real.rpow_le_rpow (div_pos hy hC0).le h3 (by linarith)
    calc x ^ A = (x ^ (-A))⁻¹ := by rw [← Real.rpow_neg hx.le, neg_neg]
      _ ≤ ((y / C) ^ (-A))⁻¹ := inv_anti₀ hpos key
      _ = C ^ (-A) * y ^ A := by
        rw [← Real.rpow_neg (div_pos hy hC0).le, neg_neg, Real.div_rpow hy.le hC0.le,
          Real.rpow_neg hC0.le]
        ring

def gbarL (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r →ₗ[ℝ] Mat k r where
  toFun := gbar k r γ
  map_add' := gbar_add
  map_smul' := by
    intro c A
    have e1 : c • A = (c : ℂ) • A := (Complex.coe_smul c A).symm
    rw [RingHom.id_apply, e1, gbar_rsmul, Complex.coe_smul]

def TL (k r : ℕ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r →ₗ[ℝ] Mat k r where
  toFun A := Hpk k r * (gbar k r γ A)ᴴ * Hpk k r
  map_add' := by
    intro A B
    show Hpk k r * (gbar k r γ (A + B))ᴴ * Hpk k r =
      Hpk k r * (gbar k r γ A)ᴴ * Hpk k r + Hpk k r * (gbar k r γ B)ᴴ * Hpk k r
    rw [gbar_add, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c A
    show Hpk k r * (gbar k r γ (c • A))ᴴ * Hpk k r = c • (Hpk k r * (gbar k r γ A)ᴴ * Hpk k r)
    have e1 : c • A = (c : ℂ) • A := (Complex.coe_smul c A).symm
    rw [e1, gbar_rsmul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.mul_smul,
      Matrix.smul_mul, Complex.coe_smul]

lemma TL_apply (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (A : Mat k r) :
    TL k r γ A = Hpk k r * (gbar k r γ A)ᴴ * Hpk k r := rfl

section main

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det) (hEG : embWb k r γ ∈ GV k r)
include hE hEG

lemma th_bound : ∃ C, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g := by
  obtain ⟨C, hC⟩ := lin_bound (TL k r γ)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * max C 0, fun g hg => ?_⟩
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  rw [th_eq hE hEG hg]
  calc gN (Hpk k r * (gbar k r γ g)ᴴ * Hpk k r) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖TL k r γ g‖ := gN_le_norm _
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (max C 0 * ‖g‖) :=
        mul_le_mul_of_nonneg_left ((hC g).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) hn
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (max C 0 * gN g) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_le_gN g) (le_max_right _ _)) hn
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * max C 0 * gN g := by ring

lemma CkOn_th {m : ℕ} {F : Mat k r → ℂ} (hF : CkOn (m : ℕ∞) (GV k r) F) :
    CkOn (m : ℕ∞) (GV k r) (F ∘ th k r γ) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, h0, hc, he⟩ := hF (th k r γ g₀) (th_mem hE hEG hg₀)
  have hT : Continuous (TL k r γ) := (TL k r γ).continuous_of_finiteDimensional
  refine ⟨(TL k r γ) ⁻¹' U, f' ∘ (TL k r γ), hU.preimage hT, ?_, ?_, ?_⟩
  · show TL k r γ g₀ ∈ U
    rw [TL_apply, ← th_eq hE hEG hg₀]
    exact h0
  · exact hc.comp ((LinearMap.toContinuousLinearMap (TL k r γ)).contDiff).contDiffOn (Set.mapsTo_preimage _ _)
  · intro g hgU hgG
    show F (th k r γ g) = f' (TL k r γ g)
    rw [TL_apply, ← th_eq hE hEG hgG]
    exact he _ (by rw [th_eq hE hEG hgG]; exact hgU) (th_mem hE hEG hgG)

end main

theorem main (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hγ : IsZFrame k r z γ) :
    (∃ C : ℝ, ∀ g ∈ GV k r, gN (th k r γ g) ≤ C * gN g) ∧
    ∀ (A : ℝ) (m : ℕ) (F : Mat k r → ℂ), InCC A m F → InCC A m (F ∘ th k r γ) := by
  have hEG : embWb k r γ ∈ GV k r := emb_mem hγ.1
  have hE : IsUnit (embWb k r γ).det := isUnit_of_uh hEG
  refine ⟨th_bound hE hEG, ?_⟩
  rintro A m F ⟨c, hCk, hb⟩
  obtain ⟨C0, hC0⟩ := th_bound hE hEG
  obtain ⟨B, hB⟩ := lin_bound (gbarL k r γ)
  set C := max C0 1 with hCdef
  set M := max B 1 with hMdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hC0' : 0 < C := by linarith
  set Yb : Mat k r → Mat k r := fun X => ((M⁻¹ : ℝ) : ℂ) • gbar k r γ X with hYb
  have hgb : ∀ X, gbar k r γ X = ((M : ℝ) : ℂ) • Yb X := by
    intro X
    simp only [hYb, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hM0.ne', Complex.ofReal_one, one_smul]
  have hunit : ∀ X, unitLie k r X → unitLie k r (Yb X) := by
    intro X hX
    refine ⟨lie_rsmul _ (lie_gbar hE hEG hX.1), fun i j => ?_⟩
    have hXn : ‖X‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).mpr hX.2
    have h1 : ‖gbar k r γ X‖ ≤ M := by
      have := hB X
      calc ‖gbar k r γ X‖ = ‖gbarL k r γ X‖ := rfl
        _ ≤ B * ‖X‖ := this
        _ ≤ M * 1 := mul_le_mul (le_max_left _ _) hXn (norm_nonneg _) hM0.le
        _ = M := mul_one M
    simp only [hYb, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM0)]
    calc M⁻¹ * ‖gbar k r γ X i j‖ ≤ M⁻¹ * M :=
          mul_le_mul_of_nonneg_left ((Matrix.norm_entry_le_entrywise_sup_norm _).trans h1) (inv_pos.mpr hM0).le
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  refine ⟨M ^ m * C ^ |A| * max c 0, CkOn_th hE hEG hCk, ?_⟩
  intro u v hu hv hlen g hg
  have hthg := th_mem hE hEG hg
  have huY : ∀ X ∈ u.map Yb, unitLie k r X := by
    intro X hX; obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX; exact hunit Y (hu Y hY)
  have hvY : ∀ X ∈ v.map Yb, unitLie k r X := by
    intro X hX; obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX; exact hunit Y (hv Y hY)
  have eu : u.map (gbar k r γ) = (u.map Yb).map (fun X => ((M : ℝ) : ℂ) • X) := by
    rw [List.map_map]; exact List.map_congr_left (fun X _ => hgb X)
  have ev : v.map (gbar k r γ) = (v.map Yb).map (fun X => ((M : ℝ) : ℂ) • X) := by
    rw [List.map_map]; exact List.map_congr_left (fun X _ => hgb X)
  have hFk : CkOn (((u.map Yb).length + (v.map Yb).length : ℕ) : ℕ∞) (GV k r) F :=
    CkOn_mono (by simp only [List.length_map]; omega) hCk
  have key : dLR u v (F ∘ th k r γ) g =
      (M ^ (u.length + v.length) : ℝ) • dLR (v.map Yb) (u.map Yb) F (th k r γ g) := by
    unfold dLR Rw
    rw [Rw_th hE, Lw_th hE, eu, ev, Rw_scale, Lw_scale, Rw_fsmul, smul_smul, Function.comp_apply,
      Pi.smul_apply, comm _ _ (fun X hX => (huY X hX).1) (fun X hX => (hvY X hX).1) F hFk _ hthg,
      List.length_map, List.length_map, pow_add]
  have hD := hb (v.map Yb) (u.map Yb) hvY huY (by simp only [List.length_map]; omega) _ hthg
  have h2 : gN (th k r γ g) ≤ C * gN g :=
    (hC0 g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gN_nonneg g))
  have h1 : gN g ≤ C * gN (th k r γ g) := by
    have h := hC0 _ hthg
    rw [th_th hE (isUnit_of_uh hg)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gN_nonneg _))
  have hcmp := rpow_cmp (A := A) (gN_pos hg) (gN_pos hthg) hC1 h1 h2
  have hMp : (0 : ℝ) ≤ M ^ (u.length + v.length) := pow_nonneg hM0.le _
  have hCA : (0 : ℝ) ≤ C ^ |A| := Real.rpow_nonneg hC0'.le _
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg hMp]
  calc gN g ^ A * (M ^ (u.length + v.length) * ‖dLR (v.map Yb) (u.map Yb) F (th k r γ g)‖)
      ≤ (C ^ |A| * gN (th k r γ g) ^ A) * (M ^ (u.length + v.length) *
          ‖dLR (v.map Yb) (u.map Yb) F (th k r γ g)‖) :=
        mul_le_mul_of_nonneg_right hcmp (mul_nonneg hMp (norm_nonneg _))
    _ = M ^ (u.length + v.length) * C ^ |A| *
          (gN (th k r γ g) ^ A * ‖dLR (v.map Yb) (u.map Yb) F (th k r γ g)‖) := by ring
    _ ≤ M ^ (u.length + v.length) * C ^ |A| * max c 0 :=
        mul_le_mul_of_nonneg_left (hD.trans (le_max_left _ _)) (mul_nonneg hMp hCA)
    _ ≤ M ^ m * C ^ |A| * max c 0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hlen) hCA)
          (le_max_right _ _)

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stInvCC : StInvCC := by
  intro k r Wp _ _ _ D X _ _ γ hγ
  exact InvCC.main k r D.z γ hγ

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
