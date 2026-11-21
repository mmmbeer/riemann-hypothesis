import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

section
noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sg; split_ifs <;> rfl

theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [← sg_val, Fin.ext_iff]
  unfold Hpk
  simp only [key, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (k r : ℕ) (w : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ w) i = (if i.val = r + k then -1 else 1) * w (sg k r i) := by
  simp [mulVec, dotProduct, hpk_apply]

theorem star_hpk_dot (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ w) = star u ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, hpk_mulVec]
  calc ∑ i, star ((if i.val = r + k then -1 else 1 : ℂ) * u (sg k r i)) * ((if i.val = r + k then -1 else 1) * w (sg k r i))
      = ∑ i, star (u (sg k r i)) * w (sg k r i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = ∑ i, star (u i) * w i :=
        Fintype.sum_equiv (Function.Involutive.toPerm _ (sg_sg k r)) _ _ (fun i => rfl)

abbrev cc : ℂ := ((Real.sqrt 2)⁻¹ : ℂ)

theorem cc_sq : cc * cc = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h'; rw [h', zero_pow two_ne_zero] at h; norm_num at h
  simp only [cc]; field_simp; rw [h]

def aF (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (eI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) - y (wI k r (Fin.last k)))

def aF' (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (esI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) + y (wI k r (Fin.last k)))

theorem levPos_inj (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro i j h; simp only [levPos, Fin.ext_iff] at h; exact Fin.ext (by omega)

theorem lift_levPos (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (levPos k 1 r' i) = v i := by
  unfold liftVec; rw [dif_pos (by simp only [levPos]; omega)]; congr 1

theorem lift_zero (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p ∉ Set.range (levPos k 1 r')) : liftVec k 1 r' v p = 0 := by
  simp only [liftVec]; rw [dif_neg]; rintro ⟨h1, h2⟩
  exact hp ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩

theorem lift_dot (k r' : ℕ) (u v : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' u) ⬝ᵥ liftVec k 1 r' v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply]
  symm
  refine Fintype.sum_of_injective _ (levPos_inj k r') _ _ (fun p hp => ?_) (fun i => ?_)
  · rw [lift_zero _ _ v _ hp, mul_zero]
  · rw [lift_levPos, lift_levPos]

theorem gram_det (m : ℕ) (Mx : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (x a : ℕ → ℂ)
    (h00 : Mx 0 0 = 1 + c) (h0j : ∀ j : Fin m, Mx 0 j.succ = star (x j))
    (hj0 : ∀ j : Fin m, Mx j.succ 0 = x j)
    (hij : ∀ i j : Fin m, Mx i.succ j.succ = (if i = j then 1 else 0) + a i * star (a j)) :
    Mx.det = (1 + c - ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (a j) * a j) +
      (∑ j ∈ Finset.range m, star (x j) * a j) * (∑ j ∈ Finset.range m, star (a j) * x j) := by
  let al : Fin (m + 1) → ℂ := Fin.cases 1 (fun _ => 0)
  let xh : Fin (m + 1) → ℂ := Fin.cases 0 (fun j => x j)
  let ah : Fin (m + 1) → ℂ := Fin.cases 0 (fun j => a j)
  let U : Matrix (Fin (m + 1)) (Fin 3) ℂ := Matrix.of fun i q => ![al i, xh i, ah i] q
  let V : Matrix (Fin 3) (Fin (m + 1)) ℂ := Matrix.of fun q j => ![c * al j + star (xh j), al j, star (ah j)] q
  have hM : Mx = 1 + U * V := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [h00, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [h0j, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
    · simp [hj0, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
    · simp [hij, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.succ_inj]
  rw [hM, det_one_add_mul_comm, det_fin_three]
  simp only [← Fin.sum_univ_eq_sum_range]
  simp [U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  ring

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

theorem hpk_es (k r : ℕ) (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  ext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem Hpk_mulVec_apply_eq_ite (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ y) v = if (v : ℕ) < r ∨ r + k < (v : ℕ) then y ⟨2 * r + k - v, by omega⟩
      else if (v : ℕ) = r + k then -y v else y v := by
  have hv := v.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h1 : (v : ℕ) < r ∨ r + k < (v : ℕ)
  · rw [if_pos h1, Finset.sum_eq_single ⟨2 * r + k - v, by omega⟩]
    · rcases h1 with h1 | h1
      · simp only [Hpk, Fin.val_mk]
        rw [if_pos ⟨h1, by omega⟩, one_mul]
      · simp only [Hpk, Fin.val_mk]
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 2 * r + k - v := fun e => hj (Fin.ext e)
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (fun hc => by have := hc.1; have := hc.2.1; omega),
        zero_mul]
    · simp
  · rw [if_neg h1, Finset.sum_eq_single v]
    · simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, by trivial⟩]
      by_cases h2 : (v : ℕ) = r + k
      · rw [if_pos h2, if_pos h2, neg_one_mul]
      · rw [if_neg h2, if_neg h2, one_mul]
    · intro j _ hj
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (fun hc => by have := hc.1; have := hc.2; omega),
        if_neg (fun hc => hj hc.2.2.symm), zero_mul]
    · simp

theorem herm_symm (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u w = star (herm (Hpk k r) w u) := by
  have hsym : ∀ i j, Hpk k r i j = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hstar : ∀ i j, star (Hpk k r i j) = Hpk k r i j := by
    intro i j
    simp only [Hpk]
    split_ifs <;> simp
  simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hstar,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym]
  ring

theorem lift_kills_first_basis (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (eI k (1 + r') (a0 r')) = 0 := by
  unfold liftVec
  rw [dif_neg (by simp only [eI, a0, Fin.val_mk]; omega)]

theorem lift_kills_last_basis (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (esI k (1 + r') (a0 r')) = 0 := by
  unfold liftVec
  rw [dif_neg (by simp only [esI, a0, Fin.val_mk]; omega)]

theorem isotropic_vector_ne_zero (k r' : ℕ) : eI k (1 + r') (a0 r') ≠ esI k (1 + r') (a0 r') := by
  intro h
  have h' := congrArg Fin.val h
  simp only [eI, esI, a0, Fin.val_mk] at h'
  omega

@[simp] theorem d_es_es (k r' : ℕ) : star (es0 k r') ⬝ᵥ es0 k r' = 1 := by
  simp [es0, bvec, Pi.single_apply]
@[simp] theorem d_e_e (k r' : ℕ) : star (e0 k r') ⬝ᵥ e0 k r' = 1 := by
  simp [e0, bvec, Pi.single_apply]
@[simp] theorem d_es_e (k r' : ℕ) : star (es0 k r') ⬝ᵥ e0 k r' = 0 := by
  simp [es0, e0, bvec, Pi.single_apply, isotropic_vector_ne_zero k r']
@[simp] theorem d_e_es (k r' : ℕ) : star (e0 k r') ⬝ᵥ es0 k r' = 0 := by
  simp [es0, e0, bvec, Pi.single_apply, (isotropic_vector_ne_zero k r').symm]
@[simp] theorem d_es_l (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (es0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  have h := lift_kills_last_basis k r' w
  simp [es0, bvec, Pi.single_apply, dotProduct, h]
@[simp] theorem d_e_l (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (e0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  have h := lift_kills_first_basis k r' w
  simp [e0, bvec, Pi.single_apply, dotProduct, h]
@[simp] theorem d_l_es (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (liftVec k 1 r' w) ⬝ᵥ es0 k r' = 0 := by
  have h := lift_kills_last_basis k r' w
  simp [es0, bvec, Pi.single_apply, dotProduct, h]
@[simp] theorem d_l_e (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (liftVec k 1 r' w) ⬝ᵥ e0 k r' = 0 := by
  have h := lift_kills_first_basis k r' w
  simp [e0, bvec, Pi.single_apply, dotProduct, h]

theorem phiV_zero (k r' : ℕ) (h : 0 < 1 + r' + 1) : phiV k (1 + r') ⟨0, h⟩ = es0 k r' := by
  show (if h' : (0 : ℕ) < 1 + r' then bvec (esI k (1 + r') ⟨0, h'⟩) else epsV k (1 + r')) =
    bvec (esI k (1 + r') (a0 r'))
  rw [dif_pos (by omega)]
  rfl

private theorem sum_herm_bvec_mul_eq_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem heisG_mulVec_eq (k r' : ℕ) (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - (∑ j, herm (Hpk k (1 + r')) (bvec j) v * u j) • e0 k r' +
      (∑ j, herm (Hpk k (1 + r')) (bvec j) (e0 k r') * u j) • (v + b • e0 k r') := by
  ext i
  rw [heisG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply]
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun j _ => by ring

theorem heisenberg_dual_base_vector_formula (k r' : ℕ) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  rw [heis0, heisG_mulVec_eq, sum_herm_bvec_mul_eq_herm, sum_herm_bvec_mul_eq_herm]
  have h1 : herm (Hpk k (1 + r')) (es0 k r') (liftVec k 1 r' x.1) = 0 := by
    rw [herm, es0, hpk_es]
    exact d_l_e k r' x.1
  have h2 : herm (Hpk k (1 + r')) (es0 k r') (e0 k r') = 1 := by
    rw [herm, es0, hpk_es]
    exact d_e_e k r'
  rw [h1, h2, zero_smul, sub_zero, one_smul, ← add_assoc]

private theorem liftVec_apply_mk_succ (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1))
    (h : (q : ℕ) + 1 < 2 * (1 + r') + k + 1) : liftVec k 1 r' w ⟨(q : ℕ) + 1, h⟩ = w q := by
  unfold liftVec
  rw [dif_pos (by simp only [Fin.val_mk]; omega)]
  congr 1
  all_goals (ext; simp only [Fin.val_mk]; omega)

private theorem star_liftVec_dotProduct_liftVec (k r' : ℕ) (a b : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' a) ⬝ᵥ liftVec k 1 r' b = star a ⬝ᵥ b := by
  unfold dotProduct
  symm
  refine Fintype.sum_of_injective (fun q : Fin (2 * r' + k + 1) => (⟨(q : ℕ) + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)))
    (fun q1 q2 h => Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)) _ _ ?_ ?_
  · intro p hp
    have hp' : ¬ (1 ≤ (p : ℕ) ∧ (p : ℕ) < 2 * r' + k + 1 + 1) := by
      rintro ⟨h1, h2⟩
      exact hp ⟨⟨(p : ℕ) - 1, by omega⟩, Fin.ext (by simp only [Fin.val_mk]; omega)⟩
    simp only [Pi.star_apply]
    unfold liftVec
    rw [dif_neg hp', dif_neg hp', star_zero, zero_mul]
  · intro q
    simp only [Pi.star_apply]
    rw [liftVec_apply_mk_succ, liftVec_apply_mk_succ]

private theorem Hpk_one_add_mulVec_liftVec (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' w = liftVec k 1 r' (Hpk k r' *ᵥ w) := by
  funext p
  have hp := p.isLt
  simp only [Hpk_mulVec_apply_eq_ite, liftVec]
  split_ifs <;> (try simp only [Fin.val_mk] at *) <;>
    first
    | rfl
    | (exfalso; omega)
    | (congr 1; ext; simp only [Fin.val_mk]; omega)
    | (congr 2; ext; simp only [Fin.val_mk]; omega)

private theorem star_bvec_dotProduct {m : ℕ} (i : Fin m) (v : Fin m → ℂ) : star (bvec i) ⬝ᵥ v = v i := by
  have h : star (bvec i : Fin m → ℂ) = bvec i := by
    ext j
    simp only [bvec, Pi.star_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [h, bvec, single_dotProduct, one_mul]

private theorem Hpk_mulVec_apply_wI_zero (k r' : ℕ) (hk : 1 ≤ k) (x : Fin (2 * r' + k + 1) → ℂ) :
    (Hpk k r' *ᵥ x) (wI k r' 0) = x (wI k r' 0) := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega),
    if_neg (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega)]

private theorem Hpk_mulVec_apply_wI_last (k r' : ℕ) (x : Fin (2 * r' + k + 1) → ℂ) :
    (Hpk k r' *ᵥ x) (wI k r' (Fin.last k)) = -x (wI k r' (Fin.last k)) := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [wI, Fin.val_last, Fin.val_mk]; omega),
    if_pos (by simp only [wI, Fin.val_last, Fin.val_mk])]

private theorem star_phiV_dotProduct_Hpk_mulVec_eq_aF (k r' : ℕ) (hk : 1 ≤ k) (x : Fin (2 * r' + k + 1) → ℂ) (t : Fin (r' + 1)) :
    star (phiV k r' t) ⬝ᵥ (Hpk k r' *ᵥ x) = aF k r' x t := by
  have htl := t.isLt
  unfold phiV aF
  by_cases ht : (t : ℕ) < r'
  · rw [dif_pos ht, dif_pos ht, star_bvec_dotProduct]
    show (Hpk k r' *ᵥ x) ⟨2 * r' + k - (t : ℕ), by omega⟩ = _
    rw [Hpk_mulVec_apply_eq_ite, if_pos (by simp only [Fin.val_mk]; omega)]
    congr 1
    ext
    simp only [eI, Fin.val_mk]
    omega
  · rw [dif_neg ht, dif_neg ht]
    have e1 := Hpk_mulVec_apply_wI_zero k r' hk x
    have e2 := Hpk_mulVec_apply_wI_last k r' x
    have hc : star (((Real.sqrt 2)⁻¹ : ℂ)) = cc := by
      unfold cc
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    simp only [epsV, star_smul, star_add, smul_dotProduct, add_dotProduct, star_bvec_dotProduct, e1, e2,
      smul_eq_mul]
    rw [hc, sub_eq_add_neg]

theorem heis_lift (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (t : Fin (r' + 1)) :
    heis0 k r' x *ᵥ liftVec k 1 r' (phiV k r' t) = liftVec k 1 r' (phiV k r' t) - star (aF k r' x.1 t) • e0 k r' := by
  rw [heis0, heisG_mulVec_eq, sum_herm_bvec_mul_eq_herm, sum_herm_bvec_mul_eq_herm]
  have hE : herm (Hpk k (1 + r')) (liftVec k 1 r' (phiV k r' t)) (e0 k r') = 0 := by
    rw [herm, Hpk_one_add_mulVec_liftVec]
    exact d_e_l k r' _
  have hA : herm (Hpk k (1 + r')) (liftVec k 1 r' (phiV k r' t)) (liftVec k 1 r' x.1) =
      star (aF k r' x.1 t) := by
    rw [herm, Hpk_one_add_mulVec_liftVec, star_liftVec_dotProduct_liftVec, ← herm, herm_symm, herm]
    congr 1
    exact star_phiV_dotProduct_Hpk_mulVec_eq_aF k r' hk x.1 t
  rw [hE, hA, zero_smul, add_zero]

theorem sum_lt_split (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range m, f j + ∑ j ∈ Finset.range N, (if m ≤ j then f j else 0) := by
  rw [← Finset.sum_range_add_sum_Ico f hm, ← Finset.sum_filter]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
  omega

theorem final_alg (N m : ℕ) (hm : m ≤ N) (A A' : ℕ → ℂ) (Uu b : ℂ) :
    let x : ℕ → ℂ := fun j => A' j - b * A j
    (1 + (∑ j ∈ Finset.range N, (star (A j) * A j + star (A' j) * A' j) + Uu + b * star b) -
        ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (A j) * A j) +
      (∑ j ∈ Finset.range m, star (x j) * A j) * (∑ j ∈ Finset.range m, star (A j) * x j) =
    (1 + ∑ j ∈ Finset.range m, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range N, star (A j) * A j) + Uu +
        ∑ j ∈ Finset.range N, (if m ≤ j then star (A' j) * A' j else 0)) +
      (b + ∑ j ∈ Finset.range m, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range m, A' j * star (A j)) := by
  intro x
  have hx1 : ∑ j ∈ Finset.range m, star (x j) * x j = ∑ j ∈ Finset.range m, star (A' j) * A' j -
      b * ∑ j ∈ Finset.range m, star (A' j) * A j - star b * ∑ j ∈ Finset.range m, star (A j) * A' j +
      b * star b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, star_sub, star_mul']
    ring
  have hx2 : ∑ j ∈ Finset.range m, star (x j) * A j = ∑ j ∈ Finset.range m, star (A' j) * A j -
      star b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, star_sub, star_mul']
    ring
  have hx3 : ∑ j ∈ Finset.range m, star (A j) * x j = ∑ j ∈ Finset.range m, star (A j) * A' j -
      b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x]
    ring
  have hq : ∑ j ∈ Finset.range m, A' j * star (A j) = ∑ j ∈ Finset.range m, star (A j) * A' j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hs : star (b + ∑ j ∈ Finset.range m, star (A j) * A' j) =
      star b + ∑ j ∈ Finset.range m, star (A' j) * A j := by
    rw [star_add, star_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [star_mul', star_star, mul_comm]
  rw [hx1, hx2, hx3, hq, hs, Finset.sum_add_distrib, sum_lt_split N m hm (fun j => star (A' j) * A' j)]
  ring




def ix (k r' : ℕ) : Fin (r' + 1) ⊕ (Fin (r' + 1) ⊕ Fin (k - 1)) → Fin (2 * r' + k + 1)
  | Sum.inl t => ⟨t.val, by omega⟩
  | Sum.inr (Sum.inl t) => ⟨2 * r' + k - t.val, by omega⟩
  | Sum.inr (Sum.inr i) => ⟨r' + i.val + 1, by omega⟩

theorem ix_inj (k r' : ℕ) (hk : 1 ≤ k) : Function.Injective (ix k r') := by
  intro a b h
  rcases a with t | t | i <;> rcases b with s | s | j <;>
    simp only [ix, Fin.mk.injEq] at h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff, reduceCtorEq] <;> omega


theorem rankOne_base_weight_eq_cmTheta (k r' : ℕ) (t : Fin (r' + 1)) (ht : ¬ t.val < r') (h : t.val < 2 * r' + k + 1) :
    (⟨t.val, h⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 := Fin.ext (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega)





end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

private theorem star_bvec {n : ℕ} (p : Fin n) : star (bvec p) = bvec p := by
  funext q
  simp only [bvec, Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem dotProduct_bvec {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : v ⬝ᵥ bvec p = v p := by
  simp [bvec, dotProduct, Pi.single_apply]

private theorem bvec_dotProduct {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : bvec p ⬝ᵥ v = v p := by
  simp [bvec, dotProduct, Pi.single_apply]

private theorem star_inv_sqrt_two' : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  first
    | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
    | simp [Complex.star_def]
    | simp

private theorem inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    norm_num at h2
  rw [← h2]
  field_simp

private theorem Hpk_mulVec_apply_of_outer (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h : i.val < r ∨ r + k < i.val) : (Hpk k r *ᵥ y) i = y ⟨2 * r + k - i.val, by omega⟩ := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
  · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

private theorem Hpk_mulVec_apply_of_mem_middle (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val < r + k) : (Hpk k r *ᵥ y) i = y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · have e : Hpk k r i i = 1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

private theorem Hpk_mulVec_apply_of_val_eq_add (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h : i.val = r + k) : (Hpk k r *ᵥ y) i = -y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · have e : Hpk k r i i = -1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, neg_one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

private theorem Hpk_conjTranspose_eq_self (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.conjTranspose_apply]
  simp only [Hpk, Fin.ext_iff] <;> (try split_ifs) <;> first | (exfalso; omega) | simp

private theorem Hpk_mulVec_Hpk_mulVec (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ y) = y := by
  funext i
  have hi := i.isLt
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [Hpk_mulVec_apply_of_outer k r _ i h1, Hpk_mulVec_apply_of_outer k r y (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)) (by simp only [Fin.val_mk]; omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  · by_cases h2 : i.val = r + k
    · rw [Hpk_mulVec_apply_of_val_eq_add k r _ i h2, Hpk_mulVec_apply_of_val_eq_add k r y i h2, neg_neg]
    · rw [Hpk_mulVec_apply_of_mem_middle k r _ i (by omega) (by omega), Hpk_mulVec_apply_of_mem_middle k r y i (by omega) (by omega)]

private theorem bvec_apply_eq_ite_val {n : ℕ} (p q : Fin n) : bvec p q = if q.val = p.val then 1 else 0 := by
  first
    | simp [bvec, Pi.single_apply, Fin.ext_iff]
    | (unfold bvec; rw [Pi.single_apply]; simp only [Fin.ext_iff])
    | (by_cases h : q = p
       · subst h; simp [bvec]
       · rw [if_neg (fun e => h (Fin.ext e))]; simp [bvec, h])

private theorem epsV_apply_eq (k r : ℕ) (q : Fin (2 * r + k + 1)) :
    epsV k r q = (Real.sqrt 2 : ℂ)⁻¹ * (bvec (wI k r 0) q + bvec (wI k r (Fin.last k)) q) := rfl

theorem phiV_succ (k r' t : ℕ) (ht : t < r' + 1) (h : t + 1 < 1 + r' + 1) :
    phiV k (1 + r') ⟨t + 1, h⟩ = liftVec k 1 r' (phiV k r' ⟨t, ht⟩) := by
  funext p
  have hp := p.isLt
  simp only [phiV, liftVec, epsV_apply_eq, bvec_apply_eq_ite_val, esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]
  split_ifs <;> (try simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]) <;> (try split_ifs) <;>
    first | rfl | (exfalso; omega) | (simp_all; done) | omega

theorem ortho (k r : ℕ) (hk : 1 ≤ k) (i j : Fin (r + 1)) :
    star (phiV k r i) ⬝ᵥ phiV k r j = if i = j then 1 else 0 := by
  unfold phiV
  by_cases hi : i.val < r <;> by_cases hj : j.val < r
  · rw [dif_pos hi, dif_pos hj, star_bvec, dotProduct_bvec]
    simp only [bvec_apply_eq_ite_val, esI, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [dif_pos hi, dif_neg hj, star_bvec, bvec_dotProduct, if_neg (fun (e : i = j) => hj (e ▸ hi))]
    simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [dif_neg hi, dif_pos hj, dotProduct_bvec, if_neg (fun (e : i = j) => hi (e ▸ hj))]
    simp only [Pi.star_apply, epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [dif_neg hi, dif_neg hj, if_pos (Fin.ext (by omega))]
    have hv : (wI k r 0).val ≠ (wI k r (Fin.last k)).val := by
      simp only [wI, Fin.val_mk, Fin.val_zero, Fin.val_last]
      omega
    unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, star_inv_sqrt_two', smul_dotProduct, dotProduct_smul, add_dotProduct,
      dotProduct_add, dotProduct_add]
    simp only [dotProduct_bvec, smul_eq_mul]
    simp only [bvec_apply_eq_ite_val, if_neg hv, if_neg (Ne.symm hv), eq_self_iff_true, if_true]
    linear_combination inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one

theorem dot_swap {n : ℕ} (u v : Fin n → ℂ) : star u ⬝ᵥ v = star (star v ⬝ᵥ u) := by
  first
    | exact star_dotProduct u v
    | exact Matrix.star_dotProduct u v
    | (simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
       exact Finset.sum_congr rfl fun i _ => mul_comm _ _)

def AN (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : ℕ) : ℂ := if h : j < r' + 1 then aF k r' y ⟨j, h⟩ else 0

def AN' (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : ℕ) : ℂ := if h : j < r' + 1 then aF' k r' y ⟨j, h⟩ else 0

def Uu (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : ℂ :=
  ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i)))

theorem phi_dot_y (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (t : Fin (r' + 1)) :
    star (phiV k r' t) ⬝ᵥ y = aF' k r' y t := by
  unfold phiV aF'
  split_ifs with ht
  · rw [star_bvec, bvec_dotProduct]
  · unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two',
      smul_eq_mul]

theorem pars1' (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    star y ⬝ᵥ y = ∑ j ∈ Finset.range (r' + 1), (star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) +
      Uu k r' y := by
  have key : ∀ a b : Fin (2 * r' + k + 1), a.val = b.val → star (y a) * y a = star (y b) * y b := by
    intro a b h
    rw [Fin.ext h]
  set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * y ⟨n, h⟩ else 0 with hf
  have hL : star y ⬝ᵥ y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n := by
    rw [← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf, Pi.star_apply]
    rw [dif_pos i.isLt]
  have h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', star (AN k r' y j) * AN k r' y j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hf, AN, aF, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [eI, Fin.val_mk])
  have h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) =
      ∑ j ∈ Finset.range r', star (AN' k r' y j) * AN' k r' y j := by
    rw [← Finset.sum_range_reflect (fun j => star (AN' k r' y j) * AN' k r' y j) r']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hf, AN', aF', Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [esI, Fin.val_mk]; omega)
  have h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]
    unfold Uu
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    simp only [hf]
    rw [dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1)]
    exact key _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
  have h4 : f r' + f (r' + 1 + (k - 1)) =
      star (AN k r' y r') * AN k r' y r' + star (AN' k r' y r') * AN' k r' y r' := by
    simp only [hf, AN, AN', aF, aF', Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | skip
    rw [show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]),
      show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from
        Fin.ext (by simp [wI]; omega)]
    simp only [cc, star_mul', star_sub, star_add, star_inv_sqrt_two']
    linear_combination (-(star (y (wI k r' 0)) * y (wI k r' 0) +
      star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
  rw [hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega,
    Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)),
    Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r',
    Finset.sum_range_succ (fun j => star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) r',
    Finset.sum_add_distrib, h1, h2, h3]
  linear_combination h4

theorem gram_Y (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (fun a => heis0 k r' x *ᵥ phiV k (1 + r') a) =
      (let A := AN k r' x.1; let A' := AN' k r' x.1; let b := hb k r' x.1 x.2
       (1 + ∑ j ∈ Finset.range l.val, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range (r' + 1), star (A j) * A j) +
          Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (A' j) * A' j else 0)) +
        (b + ∑ j ∈ Finset.range l.val, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range l.val, A' j * star (A j))).re := by
  dsimp only
  set A := AN k r' x.1 with hAd
  set A' := AN' k r' x.1 with hA'd
  set b := hb k r' x.1 x.2 with hbd
  have hY0 : ∀ c : Fin (1 + r' + 1), c.val = 0 →
      heis0 k r' x *ᵥ phiV k (1 + r') c = es0 k r' + liftVec k 1 r' x.1 + b • e0 k r' := by
    intro c hc; have hc' : c = ⟨0, by omega⟩ := Fin.ext hc; rw [hc', phiV_zero, heisenberg_dual_base_vector_formula]
  have hYs : ∀ c : Fin (1 + r' + 1), ∀ j (hj : j < r' + 1), c.val = j + 1 →
      heis0 k r' x *ᵥ phiV k (1 + r') c = liftVec k 1 r' (phiV k r' ⟨j, hj⟩) - star (A j) • e0 k r' := by
    intro c j hj hc; have hc' : c = ⟨j + 1, by omega⟩ := Fin.ext hc
    rw [hc', phiV_succ k r' j hj, heis_lift k r' hk]; simp only [A, AN, dif_pos hj]
  have hA : ∀ j (hj : j < r' + 1), A' j = aF' k r' x.1 ⟨j, hj⟩ := fun j hj => by simp only [A', AN', dif_pos hj]
  have hml : l.val ≤ r' + 1 := by have := l.isLt; omega
  unfold Ga
  rw [gram_det l.val _ (star x.1 ⬝ᵥ x.1 + b * star b) (fun j => A' j - b * A j) A]
  · congr 1
    rw [pars1' k r' hk]
    exact final_alg (r' + 1) l.val hml A A' (Uu k r' x.1) b
  · simp only [Matrix.of_apply]; rw [hY0 _ (by simp)]
    simp [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, lift_dot]; ring
  · intro j; simp only [Matrix.of_apply]
    rw [hY0 _ (by simp), hYs _ j.val (by omega) (by simp), hA j.val (by omega)]
    simp [star_add, star_smul, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, lift_dot, dot_swap (x.1), phi_dot_y]
    try ring
  · intro j; simp only [Matrix.of_apply]
    rw [hYs _ j.val (by omega) (by simp), hY0 _ (by simp), hA j.val (by omega)]
    simp [star_add, star_smul, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, lift_dot, phi_dot_y]; ring
  · intro i j; simp only [Matrix.of_apply]
    rw [hYs _ i.val (by omega) (by simp), hYs _ j.val (by omega) (by simp)]
    simp [star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, lift_dot,
      ortho k r' hk, Fin.ext_iff]
    try ring

theorem nsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  first
    | (rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq])
    | (rw [Complex.star_def, Complex.conj_mul']; push_cast; ring)
    | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]

theorem fsum (r' : ℕ) (g : ℕ → ℂ) : ∑ j : Fin (1 + r'), g j.val = ∑ j ∈ Finset.range (r' + 1), g j := by
  rw [Fin.sum_univ_eq_sum_range g (1 + r'), Nat.add_comm]

theorem fsum_lt (r' m : ℕ) (hm : m ≤ r' + 1) (g : ℕ → ℂ) :
    ∑ j : Fin (1 + r'), (if j.val < m then g j.val else 0) = ∑ j ∈ Finset.range m, g j := by
  have hs := Fin.sum_univ_eq_sum_range (fun j => if j < m then g j else 0) (1 + r')
  rw [hs, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨by omega, h⟩

theorem hc1 (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (j : Fin (1 + r')) : (hcoord k r' x).1 j = AN k r' x.1 j.val := by
  have hj : j.val < r' + 1 := by omega
  show herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j)) = AN k r' x.1 j.val
  unfold AN herm
  rw [dif_pos hj]
  unfold phiV aF
  try simp only [Fin.coe_cast, Fin.val_mk]
  split_ifs with h
  · rw [star_bvec, bvec_dotProduct, Hpk_mulVec_apply_of_outer]
    · refine congrArg x.1 (Fin.ext ?_)
      simp only [esI, eI, Fin.val_mk]
      omega
    · simp only [esI, Fin.val_mk]
      omega
  · unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two',
      Hpk_mulVec_apply_of_mem_middle, Hpk_mulVec_apply_of_val_eq_add]
    all_goals first
      | (simp only [smul_eq_mul, cc]; ring)
      | (simp [wI]; done)
      | (simp [wI]; omega)
      | omega

theorem hc2 (k r' : ℕ) (x : HPar k r') (j : Fin (1 + r')) : (hcoord k r' x).2.1 j = AN' k r' x.1 j.val := by
  have hj : j.val < r' + 1 := by omega
  show herm (Hpk k r') x.1 (phiV' k r' (Fin.cast (by omega) j)) = AN' k r' x.1 j.val
  unfold herm phiV'
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Hpk_conjTranspose_eq_self, Hpk_mulVec_Hpk_mulVec, phi_dot_y]
  unfold AN'
  rw [dif_pos hj]
  rfl

theorem Uu_real (k r' : ℕ) (x : HPar k r') :
    ((∑ i, ‖(hcoord k r' x).2.2.1 i‖ ^ 2 : ℝ) : ℂ) = Uu k r' x.1 := by
  unfold Uu
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsq]
  have e : (hcoord k r' x).2.2.1 i = x.1 (ix k r' (Sum.inr (Sum.inr i))) := by
    show x.1 (wI k r' ⟨i.val + 1, by omega⟩) = _
    congr 1 <;> first | rfl | (apply Fin.ext; rfl) | (apply Fin.ext; simp [wI, ix]) | (apply Fin.ext; simp [wI, ix]; omega)
  rw [e]

theorem Lsq_c (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    (Lsq (hcoord k r' x) l : ℂ) = 1 + ∑ j ∈ Finset.range l.val, star (AN k r' x.1 j) * AN k r' x.1 j := by
  have hl := l.isLt
  unfold Lsq
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_sum]
  congr 1
  rw [← fsum_lt r' l.val (by omega) (fun j => star (AN k r' x.1 j) * AN k r' x.1 j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [nsq, hc1 k r' hk x j]
  · simp

theorem rhoSq_c (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    (rhoSq (hcoord k r' x) l : ℂ) = (1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j) +
      Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0) := by
  have hL : (Lsq (hcoord k r' x) (Fin.last (1 + r')) : ℂ) =
      1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j := by
    rw [Lsq_c k r' hk x, Fin.val_last, Nat.add_comm 1 r']
  unfold rhoSq
  rw [Complex.ofReal_add, Complex.ofReal_add, hL, Uu_real, Complex.ofReal_sum]
  congr 1
  rw [← fsum r' (fun j => if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [nsq, hc2 k r' x j]
  · simp

theorem bco_eq (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    bco (hcoord k r' x) l = hb k r' x.1 x.2 + ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j) := by
  have hl := l.isLt
  have hB : ∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) =
      ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) := by
    rw [← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc1 k r' hk x j, hc2 k r' x j]
  have hC : ∑ j : Fin (1 + r'), (if l.val ≤ j.val then (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) else 0) =
      ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) -
        ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j) := by
    rw [← fsum_lt r' l.val (by omega) (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)),
      ← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)), eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc1 k r' hk x j, hc2 k r' x j]
    split_ifs <;> first | (exfalso; omega) | simp
  have hD : herm (Hpk k r') x.1 x.1 = (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) +
      star (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) + Uu k r' x.1 := by
    set y := x.1 with hy
    have key2 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val →
        star (y a) * y b = y d * star (y c) := by
      intro a b c d h1 h2
      rw [Fin.ext h1, Fin.ext h2, mul_comm]
    have key3 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val →
        star (y a) * y b = star (y c) * y d := by
      intro a b c d h1 h2
      rw [Fin.ext h1, Fin.ext h2]
    set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * (Hpk k r' *ᵥ y) ⟨n, h⟩ else 0
      with hf
    have hL : herm (Hpk k r') y y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n := by
      rw [← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]
      simp only [herm, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf, Pi.star_apply]
      rw [dif_pos i.isLt]
    have h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hf, AN, AN', aF, aF', Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_outer k r' y ⟨j, by omega⟩ (Or.inl (by simp only [Fin.val_mk]; omega))]
      exact key2 _ _ _ _ (by simp only [eI, Fin.val_mk]) (by simp only [esI, Fin.val_mk] <;> omega)
    have h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) =
        star (∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j)) := by
      rw [star_sum, ← Finset.sum_range_reflect (fun j => star (AN' k r' y j * star (AN k r' y j))) r']
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hf, AN, AN', aF, aF', Fin.val_mk, star_mul', star_star]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_outer k r' y ⟨r' + 1 + (k - 1) + 1 + j, by omega⟩ (Or.inr (by simp only [Fin.val_mk]; omega))]
      exact key3 _ _ _ _ (by simp only [esI, Fin.val_mk] <;> omega) (by simp only [eI, Fin.val_mk] <;> omega)
    have h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y := by
      rw [← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]
      unfold Uu
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.isLt
      simp only [hf]
      rw [dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1),
        Hpk_mulVec_apply_of_mem_middle k r' y ⟨r' + 1 + i.val, by omega⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
      exact key3 _ _ _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
        (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
    have h4 : f r' + f (r' + 1 + (k - 1)) =
        AN' k r' y r' * star (AN k r' y r') + star (AN' k r' y r' * star (AN k r' y r')) := by
      simp only [hf, AN, AN', aF, aF', Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_mem_middle k r' y ⟨r', by omega⟩, Hpk_mulVec_apply_of_val_eq_add k r' y ⟨r' + 1 + (k - 1), by omega⟩]
      · rw [show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]),
          show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from
            Fin.ext (by simp [wI]; omega)]
        simp only [cc, star_mul', star_sub, star_add, star_star, star_inv_sqrt_two']
        linear_combination (-(star (y (wI k r' 0)) * y (wI k r' 0) -
          star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
      all_goals first | omega | (simp only [Fin.val_mk]; omega) | simp
    rw [hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega,
      Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)),
      Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r',
      Finset.sum_range_succ (fun j => AN' k r' y j * star (AN k r' y j)) r', star_add, h1, h2, h3]
    linear_combination h4
  unfold bco
  rw [hC]
  have hT : (hcoord k r' x).2.2.2 = x.2 + (∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j)).im := rfl
  rw [hT, hB]
  unfold hb
  rw [hD, ← Uu_real k r' x]
  generalize (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) = S
  generalize (∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j)) = R
  generalize (∑ i, ‖(hcoord k r' x).2.2.1 i‖ ^ 2) = U
  apply Complex.ext <;> simp [Complex.star_def] <;> ring

theorem del_formula (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Del k (1 + r') l (heis0 k r' x) = de (hcoord k r' x) l := by
  unfold Del de
  congr 1
  rw [gram_Y k r' hk x l]
  try dsimp only
  rw [← Lsq_c k r' hk x l, ← rhoSq_c k r' hk x l, ← bco_eq k r' hk x l,
    mul_comm (bco (hcoord k r' x) l) (star _), ← nsq, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

theorem shear_mp {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) (c : ℂ) :
    MeasurePreserving (fun y : Fin (n + 1) → ℂ => Function.update y i (y i + c * y j)) volume volume := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i
  have he : MeasurePreserving e volume ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) i
  have h1 : MeasurePreserving (fun p : (Fin n → ℂ) × ℂ => (p.1, p.2 + c * p.1 j'))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
    refine (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).skew_product
      (g := fun x a => a + c * x j') ?_ ?_
    · exact measurable_snd.add (measurable_const.mul ((measurable_pi_apply j').comp measurable_fst))
    · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self (volume : Measure ℂ) (c * x j')
  have hS : MeasurePreserving (fun p : ℂ × (Fin n → ℂ) => (p.1 + c * p.2 j', p.2))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ)))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    (Measure.measurePreserving_swap).comp (h1.comp Measure.measurePreserving_swap)
  have key : (fun y : Fin (n + 1) → ℂ => Function.update y i (y i + c * y j)) =
      e.symm ∘ (fun p : ℂ × (Fin n → ℂ) => (p.1 + c * p.2 j', p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · show Function.update y i (y i + c * y j) i = y i + c * y (i.succAbove j')
      rw [hj']
      simp
    · funext m
      show Function.update y i (y i + c * y j) (i.succAbove m) = y (i.succAbove m)
      simp [Function.update_apply, Fin.succAbove_ne]
  rw [key]
  exact (MeasurePreserving.symm e he).comp (hS.comp he)

theorem fne {n : ℕ} (a b : Fin n) (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem w_ne (k r' : ℕ) (hk : 1 ≤ k) : wI k r' 0 ≠ wI k r' (Fin.last k) := by
  intro h
  have h' := congrArg Fin.val h
  simp [wI, Fin.last] at h'
  omega

def rotF (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ :=
  Function.update (Function.update y (wI k r' 0) (cc * (y (wI k r' 0) - y (wI k r' (Fin.last k)))))
    (wI k r' (Fin.last k)) (cc * (y (wI k r' 0) + y (wI k r' (Fin.last k))))

private lemma measurePreserving_update_update_cc_rotation_of_ne {N : ℕ} (a b : Fin (N + 1)) (hne : a ≠ b) :
    MeasurePreserving (fun y : Fin (N + 1) → ℂ =>
      Function.update (Function.update y a (cc * (y a - y b))) b (cc * (y a + y b))) volume volume := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = ((Real.sqrt 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hq : q ^ 2 = 2 := by
    rw [hqdef, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    norm_num at hq
  have hcc : cc = q / 2 := by
    have hinv : cc = q⁻¹ := by
      rw [hqdef]
    rw [hinv, eq_div_iff two_ne_zero, ← hq, pow_two, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  have key : (fun y : Fin (N + 1) → ℂ =>
      Function.update (Function.update y a (cc * (y a - y b))) b (cc * (y a + y b))) =
      (fun y : Fin (N + 1) → ℂ => Function.update y a (y a + -(q - 1) * y b)) ∘
      ((fun y : Fin (N + 1) → ℂ => Function.update y b (y b + q / 2 * y a)) ∘
      (fun y : Fin (N + 1) → ℂ => Function.update y a (y a + -(q - 1) * y b))) := by
    funext y m
    by_cases hma : m = a
    · simp [Function.update_apply, hma, hne, hne.symm, hcc]
      linear_combination (y a - (q - 2) * y b) / 2 * hq
    · by_cases hmb : m = b
      · simp [Function.update_apply, hmb, hne, hne.symm, hcc]
        linear_combination y b / 2 * hq
      · simp [Function.update_apply, hma, hmb]
  rw [key]
  exact (shear_mp a b hne _).comp ((shear_mp b a hne.symm _).comp (shear_mp a b hne _))

theorem rot_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (rotF k r') volume volume := by
  exact measurePreserving_update_update_cc_rotation_of_ne (wI k r' 0) (wI k r' (Fin.last k)) (w_ne k r' hk)

def ix2 (k r' : ℕ) : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) → Fin (2 * r' + k + 1)
  | Sum.inl t => ⟨t.val, by omega⟩
  | Sum.inr (Sum.inl t) => ⟨2 * r' + k - t.val, by omega⟩
  | Sum.inr (Sum.inr i) => ⟨r' + i.val + 1, by omega⟩

theorem index_embedding_bijective (k r' : ℕ) (hk : 1 ≤ k) : Function.Bijective (ix2 k r') := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro (a | a | a) (b | b | b) h <;>
      (have := a.isLt; have := b.isLt; simp [ix2, Fin.ext_iff] at h ⊢ <;> omega)
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

def permF (k r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ) :=
  (fun j => z (ix2 k r' (Sum.inl j)), fun j => z (ix2 k r' (Sum.inr (Sum.inl j))),
    fun i => z (ix2 k r' (Sum.inr (Sum.inr i))))

theorem perm_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (permF k r') volume volume := by
  let E := Equiv.ofBijective (ix2 k r') (index_embedding_bijective k r' hk)
  have h1 := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : Fin (2 * r' + k + 1) => (volume : Measure ℂ)) E)
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (1 + r') ⊕ Fin (k - 1) => (volume : Measure ℂ))
  have h4 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod h3
  have h5 := h4.comp (h2.comp h1)
  first
    | exact h5
    | (convert h5 using 1; funext z; rfl)

theorem lin_eq (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    permF k r' (rotF k r' y) = ((hcoord k r' (y, 0)).1, (hcoord k r' (y, 0)).2.1, (hcoord k r' (y, 0)).2.2.1) := by
  have hne := w_ne k r' hk
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun j => ?_) (funext fun i => ?_))
  · have := j.isLt
    show rotF k r' y ⟨j.val, by omega⟩ = (hcoord k r' (y, 0)).1 j
    rw [hc1 k r' hk, AN, dif_pos (by omega), aF]
    split_ifs with hj
    · have hj' : j.val < r' := hj
      have n1 : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
        fne _ _ (by simp only [wI, Fin.val_last]; omega)
      have n0 : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
        fne _ _ (by simp only [wI, Fin.val_zero]; omega)
      rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
      try rfl
    · have hj' : ¬ j.val < r' := hj
      have e : (⟨j.val, by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 :=
        Fin.ext (by simp only [wI, Fin.val_zero]; omega)
      rw [e, rotF, Function.update_of_ne hne, Function.update_self]
  · have := j.isLt
    show rotF k r' y ⟨2 * r' + k - j.val, by omega⟩ = (hcoord k r' (y, 0)).2.1 j
    rw [hc2, AN', dif_pos (by omega), aF']
    split_ifs with hj
    · have hj' : j.val < r' := hj
      have n1 : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
        fne _ _ (by simp only [wI, Fin.val_last]; omega)
      have n0 : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
        fne _ _ (by simp only [wI, Fin.val_zero]; omega)
      rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
      try rfl
    · have hj' : ¬ j.val < r' := hj
      have e : (⟨2 * r' + k - j.val, by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) :=
        Fin.ext (by simp only [wI, Fin.val_last]; omega)
      rw [e, rotF, Function.update_self]
  · have := i.isLt
    show rotF k r' y ⟨r' + i.val + 1, by omega⟩ = (hcoord k r' (y, 0)).2.2.1 i
    have n1 : (⟨r' + i.val + 1, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' (Fin.last k) :=
      fne _ _ (by simp only [wI, Fin.val_last]; omega)
    have n0 : (⟨r' + i.val + 1, by omega⟩ : Fin (2 * r' + k + 1)) ≠ wI k r' 0 :=
      fne _ _ (by simp only [wI, Fin.val_zero]; omega)
    rw [rotF, Function.update_of_ne n1, Function.update_of_ne n0]
    try rfl

def imF (k r' : ℕ) (q : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) : ℝ :=
  (∑ j, q.2.1 j * star (q.1 j)).im

theorem imF_meas (k r' : ℕ) : Measurable (imF k r') := by
  apply Continuous.measurable
  unfold imF
  fun_prop

theorem hcoord_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (hcoord k r') volume volume := by
  have hL : MeasurePreserving (fun y => permF k r' (rotF k r' y)) volume volume :=
    (perm_mp k r' hk).comp (rot_mp k r' hk)
  have hP := hL.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hSk : MeasurePreserving
      (fun z : ((Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) × ℝ =>
        (z.1, z.2 + imF k r' z.1)) volume volume := by
    refine (MeasurePreserving.id
      (volume : Measure ((Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)))).skew_product
      (g := fun q t => t + imF k r' q) ?_ ?_
    · exact measurable_snd.add ((imF_meas k r').comp measurable_fst)
    · exact Filter.Eventually.of_forall fun q => map_add_right_eq_self (volume : Measure ℝ) (imF k r' q)
  have hA1 := measurePreserving_prodAssoc (volume : Measure (Fin (1 + r') → ℂ))
    (volume : Measure ((Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ))) (volume : Measure ℝ)
  have hA2 := measurePreserving_prodAssoc (volume : Measure (Fin (1 + r') → ℂ))
    (volume : Measure (Fin (k - 1) → ℂ)) (volume : Measure ℝ)
  have hA3 := (MeasurePreserving.id (volume : Measure (Fin (1 + r') → ℂ))).prod hA2
  have hAll := hA3.comp (hA1.comp (hSk.comp hP))
  have key : hcoord k r' = fun x : HPar k r' =>
      ((permF k r' (rotF k r' x.1)).1, (permF k r' (rotF k r' x.1)).2.1,
        (permF k r' (rotF k r' x.1)).2.2, x.2 + imF k r' (permF k r' (rotF k r' x.1))) := by
    funext x
    obtain ⟨y, t⟩ := x
    dsimp only
    rw [lin_eq k r' hk y]
    rfl
  rw [key]
  exact hAll

theorem formulaF_all : FormulaF := fun k r' hk => ⟨fun x l => del_formula k r' hk x l, hcoord_mp k r' hk⟩

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Xi

end ReciprocityTheory.ChartRestriction.DS.Xi
end
