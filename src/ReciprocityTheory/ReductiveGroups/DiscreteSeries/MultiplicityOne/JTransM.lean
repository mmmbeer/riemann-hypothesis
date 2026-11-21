import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary
import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

section
noncomputable section

open Matrix
open scoped InnerProductSpace ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace TransM

variable {S : Type} [Fintype S] [DecidableEq S]

def cE (S : Type) [Fintype S] : EuclideanSpace ℂ S ≃ₗᵢ⋆[ℂ] EuclideanSpace ℂ S where
  toFun v := WithLp.toLp 2 (fun i => conj (v.ofLp i))
  invFun v := WithLp.toLp 2 (fun i => conj (v.ofLp i))
  map_add' u v := by ext i; simp
  map_smul' a v := by ext i; simp
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  norm_map' v := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp

private theorem unitary_exists_unit_scalar_isUnit_det_one_add (m : Matrix S S ℂ) (hm : mᴴ * m = 1) :
    ∃ ζ : ℂ, starRingEnd ℂ ζ * ζ = 1 ∧ IsUnit (1 + ζ • m).det := by
  have hH : (m + mᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ := ((Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).diff
    (Finset.univ.image fun j => -hH.eigenvalues j / 2).finite_toSet).nonempty
  obtain ⟨s, hs2⟩ : ∃ s : ℝ, s ^ 2 = 1 - r ^ 2 := ⟨Real.sqrt (1 - r ^ 2), Real.sq_sqrt (by nlinarith)⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ = (r : ℂ) + (s : ℂ) * Complex.I := ⟨_, rfl⟩
  have hζ1 : starRingEnd ℂ ζ * ζ = 1 := by
    subst hζ
    apply Complex.ext <;> simp <;> nlinarith [hs2]
  have hζ2 : ζ + starRingEnd ℂ ζ = 2 * (r : ℂ) := by
    subst hζ
    apply Complex.ext <;> simp <;> ring
  refine ⟨ζ, hζ1, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have ha : m *ᵥ v = (-starRingEnd ℂ ζ) • v := by
    funext i
    have h1 := congrFun hv i
    have hsm : (ζ • m) *ᵥ v = ζ • (m *ᵥ v) := by
      first
        | exact Matrix.smul_mulVec ζ m v
        | exact Matrix.smul_mulVec_assoc ζ m v
        | (funext k; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, hsm, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (starRingEnd ℂ ζ) * h1 - (m *ᵥ v) i * hζ1
  have hb : mᴴ *ᵥ v = (-ζ) • v := by
    have h2 : mᴴ *ᵥ (m *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at h2
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at h3 ⊢
    linear_combination (-ζ) * h3 - (mᴴ *ᵥ v) i * hζ1
  have hsum : (m + mᴴ) *ᵥ v = ((-2 * r : ℝ) : ℂ) • v := by
    funext i
    rw [Matrix.add_mulVec, Pi.add_apply, ha, hb]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (-(v i)) * hζ2
  obtain ⟨W, hW⟩ : ∃ W : Matrix S S ℂ, W = (hH.eigenvectorUnitary : Matrix S S ℂ) := ⟨_, rfl⟩
  have hW1 : Wᴴ * W = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hW2 : W * Wᴴ = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hsp : m + mᴴ = W * Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) * Wᴴ := by
    rw [hW]
    conv_lhs => rw [hH.spectral_theorem]
    first
      | rfl
      | simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
  obtain ⟨y, hy⟩ : ∃ y : S → ℂ, y = Wᴴ *ᵥ v := ⟨_, rfl⟩
  have hy0 : y ≠ 0 := by
    intro h
    apply hv0
    rw [← Matrix.one_mulVec v, ← hW2, ← Matrix.mulVec_mulVec, ← hy, h, Matrix.mulVec_zero]
  have h4 : Wᴴ *ᵥ ((m + mᴴ) *ᵥ v) = Wᴴ *ᵥ (((-2 * r : ℝ) : ℂ) • v) := by rw [hsum]
  rw [Matrix.mulVec_smul, ← hy, Matrix.mulVec_mulVec, hsp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hW1,
    Matrix.one_mul, ← Matrix.mulVec_mulVec, ← hy] at h4
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have h5 := congrFun h4 j
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h5
  have h6 : (hH.eigenvalues j : ℂ) = ((-2 * r : ℝ) : ℂ) := mul_right_cancel₀ hj h5
  have h7 : hH.eigenvalues j = -2 * r := by exact_mod_cast h6
  exact hr (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [h7]; ring⟩))

private theorem unitary_exists_diagonalization (m : Matrix S S ℂ) (hm : mᴴ * m = 1) :
    ∃ V : Matrix S S ℂ, ∃ d : S → ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      (∀ i, starRingEnd ℂ (d i) * d i = 1) ∧ m = V * Matrix.diagonal d * Vᴴ := by
  obtain ⟨ζ, hζ1, hQ⟩ := unitary_exists_unit_scalar_isUnit_det_one_add m hm
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have hζ0' : starRingEnd ℂ ζ ≠ 0 := by rintro h; rw [h, zero_mul] at hζ1; exact zero_ne_one hζ1
  obtain ⟨u, hu⟩ : ∃ u : Matrix S S ℂ, u = ζ • m := ⟨_, rfl⟩
  have hu1 : uᴴ * u = 1 := by
    rw [hu, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hm, smul_smul]
    show (starRingEnd ℂ ζ * ζ) • (1 : Matrix S S ℂ) = 1
    rw [hζ1, one_smul]
  obtain ⟨Q, hQd⟩ : ∃ Q : Matrix S S ℂ, Q = 1 + u := ⟨_, rfl⟩
  rw [← hu, ← hQd] at hQ
  obtain ⟨X, hX⟩ : ∃ X : Matrix S S ℂ, X = (1 - u) * Q⁻¹ := ⟨_, rfl⟩
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  have hXQ : X * Q = 1 - u := by rw [hX, Matrix.mul_assoc, hQQ', Matrix.mul_one]
  have key : u * (1 + X) = 1 - X := by
    have h2 : u * (1 + X) * Q = (1 - X) * Q := by
      rw [Matrix.mul_assoc, add_mul, sub_mul, Matrix.one_mul, hXQ, hQd]
      noncomm_ring
    calc u * (1 + X) = u * (1 + X) * Q * Q⁻¹ := by rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_one]
      _ = (1 - X) * Q * Q⁻¹ := by rw [h2]
      _ = 1 - X := by rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hQH : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  have canc : ∀ Y : Matrix S S ℂ, Y = (Q⁻¹)ᴴ * (Qᴴ * Y * Q) * Q⁻¹ := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hQQ, Matrix.mul_one, ← Matrix.mul_assoc, hQH, Matrix.one_mul]
  have e : Qᴴ * Xᴴ * Q = Qᴴ * (-X) * Q := by
    rw [← Matrix.conjTranspose_mul, hXQ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hXQ, hQd,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    simp only [add_mul, sub_mul, mul_add, mul_sub, Matrix.one_mul, Matrix.mul_one, hu1]
    abel
  have hXs : Xᴴ = -X := by rw [canc Xᴴ, e, ← canc]
  have hH : (Complex.I • X).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hXs, smul_neg, ← neg_smul]
    congr 1
    show -(starRingEnd ℂ Complex.I) = Complex.I
    rw [Complex.conj_I, neg_neg]
  obtain ⟨W, hW⟩ : ∃ W : Matrix S S ℂ, W = (hH.eigenvectorUnitary : Matrix S S ℂ) := ⟨_, rfl⟩
  have hW1 : Wᴴ * W = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hW2 : W * Wᴴ = 1 := by
    rw [hW, ← Matrix.star_eq_conjTranspose (hH.eigenvectorUnitary : Matrix S S ℂ)]
    first
      | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  obtain ⟨ev, hev⟩ : ∃ ev : S → ℝ, ev = hH.eigenvalues := ⟨_, rfl⟩
  have hsp : Complex.I • X = W * Matrix.diagonal (fun j => (ev j : ℂ)) * Wᴴ := by
    rw [hW, hev]
    conv_lhs => rw [hH.spectral_theorem]
    first
      | rfl
      | simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hY : Wᴴ * X * W = Matrix.diagonal (fun j => -Complex.I * (ev j : ℂ)) := by
    have h := congrArg (fun M => Wᴴ * M * W) hsp
    try simp only at h
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    rw [show Wᴴ * (W * Matrix.diagonal (fun j => (ev j : ℂ)) * Wᴴ) * W =
        Matrix.diagonal (fun j => (ev j : ℂ)) by
      simp only [Matrix.mul_assoc]
      rw [hW1, Matrix.mul_one, ← Matrix.mul_assoc, hW1, Matrix.one_mul]] at h
    ext i j
    have h8 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply] at h8 ⊢
    split_ifs at h8 ⊢ with hij
    · linear_combination (-Complex.I) * h8 + (Wᴴ * X * W) i j * Complex.I_sq
    · linear_combination (-Complex.I) * h8 + (Wᴴ * X * W) i j * Complex.I_sq
  have eL : Wᴴ * (u * (1 + X)) * W = (Wᴴ * u * W) * (1 + Wᴴ * X * W) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W Wᴴ, hW2, Matrix.one_mul]
  have eR : Wᴴ * (1 - X) * W = 1 - Wᴴ * X * W := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [hW1]
  have h := congrArg (fun M => Wᴴ * M * W) key
  try simp only at h
  rw [eL, eR, hY, hu, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul] at h
  have hent : ∀ i j, ζ * (Wᴴ * m * W) i j * (1 - Complex.I * (ev j : ℂ)) =
      if i = j then 1 + Complex.I * (ev i : ℂ) else 0 := by
    intro i j
    have h9 := congrFun (congrFun h i) j
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul] at h9
    split_ifs at h9 ⊢ with hij
    · subst hij; linear_combination h9
    · linear_combination h9
  have hc : ∀ i, (1 - Complex.I * (ev i : ℂ)) ≠ 0 := by
    intro i h0
    have := congrArg Complex.re h0
    simp at this
  have hc' : ∀ i, (1 + Complex.I * (ev i : ℂ)) ≠ 0 := by
    intro i h0
    have := congrArg Complex.re h0
    simp at this
  refine ⟨W, fun i => (1 + Complex.I * (ev i : ℂ)) / (ζ * (1 - Complex.I * (ev i : ℂ))), hW1, hW2,
    fun i => ?_, ?_⟩
  · have ha : starRingEnd ℂ (1 + Complex.I * (ev i : ℂ)) = 1 - Complex.I * (ev i : ℂ) := by
      simp [Complex.conj_ofReal] <;> ring
    have hb : starRingEnd ℂ (1 - Complex.I * (ev i : ℂ)) = 1 + Complex.I * (ev i : ℂ) := by
      simp [Complex.conj_ofReal] <;> ring
    simp only [map_div₀, map_mul, ha, hb]
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hζ0' (hc' i)) (mul_ne_zero hζ0 (hc i)))]
    linear_combination (-((1 - Complex.I * (ev i : ℂ)) * (1 + Complex.I * (ev i : ℂ)))) * hζ1
  · have hm' : Wᴴ * m * W = Matrix.diagonal
        (fun i => (1 + Complex.I * (ev i : ℂ)) / (ζ * (1 - Complex.I * (ev i : ℂ)))) := by
      ext i j
      rw [Matrix.diagonal_apply]
      split_ifs with hij
      · subst hij
        have h10 := hent i i
        rw [if_pos rfl] at h10
        rw [eq_div_iff (mul_ne_zero hζ0 (hc i))]
        linear_combination h10
      · have h10 := hent i j
        rw [if_neg hij] at h10
        simpa [hζ0, hc j] using h10
    calc m = W * Wᴴ * m * (W * Wᴴ) := by rw [hW2, Matrix.one_mul, Matrix.mul_one]
      _ = W * (Wᴴ * m * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hm']

theorem exists_transpose_mat (m : Matrix S S ℂ) (hm : mᴴ * m = 1) (w : S → ℂ) (hw : ∀ s, conj (w s) = w s) :
    ∃ U : Matrix S S ℂ, Uᴴ * U = 1 ∧ U *ᵥ w = w ∧ m.map (starRingEnd ℂ) * U * m = U := by
  obtain ⟨V, d, hV1, hV2, hd, rfl⟩ := unitary_exists_diagonalization m hm
  obtain ⟨x, hx⟩ : ∃ x : S → ℂ, x = Vᴴ *ᵥ w := ⟨_, rfl⟩
  obtain ⟨p, hp, hpx⟩ : ∃ p : S → ℂ, (∀ i, starRingEnd ℂ (p i) * p i = 1) ∧
      ∀ i, p i * (‖x i‖ : ℂ) = x i := by
    refine ⟨fun i => Complex.exp (Complex.arg (x i) * Complex.I), fun i => ?_, fun i => ?_⟩
    · rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    · rw [mul_comm]
      first
        | exact Complex.norm_mul_exp_arg_mul_I (x i)
        | exact Complex.abs_mul_exp_arg_mul_I (x i)
  obtain ⟨e, he⟩ : ∃ e : S → ℂ, ∀ i, e i = starRingEnd ℂ (p i) ^ 2 := ⟨_, fun _ => rfl⟩
  have he1 : ∀ i, e i * x i = starRingEnd ℂ (x i) := by
    intro i
    have hcx : starRingEnd ℂ (x i) = starRingEnd ℂ (p i) * (‖x i‖ : ℂ) := by
      conv_lhs => rw [← hpx i]
      rw [map_mul, Complex.conj_ofReal]
    rw [hcx, he i]
    linear_combination (-(starRingEnd ℂ (p i)) ^ 2) * hpx i + (starRingEnd ℂ (p i) * (‖x i‖ : ℂ)) * hp i
  have he2 : ∀ i, starRingEnd ℂ (e i) * e i = 1 := by
    intro i
    rw [he i]
    simp only [map_pow, starRingEnd_self_apply]
    linear_combination (starRingEnd ℂ (p i) * p i + 1) * hp i
  have hVT : Vᴴ.map (starRingEnd ℂ) = Vᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hcVH : (V.map (starRingEnd ℂ))ᴴ = Vᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hcV : Vᵀ * V.map (starRingEnd ℂ) = 1 := by
    have h : (Vᴴ * V).map (starRingEnd ℂ) = 1 := by
      rw [hV1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rwa [Matrix.map_mul, hVT] at h
  have hEE : (Matrix.diagonal e)ᴴ * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact he2 i
  have hVx : V *ᵥ x = w := by rw [hx, Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec]
  have hEx : Matrix.diagonal e *ᵥ x = fun i => starRingEnd ℂ (x i) := by
    funext i
    rw [Matrix.mulVec_diagonal]
    exact he1 i
  have hmv : ∀ (M : Matrix S S ℂ) (v : S → ℂ),
      M.map (starRingEnd ℂ) *ᵥ (fun i => starRingEnd ℂ (v i)) = fun i => starRingEnd ℂ ((M *ᵥ v) i) := by
    intro M v
    funext i
    first
      | simp [Matrix.mulVec, dotProduct, map_sum]
      | simp [Matrix.mulVec, Matrix.dotProduct, map_sum]
  refine ⟨V.map (starRingEnd ℂ) * Matrix.diagonal e * Vᴴ, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hcVH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ, hcV, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal e)ᴴ, hEE,
      Matrix.one_mul, hV2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hx, hEx, hmv, hVx]
    funext i
    exact hw i
  · rw [Matrix.map_mul, Matrix.map_mul, hVT, Matrix.diagonal_map (map_zero _)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ, hcV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hV1, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal e) (Matrix.diagonal d), Matrix.diagonal_mul_diagonal,
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    have hde : ∀ i, starRingEnd ℂ (d i) * (e i * d i) = e i := fun i => by linear_combination e i * hd i
    simp only [hde]

end TransM

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace TransM

variable {k r : ℕ}

def pK (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (k r : ℕ) : DecidablePred (pK k r) := fun i => inferInstanceAs (Decidable (r ≤ i.val ∧ i.val < r + k))

def Qm (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    Mat k r :=
  Matrix.reindex (Equiv.sumCompl (pK k r)) (Equiv.sumCompl (pK k r)) (fromBlocks a 0 0 b)

theorem Qm_apply (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ)
    (i j : Fin (2 * r + k + 1)) :
    Qm a b i j = if hi : pK k r i then (if hj : pK k r j then a ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else (if hj : pK k r j then 0 else b ⟨i, hi⟩ ⟨j, hj⟩) := by
  simp only [Qm, Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hi : pK k r i <;> by_cases hj : pK k r j <;>
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg]

theorem Qm_mul (a c : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b d : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    Qm a b * Qm c d = Qm (a * c) (b * d) := by
  simp only [Qm, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem Qm_conjTranspose (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    (Qm a b)ᴴ = Qm aᴴ bᴴ := by
  simp [Qm, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem Qm_map (a : Matrix {i // pK k r i} {i // pK k r i} ℂ) (b : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ) :
    (Qm a b).map (starRingEnd ℂ) = Qm (a.map (starRingEnd ℂ)) (b.map (starRingEnd ℂ)) := by
  simp only [Qm, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

theorem Qm_one : Qm (1 : Matrix {i // pK k r i} {i // pK k r i} ℂ) 1 = (1 : Mat k r) := by
  simp [Qm, Matrix.reindex_apply, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem Qm_left_inj {a c : Matrix {i // pK k r i} {i // pK k r i} ℂ} {b d : Matrix {i // ¬ pK k r i} {i // ¬ pK k r i} ℂ}
    (h : Qm a b = Qm c d) : a = c := by
  have h' := (Matrix.reindex (Equiv.sumCompl (pK k r)) (Equiv.sumCompl (pK k r))).injective h
  exact (Matrix.fromBlocks_inj.mp h').1

theorem Hpk_left (i j : Fin (2 * r + k + 1)) (hi : pK k r i) : Hpk k r i j = if i = j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := hi
  unfold Hpk
  by_cases hij : i = j
  · subst hij
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega), if_pos rfl]
  · rw [if_neg (by omega), if_neg (fun h => by have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega),
      if_neg (fun h => hij h.2.2), if_neg hij]

theorem Hpk_right (i j : Fin (2 * r + k + 1)) (hj : pK k r j) : Hpk k r i j = if i = j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := hj
  unfold Hpk
  by_cases hij : i = j
  · subst hij
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega), if_pos rfl]
  · rw [if_neg (fun h => by have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega), if_neg (by omega),
      if_neg (fun h => hij h.2.2), if_neg hij]

theorem Hpk_eq_Qm : Hpk k r = Qm 1 ((Hpk k r).submatrix Subtype.val Subtype.val) := by
  ext i j
  rw [Qm_apply]
  by_cases hi : pK k r i
  · rw [Hpk_left i j hi, dif_pos hi]
    by_cases hj : pK k r j
    · rw [dif_pos hj, Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    · rw [dif_neg hj, if_neg]
      rintro rfl
      exact hj hi
  · rw [dif_neg hi]
    by_cases hj : pK k r j
    · rw [dif_pos hj, Hpk_right i j hj, if_neg]
      rintro rfl
      exact hi hj
    · rw [dif_neg hj]
      rfl

theorem col_fix (x : Mat k r) (j : Fin (2 * r + k + 1)) (h : x *ᵥ bvec j = bvec j) (i : Fin (2 * r + k + 1)) :
    x i j = if i = j then 1 else 0 := by
  rw [← InvGrp.col_apply x i j, h]
  simp [bvec, Pi.single_apply]

theorem row_fix (x : Mat k r) (hx : x ∈ UH (Hpk k r)) (i j : Fin (2 * r + k + 1)) (s : ℂ) (hs : s ≠ 0)
    (hcol : x *ᵥ bvec j = bvec j) (hH : ∀ l, Hpk k r j l = if l = i then s else 0) (l : Fin (2 * r + k + 1)) :
    x i l = if i = l then 1 else 0 := by
  have hc := col_fix x j hcol
  have hrow : ∀ n, (xᴴ * Hpk k r) j n = Hpk k r j n := by
    intro n
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [Matrix.conjTranspose_apply, hc]
    · intro m _ hm
      simp [Matrix.conjTranspose_apply, hc, hm]
    · simp
  have key : (xᴴ * Hpk k r * x) j l = s * x i l := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hrow, hH, if_pos rfl]
    · intro n _ hn
      rw [hrow, hH, if_neg hn, zero_mul]
    · simp
  have hx2 : xᴴ * Hpk k r * x = Hpk k r := hx
  rw [hx2, hH] at key
  by_cases hil : i = l
  · subst hil
    rw [if_pos rfl] at key
    rw [if_pos rfl]
    exact mul_left_cancel₀ hs (key.symm.trans (mul_one s).symm)
  · rw [if_neg (Ne.symm hil)] at key
    rw [if_neg hil]
    exact (mul_eq_zero.mp key.symm).resolve_left hs

theorem Hpk_esI (a : Fin r) (l : Fin (2 * r + k + 1)) : Hpk k r (esI k r a) l = if l = eI k r a then 1 else 0 := by
  have he : (esI k r a).val = 2 * r + k - a.val := rfl
  have he2 : (eI k r a).val = a.val := rfl
  have ha := a.isLt
  unfold Hpk
  by_cases hl : l = eI k r a
  · have hv : l.val = a.val := by rw [hl, he2]
    rw [if_neg (by omega), if_pos (by omega), if_pos hl]
  · have hv : l.val ≠ a.val := fun h => hl (Fin.ext (h.trans he2.symm))
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => by obtain ⟨_, h2, _⟩ := h; omega), if_neg hl]

theorem Hpk_eI (a : Fin r) (l : Fin (2 * r + k + 1)) : Hpk k r (eI k r a) l = if l = esI k r a then 1 else 0 := by
  have he : (esI k r a).val = 2 * r + k - a.val := rfl
  have he2 : (eI k r a).val = a.val := rfl
  have ha := a.isLt
  have hlt := l.isLt
  unfold Hpk
  by_cases hl : l = esI k r a
  · have hv : l.val = 2 * r + k - a.val := by rw [hl, he]
    rw [if_pos (by omega), if_pos hl]
  · have hv : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext (h.trans he.symm))
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => by obtain ⟨h1, _, _⟩ := h; omega), if_neg hl]

theorem Hpk_wlast (l : Fin (2 * r + k + 1)) :
    Hpk k r (wI k r (Fin.last k)) l = if l = wI k r (Fin.last k) then -1 else 0 := by
  have hw : (wI k r (Fin.last k)).val = r + k := rfl
  unfold Hpk
  by_cases hl : l = wI k r (Fin.last k)
  · subst hl
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos hw, if_pos rfl]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hl h.2.2.symm), if_neg hl]

theorem not_pK_cases (j : Fin (2 * r + k + 1)) (hj : ¬ pK k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) ∨ j = wI k r (Fin.last k) := by
  unfold pK at hj
  have hjlt := j.isLt
  by_cases h1 : j.val < r
  · exact Or.inl ⟨⟨j.val, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : j.val = r + k
    · exact Or.inr (Or.inr (Fin.ext h2))
    · refine Or.inr (Or.inl ⟨⟨2 * r + k - j.val, by omega⟩, Fin.ext ?_⟩)
      show j.val = 2 * r + k - (2 * r + k - j.val)
      omega

private theorem mulVec_bvec_eq_of_fix_e_es_last_not_pK (x : Mat k r)
    (he : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hl : x *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (j : Fin (2 * r + k + 1)) (hj : ¬ pK k r j) : x *ᵥ bvec j = bvec j := by
  rcases not_pK_cases j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact (he a).1
  · exact (he a).2
  · exact hl

private theorem apply_eq_ite_of_fix_e_es_last_not_pK (x : Mat k r) (hx : x ∈ UH (Hpk k r))
    (he : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hl : x *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (i : Fin (2 * r + k + 1)) (hi : ¬ pK k r i) (l : Fin (2 * r + k + 1)) :
    x i l = if i = l then 1 else 0 := by
  rcases not_pK_cases i hi with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact row_fix x hx (eI k r a) (esI k r a) 1 one_ne_zero (he a).2 (Hpk_esI a) l
  · exact row_fix x hx (esI k r a) (eI k r a) 1 one_ne_zero (he a).1 (Hpk_eI a) l
  · exact row_fix x hx _ _ (-1) (neg_ne_zero.mpr one_ne_zero) hl (fun l => Hpk_wlast l) l

theorem eq_Qm (x : Mat k r) (hx : x ∈ UH (Hpk k r))
    (he : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hl : x *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))) :
    x = Qm (x.submatrix Subtype.val Subtype.val) 1 := by
  ext i j
  rw [Qm_apply]
  by_cases hi : pK k r i
  · rw [dif_pos hi]
    by_cases hj : pK k r j
    · rw [dif_pos hj]
      rfl
    · rw [dif_neg hj, col_fix x j (mulVec_bvec_eq_of_fix_e_es_last_not_pK x he hl j hj) i, if_neg]
      rintro rfl
      exact hj hi
  · rw [dif_neg hi, apply_eq_ite_of_fix_e_es_last_not_pK x hx he hl i hi j]
    by_cases hj : pK k r j
    · rw [dif_pos hj, if_neg]
      rintro rfl
      exact hi hj
    · rw [dif_neg hj, Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h]

theorem unitary_of_Qm (m : Matrix {i // pK k r i} {i // pK k r i} ℂ) (hx : Qm m 1 ∈ UH (Hpk k r)) : mᴴ * m = 1 := by
  have h : (Qm m 1)ᴴ * Hpk k r * Qm m 1 = Hpk k r := hx
  rw [Hpk_eq_Qm, Qm_conjTranspose, Qm_mul, Qm_mul] at h
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h
  exact Qm_left_inj h

theorem Qm_mem_UH (U : Matrix {i // pK k r i} {i // pK k r i} ℂ) (hU : Uᴴ * U = 1) : Qm U 1 ∈ UH (Hpk k r) := by
  show (Qm U 1)ᴴ * Hpk k r * Qm U 1 = Hpk k r
  rw [Hpk_eq_Qm, Qm_conjTranspose, Qm_mul, Qm_mul]
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, hU]

theorem Qm_fix_off (U : Matrix {i // pK k r i} {i // pK k r i} ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ pK k r j) :
    Qm U 1 *ᵥ bvec j = bvec j := by
  ext i
  rw [InvGrp.col_apply, Qm_apply]
  simp only [bvec, Pi.single_apply]
  by_cases hi : pK k r i
  · rw [dif_pos hi, dif_neg hj, if_neg]
    rintro rfl
    exact hj hi
  · rw [dif_neg hi, dif_neg hj, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]

theorem Qm_fix_vec (U : Matrix {i // pK k r i} {i // pK k r i} ℂ) (j : Fin (2 * r + k + 1))
    (hU : U *ᵥ (fun s => bvec j s.1) = fun s => bvec j s.1) : Qm U 1 *ᵥ bvec j = bvec j := by
  by_cases hj : pK k r j
  · ext i
    rw [InvGrp.col_apply, Qm_apply]
    have h2 : (fun s : {i // pK k r i} => bvec j s.1) = Pi.single ⟨j, hj⟩ 1 := by
      ext s
      simp only [bvec, Pi.single_apply, Subtype.ext_iff]
    rw [h2] at hU
    by_cases hi : pK k r i
    · rw [dif_pos hi, dif_pos hj]
      have := congrFun hU ⟨i, hi⟩
      simp [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp [bvec, Pi.single_apply, this]
    · rw [dif_neg hi, dif_pos hj]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      rintro rfl
      exact hi hj
  · exact Qm_fix_off U j hj

end TransM

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stTransM (h : UnitaryGroupStructuralFacts) : StTransM := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩ := hB2
  intro k r Wp _ _ _ D X _ _ γ hγ y hy
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  set E := embWb k r γ with hEdef
  have hEiG : E⁻¹ ∈ GV k r := hG.inv_mem _ hEG
  have hc : ∀ B : Mat k r, E⁻¹ * (E * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left E B hE
  have hEE : ∀ v, E⁻¹ *ᵥ (E *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  have hEfix : ∀ j, ¬ InvGrp.isW k r j → E *ᵥ bvec j = bvec j := fun j hj =>
    InvGrp.embWb_fix_offW γ _ (InvGrp.bvec_offW j hj)
  have hEifix : ∀ j, ¬ InvGrp.isW k r j → E⁻¹ *ᵥ bvec j = bvec j := fun j hj =>
    InvGrp.embWb_inv_fix_offW hE _ (InvGrp.bvec_offW j hj)
  have hwl : ¬ InvGrp.isW k r (wI k r (Fin.last k)) → False := fun h => h ⟨by simp [wI], by simp [wI]⟩
  set b := bvec (wI k r (Fin.last k)) with hbdef
  have hs0 : ((Real.sqrt (Tz k r D.z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr D.T_pos).ne'
  have hzE : D.z = ((Real.sqrt (Tz k r D.z) : ℝ) : ℂ) • (E *ᵥ b) := by
    rw [hγ.2, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hs0, one_smul]

  set x := E⁻¹ * y * E with hxdef
  have hxG : x ∈ GV k r := hG.mul_mem _ (hG.mul_mem _ hEiG _ hy.1) _ hEG
  have hxv : ∀ v, x *ᵥ v = E⁻¹ *ᵥ (y *ᵥ (E *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hxe : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro a
    constructor
    · rw [hxv, hEfix _ (InvGrp.not_isW_eI a), (hy.2.1 a).1, hEifix _ (InvGrp.not_isW_eI a)]
    · rw [hxv, hEfix _ (InvGrp.not_isW_esI a), (hy.2.1 a).2, hEifix _ (InvGrp.not_isW_esI a)]
  have hxl : x *ᵥ b = b := by
    rw [hxv, hγ.2, Matrix.mulVec_smul, hy.2.2, ← hγ.2, hEE]
  have hxeq := TransM.eq_Qm x hxG hxe hxl
  set m := x.submatrix (Subtype.val : {i // TransM.pK k r i} → _) Subtype.val with hmdef
  have hm : mᴴ * m = 1 := TransM.unitary_of_Qm m (hxeq ▸ hxG)
  have hw : ∀ s : {i // TransM.pK k r i}, conj (bvec (wI k r 0) s.1) = bvec (wI k r 0) s.1 := by
    intro s
    simp only [bvec, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨U, hU1, hUw, hUc⟩ := TransM.exists_transpose_mat m hm (fun s => bvec (wI k r 0) s.1) hw
  set PU := TransM.Qm U 1 with hPUdef
  have hPUG : PU ∈ GV k r := TransM.Qm_mem_UH U hU1
  have hPUs : TransM.Qm Uᴴ 1 * PU = 1 := by
    rw [hPUdef, TransM.Qm_mul, hU1, Matrix.one_mul, TransM.Qm_one]
  have hPUs' : PU * TransM.Qm Uᴴ 1 = 1 := by
    rw [hPUdef, TransM.Qm_mul, mul_eq_one_comm.mp hU1, Matrix.one_mul, TransM.Qm_one]
  have hkey : x.map (starRingEnd ℂ) * PU * x = PU := by
    rw [hxeq, TransM.Qm_map, hPUdef, TransM.Qm_mul, TransM.Qm_mul, hUc]
    simp
  have hyx : y = E * x * E⁻¹ := by
    rw [hxdef]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left E _ hE, Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
  have hnotK : ∀ j, ¬ InvGrp.isW k r j → ¬ TransM.pK k r j := fun j hj hK =>
    hj ⟨hK.1, by have := hK.2; omega⟩
  have hnotKl : ¬ TransM.pK k r (wI k r (Fin.last k)) := fun hK => by
    have := hK.2; simp [wI] at this
  refine ⟨E * PU * E⁻¹, ⟨⟨hG.mul_mem _ (hG.mul_mem _ hEG _ hPUG) _ hEiG, fun a => ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEifix _ (InvGrp.not_isW_eI a),
      TransM.Qm_fix_off U _ (hnotK _ (InvGrp.not_isW_eI a)), hEfix _ (InvGrp.not_isW_eI a)]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEifix _ (InvGrp.not_isW_esI a),
      TransM.Qm_fix_off U _ (hnotK _ (InvGrp.not_isW_esI a)), hEfix _ (InvGrp.not_isW_esI a)]
  · conv_lhs => rw [hzE]
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEE, TransM.Qm_fix_off U _ hnotKl, ← hzE]
  · show (E * PU * E⁻¹) *ᵥ (E *ᵥ bvec (wI k r 0)) = E *ᵥ bvec (wI k r 0)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEE, TransM.Qm_fix_vec U _ hUw]
  · have hinv : (E * PU * E⁻¹)⁻¹ = E * TransM.Qm Uᴴ 1 * E⁻¹ := by
      apply Matrix.inv_eq_left_inv
      simp only [Matrix.mul_assoc, hc]
      rw [← Matrix.mul_assoc (TransM.Qm Uᴴ 1) PU, hPUs, Matrix.one_mul, Matrix.mul_nonsing_inv _ hE]
    have hgb : gbar k r γ y = E * x.map (starRingEnd ℂ) * E⁻¹ := rfl
    show (gbar k r γ y)⁻¹ = _
    rw [hinv, hgb]
    apply Matrix.inv_eq_right_inv
    rw [hyx]
    simp only [Matrix.mul_assoc, hc]
    rw [← Matrix.mul_assoc (x.map (starRingEnd ℂ)) PU, ← Matrix.mul_assoc (x.map (starRingEnd ℂ) * PU) x, hkey,
      ← Matrix.mul_assoc PU, hPUs', Matrix.one_mul, Matrix.mul_nonsing_inv _ hE]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
