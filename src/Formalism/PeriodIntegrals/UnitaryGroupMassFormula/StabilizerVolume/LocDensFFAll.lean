import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF

section
noncomputable section

namespace PI.VolStabS

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h v hv
    funext j
    refine h v ?_ j
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro h g hg i
    have hPg : P *ᵥ g = 0 := by
      funext r
      have := congrFun hg r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    exact congrFun (h g hPg) i

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact (linInd_cols_iff P).1 hP v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun D => D * P
      map_add' := fun D E => Matrix.add_mul D E P
      map_smul' := fun c D => Matrix.smul_mul c D P }
  have hf : ∀ D, f D = D * P := fun D => rfl
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro E
    exact ⟨E * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * M - a * a := by omega
  have e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W => ⟨W.1 - L, by rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun D => ⟨D.1 + L, by
        have hD := D.2
        rw [LinearMap.mem_ker, hf] at hD
        rw [Matrix.add_mul, hD, hL, zero_add]⟩
      left_inv := fun W => by ext1; simp
      right_inv := fun D => by ext1; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker, Nat.mul_sub_left_distrib]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  unfold ffH
  simp [Prod.fst_sum, swapR]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]

private theorem ffGram_apply (J : Matrix (Fin M) (Fin M) (k × k))
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    ffGram (swapR k) J X r s = ffH (swapR k) J (X r) (X s) := by
  first
  | rfl
  | simp [ffGram]
  | (unfold ffGram; simp)

private theorem fst_ffGram_eq_V1_mul_map_fst (J : Matrix (Fin M) (Fin M) (k × k)) (X : Fin a → Fin M → k × k)
    (r s : Fin a) :
    (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s = (ffGram (swapR k) J X r s).1 := by
  rw [ffGram_apply, ffH_fst]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, V1, U1, Finset.sum_mul]
  exact Finset.sum_comm

private theorem snd_ffGram_eq_fst_ffGram_swap (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
  rw [ffGram_apply, ffGram_apply, ffH_fst, ffH_snd]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have h := congrArg Prod.fst (hJ x y)
  rw [Prod.fst_swap] at h
  rw [h]
  ring

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  constructor
  · rintro rfl
    refine Matrix.ext fun r s => ?_
    rw [fst_ffGram_eq_V1_mul_map_fst]
    rfl
  · intro h
    have hf : ∀ r s, (ffGram (swapR k) J X r s).1 = (T r s).1 := fun r s => by
      rw [← fst_ffGram_eq_V1_mul_map_fst]
      exact congrFun (congrFun h r) s
    refine Matrix.ext fun r s => Prod.ext (hf r s) ?_
    rw [snd_ffGram_eq_fst_ffGram_swap J hJ X, hf s r]
    have h2 := congrArg Prod.snd (hT r s)
    rw [Prod.snd_swap] at h2
    exact h2

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have hJ1 : IsUnit (J.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hJd).1
    rwa [show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J] at h1
  have hT1 : IsUnit (T.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hTd).1
    rwa [show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T] at h1
  have e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃
      {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} :=
    { toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by
        have h := (gram_iff J hJ T hT X.1).1 X.2
        show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩
      invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
          (T.map Prod.fst * WP.1.1) r i), by
        rw [gram_iff J hJ T hT]
        have hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ := rfl
        have hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1 := rfl
        rw [hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst),
          Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext r i
        apply Prod.ext
        · show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul,
            Matrix.transpose_transpose]
          rfl
        · show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]
          rfl
      right_inv := fun WP => by
        apply Subtype.ext
        apply Prod.ext
        · show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]
        · show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2
          rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1,
            Matrix.one_mul] }
  rw [Nat.card_congr e, card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  unfold FFSplit
  intro k _ _ M a ha J hJ hJd T hT hTd
  have h := FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd
  simp only [FiniteFieldSplitting.swapR] at h
  rw [h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : 1 ≤ Nat.card k := Nat.card_pos
  have hi : (i : ℕ) ≤ M := by have := i.isLt; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : |∏ j ∈ s, (1 + δ j)| ≤ 1 + t * (2 ^ s.card - 1) := by
      have := abs_sub_abs_le_abs_sub (∏ j ∈ s, (1 + δ j)) 1
      rw [abs_one] at this
      linarith
    have hpow : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    have h2 : |δ a * ∏ j ∈ s, (1 + δ j)| ≤ t * (1 + t * (2 ^ s.card - 1)) := by
      rw [abs_mul]
      exact mul_le_mul (h a) h1 (abs_nonneg _) ht0
    have h3 : (1 + δ a) * ∏ j ∈ s, (1 + δ j) - 1 =
        (∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j) := by ring
    rw [h3]
    have h4 : t * (t * (2 ^ s.card - 1)) ≤ t * (2 ^ s.card - 1) := by
      apply mul_le_mul_of_nonneg_left _ ht0
      nlinarith
    calc |(∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j)|
        ≤ |∏ j ∈ s, (1 + δ j) - 1| + |δ a * ∏ j ∈ s, (1 + δ j)| := abs_add_le _ _
      _ ≤ t * (2 ^ s.card - 1) + t * (1 + t * (2 ^ s.card - 1)) := add_le_add ih h2
      _ ≤ t * (2 ^ (s.card + 1) - 1) := by
          rw [pow_succ]
          nlinarith

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have hq0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have h1 := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 := pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.add_sub_cancel_left]
  symm
  apply Nat.sub_eq_of_eq_add
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : a + 1 + d - a = d + 1 := by omega
    rw [e1]
    have e2 : 2 * (a + 1 + d) * a - a ^ 2 = a ^ 2 + 2 * a * (d + 1) := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e3 : 2 * (a + 1 + d) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * (a + 1) * d := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e2, e3]
    have e4 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
    rw [e4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hqM : q ^ M ≠ 0 := pow_ne_zero _ hq
  rw [← exp_id M a ha, pow_add]
  have h1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hA : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have hB : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  rw [mul_comm (q ^ (M * a)), mul_assoc, mul_div_assoc, div_self (mul_ne_zero hA hB), mul_one]

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have hs : ∑ j : Fin a, (2 * (M - (j : ℕ)) - 1) = 2 * M * a - a ^ 2 :=
    (Fin.sum_univ_eq_sum_range (fun j => 2 * (M - j) - 1) a).trans (sum_exp M a ha)
  have hden : q ^ (2 * M * a - a ^ 2) = ∏ j : Fin a, q ^ (2 * (M - (j : ℕ)) - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, hs]
  rw [hden, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : q ^ (2 * (M - (j : ℕ)) - 1) ≠ 0 := pow_ne_zero _ hq
  rw [sub_div, div_self hB]
  ring

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hi := i.isLt
  rw [abs_neg, abs_of_nonneg (div_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _))]
  have hM : M = (i : ℕ) + (M - i) := by omega
  have h1 : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    conv_lhs => rw [hM, pow_add]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), inv_pow, one_div]
  rw [h1]
  exact inv_pow_le q hq (M - i) (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hj := j.isLt
  rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos hq0 _), abs_of_pos (pow_pos hq0 _)]
  have he : 2 * (M - (j : ℕ)) - 1 = (M - (j : ℕ) - 1) + (M - (j : ℕ)) := by omega
  rw [he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), one_div, ← inv_pow]
  exact inv_pow_le q hq _ (by omega)

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) ?_
  intro X
  have key : ffGram (FiniteFieldSplitting.swapR k) (J.map e)
      ((Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) X) =
        (ffGram (σ : K →+* K) J X).map e := by
    funext i j
    show ∑ a', ∑ b, (e (X i a')).swap * e (J a' b) * e (X j b) =
      e (∑ a', ∑ b, σ (X i a') * J a' b * X j b)
    rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, he]
  rw [key]
  constructor
  · intro h
    rw [h]
  · intro h
    ext i j
    exact e.injective (congrFun (congrFun h i) j)

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by linarith
  have haM : a ≤ M := by omega
  rcases hσ.2 with ⟨hF, hrank, hne⟩ | ⟨e, he⟩
  · letI : Field K := hF.toField
    have hc := hI k K σ hσ.1 hrank hne h2 M a haM J hJ hJd T hT hTd
    rw [hc, FiniteFieldCounting.inert_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun j => FiniteFieldCounting.inert_delta M a ha _ hq1 j)
  · have hc := FiniteFieldCounting.card_transport σ e he J T
    have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have h := hJd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hTd' : IsUnit (T.map e).det := by
      have h := hTd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hs : (Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} : ℝ) =
        (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
          (Nat.card k : ℝ) ^ (a * (M - a)) := hS k M a haM (J.map e) hJ' hJd' (T.map e) hT' hTd'
    rw [hc, hs, FiniteFieldCounting.split_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun i => FiniteFieldCounting.split_delta M a ha _ hq1 i)

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm z x, ← hs.herm z y]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]

theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0

theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z :=
  (hs.lin x).map_sub y z

theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := (hs.herm x x).symm

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y

theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  have hq := hs.toIsSq
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key := H (x + (h x y)⁻¹ • y)
  simp only [hq.add_right, hq.add_left, hq.smul_right, hq.smul_left, H x, H y,
    hq.herm x y] at key
  have e1 : σ (h x y)⁻¹ * σ (h x y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hy, map_one]
  have e2 : (h x y)⁻¹ * h x y = 1 := inv_mul_cancel₀ hy
  exact h2 (by linear_combination key - e1 - e2)

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : Function.Surjective (hs.lin e) := fun c =>
    ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he,
      mul_one]⟩
  have := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · rw [map_smul, IsSq.lin_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h2 i)
  · intro j _ hji
    rw [map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  simp only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]
  ring

end basic

theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _ _ _ h _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hq := hs.toIsSq
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    obtain ⟨g, hg1, hg2⟩ := ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_perp hq e (g j)).1 (g j).2
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun hh => hij (by rw [hh]))
    · intro i
      induction i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i

end PI.VolStabS.FFHS
end
end

section
noncomputable section

namespace PI.VolStabS.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right]
  rw [mul_comm (h e e)⁻¹ (h e x), mul_assoc, inv_mul_cancel₀ he, mul_one, sub_self]

private theorem natCard_sigma_eq_sum {α : Type} [Fintype α] {β : α → Type} [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  exact Nat.card_sigma

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  have hcoef : ∀ (t : K) (w : V), h e w = 0 → (h e e)⁻¹ * h e (t • e + w) = t := by
    intro t w hw
    rw [hs.add_right, hs.smul_right, hw, add_zero]
    rw [mul_comm t, ← mul_assoc, inv_mul_cancel₀ he, one_mul]
  let E : {x : V // h x x = c} ≃
      Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨(h e e)⁻¹ * h e x.1,
        ⟨⟨x.1 - ((h e e)⁻¹ * h e x.1) • e, perp_sub_mem hs e x.1 he⟩, by
          have hw := (mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)
          have key := decomp_val hs e _ hw ((h e e)⁻¹ * h e x.1)
          have hx : ((h e e)⁻¹ * h e x.1) • e + (x.1 - ((h e e)⁻¹ * h e x.1) • e) = x.1 := by
            abel
          rw [hx, x.2] at key
          show h (x.1 - ((h e e)⁻¹ * h e x.1) • e) (x.1 - ((h e e)⁻¹ * h e x.1) • e) = _
          linear_combination -key⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
          rw [decomp_val hs e _ ((mem_perp hs e _).1 p.2.1.2) p.1, p.2.2]
          ring⟩
      left_inv := fun x => Subtype.ext (by
          show ((h e e)⁻¹ * h e x.1) • e + (x.1 - ((h e e)⁻¹ * h e x.1) • e) = x.1
          abel)
      right_inv := by
        rintro ⟨t, ⟨w, hw⟩, hww⟩
        have hw0 := (mem_perp hs e w).1 hw
        refine Sigma.subtype_ext (hcoef t w hw0) ?_
        apply Subtype.ext
        show t • e + w - ((h e e)⁻¹ * h e (t • e + w)) • e = w
        rw [hcoef t w hw0]
        abel }
  rw [Nat.card_congr E, natCard_sigma_eq_sum]

private theorem natCard_subtype_eq_card_filter {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] : Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  have hQ : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0.ne'
  have z1 : ∀ n : ℕ, (q : ℝ) ^ (2 * (n : ℤ) - 1) = (q : ℝ) ^ (2 * n) * (q : ℝ)⁻¹ := by
    intro n
    rw [zpow_sub₀ hQ, zpow_one, div_eq_mul_inv,
      show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by omega, zpow_natCast]
  have z2 : ∀ n : ℕ, (q : ℝ) ^ ((n : ℤ) - 1) = (q : ℝ) ^ n * (q : ℝ)⁻¹ := by
    intro n
    rw [zpow_sub₀ hQ, zpow_one, div_eq_mul_inv, zpow_natCast]
  intro m
  induction m with
  | zero =>
    intro V i1 i2 i3 h hh hm c hc
    have : Subsingleton V := by
      rcases subsingleton_or_nontrivial V with hV | hV
      · exact hV
      · exfalso
        have hpos : 0 < finrank K V := Module.finrank_pos
        omega
    have h00 : h 0 0 = 0 := hh.toIsSq.zero_left 0
    simp only [z1, z2]
    by_cases hc0 : c = 0
    · subst hc0
      have hcard : Nat.card {x : V // h x x = 0} = 1 := by
        have : Unique {x : V // h x x = 0} :=
          ⟨⟨⟨0, h00⟩⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
        exact Nat.card_unique
      rw [hcard, if_pos rfl, Nat.cast_one]
      have hqq : (q : ℝ) * (q : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hQ
      linear_combination -hqq
    · have hcard : Nat.card {x : V // h x x = c} = 0 := by
        have : IsEmpty {x : V // h x x = c} :=
          ⟨fun y => hc0 (by
            have hy := y.2
            rw [Subsingleton.elim y.1 0, h00] at hy
            exact hy.symm)⟩
        exact Nat.card_of_isEmpty
      rw [hcard, if_neg hc0, Nat.cast_zero]
      ring
  | succ m ih =>
    intro V i1 i2 i3 h hh hm c hc
    have hs := hh.toIsSq
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hh x hx
    have hW := perp_isHS hh e he
    have hWr : finrank K (perp hs e) = m := by
      have := finrank_perp hs e he
      omega
    have : Finite V := Module.finite_of_finite K
    have hterm : ∀ t : K, (Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} : ℝ) =
        (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1) := by
      intro t
      refine ih (perp hs e) (fun w w' : perp hs e => h w w') hW hWr _ ?_
      simp only [map_sub, map_mul, hσ, hc, hs.self_fixed]
      ring
    have hfix : σ (c * (h e e)⁻¹) = c * (h e e)⁻¹ := by
      rw [map_mul, map_inv₀, hc, hs.self_fixed]
    have hiff : ∀ t : K, c - σ t * t * h e e = 0 ↔ t * σ t = c * (h e e)⁻¹ := by
      intro t
      constructor
      · intro H
        have H' : σ t * t * h e e = c := (sub_eq_zero.1 H).symm
        rw [← H', mul_inv_cancel_right₀ he, mul_comm]
      · intro H
        rw [mul_comm (σ t) t, H, mul_assoc, inv_mul_cancel₀ he, mul_one, sub_self]
    have hcount : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      rw [← natCard_subtype_eq_card_filter, Nat.card_congr (Equiv.subtypeEquivRight hiff),
        hN _ hfix]
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp [hc0, he]
    have hsum : ∑ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
        (q : ℝ) ^ 2 * ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
          (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * (q : ℝ) *
            ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) := by
      have hpt : ∀ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
          ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
            (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * (q : ℝ) *
              (if c - σ t * t * h e e = 0 then (1 : ℝ) else 0) := by
        intro t
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_boole, Finset.sum_const, Finset.card_univ, hK, nsmul_eq_mul, Nat.cast_pow]
    rw [card_decomp hs e he c, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hterm t),
      hsum, hcount]
    simp only [z1, z2]
    split_ifs <;> ring

theorem card_diag (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  intro a
  induction a with
  | zero =>
    intro m _ V i1 i2 i3 h _ _ d _ _
    have : Unique {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} :=
      ⟨⟨⟨Fin.elim0, fun i => i.elim0⟩⟩, fun Y => Subtype.ext (funext fun i => i.elim0)⟩
    rw [Nat.card_unique, Fin.prod_univ_zero, Nat.cast_one]
  | succ a ih =>
    intro m ham V i1 i2 i3 h hh hm d hd hd0
    have hs := hh.toIsSq
    have : Finite V := Module.finite_of_finite K
    letI : Fintype V := Fintype.ofFinite V
    have hfibEq : ∀ y : V, Nat.card {Z : Fin a → V // (∀ i, h y (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} =
        Nat.card {W : Fin a → perp hs y //
          ∀ i j, h (W i) (W j) = if i = j then d i.succ else 0} := by
      intro y
      apply Nat.card_congr
      exact
        { toFun := fun Z => ⟨fun i => ⟨Z.1 i, (mem_perp hs y _).2 (Z.2.1 i)⟩, Z.2.2⟩
          invFun := fun W => ⟨fun i => (W.1 i : V),
            fun i => (mem_perp hs y _).1 (W.1 i).2, W.2⟩
          left_inv := fun Z => rfl
          right_inv := fun W => rfl }
    have hfib : ∀ y : {y : V // h y y = d 0},
        (Nat.card {Z : Fin a → V // (∀ i, h y.1 (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} : ℝ) =
          ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - 1 - j) - 1) -
            (-1) ^ (m - 1 - j) * (q : ℝ) ^ (m - 1 - j - 1)) := by
      intro y
      have hy0 : h y.1 y.1 ≠ 0 := by rw [y.2]; exact hd0 0
      rw [hfibEq y.1]
      exact ih (m - 1) (by omega) (perp hs y.1) (fun w w' : perp hs y.1 => h w w')
        (perp_isHS hh y.1 hy0)
        (by have := finrank_perp hs y.1 hy0; omega)
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    let E : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y : {y : V // h y y = d 0}, {Z : Fin a → V // (∀ i, h y.1 (Z i) = 0) ∧
          ∀ i j, h (Z i) (Z j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, (Y.2 0 0).trans (if_pos rfl)⟩,
          ⟨fun i => Y.1 i.succ, fun i => (Y.2 0 i.succ).trans (if_neg (Fin.succ_ne_zero i).symm),
            fun i j => (Y.2 i.succ j.succ).trans (by simp only [Fin.succ_inj])⟩⟩
        invFun := fun p => ⟨(Fin.cons p.1.1 p.2.1 : Fin (a + 1) → V), by
          intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j => simpa [(Fin.succ_ne_zero j).symm] using p.2.2.1 j
          | succ i =>
            induction j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hs.herm, p.2.2.1 i, map_zero]
            | succ j => simpa [Fin.succ_inj] using p.2.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (Fin.cons_self_tail Y.1)
        right_inv := by
          rintro ⟨⟨y, hy⟩, ⟨Z, hZ⟩⟩
          refine Sigma.subtype_ext (Subtype.ext (by simp)) ?_
          funext i
          simp }
    have hN0 : (Nat.card {y : V // h y y = d 0} : ℝ) =
        (q : ℝ) ^ (2 * m - 1) - (-1) ^ m * (q : ℝ) ^ (m - 1) := by
      rw [card_norm q hq0 hK hσ h2 hN m V h hh hm (d 0) (hd 0), if_neg (hd0 0),
        show (2 * (m : ℤ) - 1) = ((2 * m - 1 : ℕ) : ℤ) by omega,
        show ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast, zpow_natCast]
      ring
    have hsub : ∀ j : ℕ, m - (j + 1) = m - 1 - j := fun j => by omega
    rw [Nat.card_congr E, natCard_sigma_eq_sum, Nat.cast_sum,
      Finset.sum_congr rfl (fun y _ => hfib y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hN0, Fin.prod_univ_succ]
    congr 1
    all_goals first
      | (refine Finset.prod_congr rfl (fun j _ => ?_)
         simp only [Fin.val_succ, hsub j])
      | simp only [Fin.val_zero, Nat.sub_zero]
      | rfl

end PI.VolStabS.FFHS
end
end

section
noncomputable section

namespace PI.VolStabS.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

private theorem ffH_single_right {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K)
    (j : Fin M) :
    PI.VolStabS.ffH σ J x (Pi.single j 1) = ∑ i, σ (x i) * J i j := by
  unfold PI.VolStabS.ffH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]

theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  rw [ffH_single_right, Fintype.sum_eq_single i]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]

end matrix

private theorem isSq_comp_linearMap {K : Type} [Field K] {σ : K →+* K} {U V : Type}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {hV : V → V → K}
    (hsV : IsSq σ hV) (φ : U →ₗ[K] V) :
    IsSq σ (fun x y => hV (φ x) (φ y)) := {
  add_right x y z := by
    show hV (φ x) (φ (y + z)) = hV (φ x) (φ y) + hV (φ x) (φ z)
    rw [map_add, hsV.add_right]
  smul_right c x y := by
    show hV (φ x) (φ (c • y)) = c * hV (φ x) (φ y)
    rw [map_smul, hsV.smul_right]
  herm x y := hsV.herm (φ x) (φ y) }

theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by
  refine Nat.card_congr
    { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩
      invFun := fun Y => ⟨b.constr K Y.1, fun x y =>
        (isSq_comp_linearMap hsV (b.constr K Y.1)).ext_basis hsU b
          (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y⟩
      left_inv := fun φ => by
        apply Subtype.ext
        apply b.ext
        intro i
        simp
      right_inv := fun Y => by
        apply Subtype.ext
        funext i
        simp }

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

private theorem card_eq_card_sq_of_finrank_two (h2 : finrank k K = 2) :
    Fintype.card K = Fintype.card k ^ 2 := by
  rw [← h2]
  exact Module.card_eq_pow_finrank

private theorem add_pow_card_eq_add_pow_card (a b : K) :
    (a + b) ^ Fintype.card k = a ^ Fintype.card k + b ^ Fintype.card k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hprime, hn⟩ := FiniteField.card k p
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [hn]
  exact add_pow_char_pow a b p (n : ℕ)

private theorem mem_range_algebraMap_of_pow_card_eq (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hP : (X ^ Fintype.card k - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hsub : Finset.univ.image (algebraMap k K) ⊆
      (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hcard : (X ^ Fintype.card k - X : K[X]).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap k K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
    calc _ ≤ Multiset.card (X ^ Fintype.card k - X : K[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card k - X : K[X]).natDegree := card_roots' _
      _ = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : d ∈ (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, hd, sub_self]
  rw [← heq] at hmem
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
  exact ⟨y, hy⟩

theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hfix : ∀ c : K, c ^ Fintype.card k = c → σ c = c := by
    intro c hc
    obtain ⟨d0, rfl⟩ := mem_range_algebraMap_of_pow_card_eq c hc
    exact σ.commutes d0
  have hdich : ∀ x : K, σ x = x ∨ σ x = x ^ Fintype.card k := by
    intro x
    have hs : σ x + σ x ^ Fintype.card k = x + x ^ Fintype.card k := by
      rw [← map_pow, ← map_add]
      exact hfix _ (by rw [add_pow_card_eq_add_pow_card, hqq, add_comm])
    have hm : σ x * σ x ^ Fintype.card k = x * x ^ Fintype.card k := by
      rw [← map_pow, ← map_mul]
      exact hfix _ (by rw [mul_pow, hqq, mul_comm])
    have h0 : (σ x - x) * (σ x - x ^ Fintype.card k) = 0 := by
      linear_combination σ x * hs - hm
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  intro x
  by_contra ha
  have hq0 : Fintype.card k ≠ 0 := Fintype.card_ne_zero
  have hax : σ x = x := (hdich x).resolve_right ha
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgEquiv.ext fun y => by simpa using hcon y)
  have hbq : σ b = b ^ Fintype.card k := (hdich b).resolve_left hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero, zero_pow hq0])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (map_zero σ)
  rcases hdich (x * b) with h | h
  · rw [map_mul, hax, hbq] at h
    exact hb (hbq.trans (mul_left_cancel₀ hx0 h))
  · rw [map_mul, hax, hbq, mul_pow] at h
    exact ha (hax.trans (mul_right_cancel₀ (pow_ne_zero _ hb0) h))

theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_pos rfl, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, by simp⟩, fun y => Subtype.ext ?_⟩
    rcases mul_eq_zero.mp y.2 with h | h
    · exact h
    · exact (map_eq_zero σ).mp h
  rw [if_neg hd0]
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hN : ∀ t : K, t * σ t = t ^ (Fintype.card k + 1) := fun t => by
    rw [hfrob, pow_succ']
  have hfixset : Finset.univ.filter (fun e : K => σ e = e) =
      Finset.univ.image (algebraMap k K) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro he
      exact mem_range_algebraMap_of_pow_card_eq e ((hfrob e).symm.trans he)
    · rintro ⟨y, rfl⟩
      exact σ.commutes y
  have hfixcard : (Finset.univ.filter (fun e : K => σ e = e)).card = Fintype.card k := by
    rw [hfixset, Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
  have hD : (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card + 1 = Fintype.card k := by
    have hset : Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) =
        (Finset.univ.filter (fun e : K => σ e = e)).erase 0 := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      exact and_comm
    rw [hset, Finset.card_erase_add_one (by simp), hfixcard]
  have hS : (Finset.univ.filter (fun t : K => t ≠ 0)).card + 1 = Fintype.card k ^ 2 := by
    rw [Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, hK]
  have hmaps : ∀ t ∈ Finset.univ.filter (fun t : K => t ≠ 0),
      t * σ t ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    refine ⟨?_, mul_ne_zero ht ((map_ne_zero σ).mpr ht)⟩
    rw [map_mul, hfrob (σ t), hfrob t, hqq, mul_comm]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ e : K, ((Finset.univ.filter (fun t : K => t ≠ 0)).filter
      (fun t => t * σ t = e)).card ≤ Fintype.card k + 1 := by
    intro e
    calc _ ≤ (nthRoots (Fintype.card k + 1) e).toFinset.card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos _), ← hN]
          exact ht.2
      _ ≤ Multiset.card (nthRoots (Fintype.card k + 1) e) := Multiset.toFinset_card_le _
      _ ≤ Fintype.card k + 1 := card_nthRoots _ _
  have htarget : Nat.card {t : K // t * σ t = d} =
      ((Finset.univ.filter (fun t : K => t ≠ 0)).filter (fun t => t * σ t = d)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      refine ⟨?_, ht⟩
      rintro rfl
      exact hd0 (by simpa using ht.symm)
    · exact fun ht => ht.2
  rw [htarget]
  refine le_antisymm (hbound d) (not_lt.mp fun hlt => ?_)
  have hdD : d ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    simp [hd, hd0]
  have hlt2 : (Finset.univ.filter (fun t : K => t ≠ 0)).card <
      (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card * (Fintype.card k + 1) := by
    calc (Finset.univ.filter (fun t : K => t ≠ 0)).card = _ := hsum
      _ < ∑ e ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0), (Fintype.card k + 1) :=
          Finset.sum_lt_sum (fun e _ => hbound e) ⟨d, hdD, hlt⟩
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  rw [← hD] at hS hlt2
  nlinarith [hS, hlt2]

end field

theorem fFInert_holds : FFInert := by
  intro k K _ _ _ _ σ hσ hrank hne h2k M a haM J hJ hJdet T hT hTdet
  classical
  haveI : Module.Finite k K := Module.finite_of_finrank_eq_succ hrank
  haveI : Finite K := Module.finite_of_finite k
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ hrank hne
  have hσr : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have h2' := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at h2'
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact card_eq_card_sq_of_finrank_two hrank
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob hrank d hd
  have hsV : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) J) :=
    ffH_isHS hσr J hJ hJdet
  have hsU : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) T) :=
    ffH_isHS hσr T hT hTdet
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabS.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i)
            (Pi.basisFun K (Fin a) j)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro X
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      subst h
      rfl
    · intro h
      exact Matrix.ext fun i j => h i j
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabS.ffH (σ : K →+* K) T) hsU (by simp)
  have hli := linIndep_orth hsU.toIsSq f hf1 hf2
  obtain ⟨b', hb'⟩ : ∃ b' : Basis (Fin a) K (Fin a → K), ∀ i, b' i = f i := by
    rcases isEmpty_or_nonempty (Fin a) with hE | hE
    · exact ⟨Basis.empty _, fun i => isEmptyElim i⟩
    · exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), fun i => by simp⟩
  have e2 := card_isom hsU.toIsSq hsV.toIsSq
    (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq hsV.toIsSq b'
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hdiag : ∀ i j, PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j) =
        if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      rw [hb', hb']
      split_ifs with hij
      · subst hij
        rfl
      · exact hf1 i j hij
    simp only [hdiag]
  have key := e1.trans (e2.symm.trans (e3.trans e4))
  have final := card_diag (Nat.card k) hq0 hK hσr h2K hN a M haM (Fin M → K)
    (PI.VolStabS.ffH (σ : K →+* K) J) hsV (by simp)
    (fun i => PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hf2
  exact (congrArg (fun n : ℕ => (n : ℝ)) key).trans final

end PI.VolStabS.FFHS
end
end

section
namespace PI.VolStabS

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabS
end
