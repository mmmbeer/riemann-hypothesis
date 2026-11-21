import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenBase

section
open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

def ColsFixed (k : ℕ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ i : Fin g, (i : ℕ) < k →
    (∀ r, M r (Sum.inl i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl i)) ∧
    (∀ r, M r (Sum.inr i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr i))

theorem colsFixed_one (k : ℕ) : ColsFixed k (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
  intro i _
  exact ⟨fun r => rfl, fun r => rfl⟩

theorem colsFixed_mul {k : ℕ} {O M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hO : ColsFixed k O) (hM : ColsFixed k M) : ColsFixed k (O * M) := by
  intro i hi
  refine ⟨fun r => ?_, fun r => ?_⟩
  · have e : (O * M) r (Sum.inl i) = (O * (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) r (Sum.inl i) := by
      simp only [Matrix.mul_apply, (hM i hi).1]
    rw [e, Matrix.mul_one, (hO i hi).1]
  · have e : (O * M) r (Sum.inr i) = (O * (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) r (Sum.inr i) := by
      simp only [Matrix.mul_apply, (hM i hi).2]
    rw [e, Matrix.mul_one, (hO i hi).2]

private theorem J_mul_apply_inl (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g)
    (q : Fin g ⊕ Fin g) : (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem symplectic_entry_mul_J_mul_of_single_column_entry {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {p r0 : Fin g ⊕ Fin g} (h : ∀ r, r ≠ r0 → M r p = 0)
    (q : Fin g ⊕ Fin g) : M r0 p * (J (Fin g) ℤ * M) r0 q = J (Fin g) ℤ p q := by
  have h1 := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem hM)
  rw [Matrix.transpose_transpose, Matrix.mul_assoc] at h1
  have h2 := congrArg (fun A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ => A p q) h1
  rw [Matrix.mul_apply, Finset.sum_eq_single r0] at h2
  · rw [Matrix.transpose_apply] at h2
    exact h2
  · intro r _ hr
    rw [Matrix.transpose_apply, h r hr, zero_mul]
  · intro hr
    exact absurd (Finset.mem_univ _) hr

theorem low_entries {k : ℕ} {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M) {i j : Fin g} (hi : (i : ℕ) < k)
    (hj : k ≤ (j : ℕ)) : M (Sum.inl i) (Sum.inl j) = 0 ∧ M (Sum.inr i) (Sum.inl j) = 0 := by
  have hi1 := hF i hi
  have hA : ∀ r, r ≠ Sum.inl i → M r (Sum.inl i) = 0 := fun r hr => by
    rw [hi1.1 r, Matrix.one_apply_ne hr]
  have hB : ∀ r, r ≠ Sum.inr i → M r (Sum.inr i) = 0 := fun r hr => by
    rw [hi1.2 r, Matrix.one_apply_ne hr]
  have hA1 : M (Sum.inl i) (Sum.inl i) = 1 := by rw [hi1.1, Matrix.one_apply_eq]
  have hB1 : M (Sum.inr i) (Sum.inr i) = 1 := by rw [hi1.2, Matrix.one_apply_eq]
  have hij : i ≠ j := fun h => by subst h; omega
  have e1 := symplectic_entry_mul_J_mul_of_single_column_entry hM hA (Sum.inl j)
  have e2 := symplectic_entry_mul_J_mul_of_single_column_entry hM hB (Sum.inl j)
  rw [hA1, one_mul, J_mul_apply_inl] at e1
  rw [hB1, one_mul] at e2
  constructor
  · simpa [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hij] using e2
  · simpa [Matrix.J] using e1

theorem eJ_apply (j i l : Fin g) : eJ j i l = if j = i ∧ j = l then 1 else 0 := rfl

theorem sum_eJ (j i : Fin g) (x : Fin g → ℤ) :
    ∑ l, eJ j i l * x l = if i = j then x j else 0 := by
  simp only [eJ_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Ne.symm h, h]

theorem spTransl_mul_inl (S : Matrix (Fin g) (Fin g) ℤ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spTransl S * M) (Sum.inl i) p = M (Sum.inl i) p + ∑ l, S i l * M (Sum.inr l) p := by
  simp [spTransl, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem spTransl_mul_inr (S : Matrix (Fin g) (Fin g) ℤ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (i : Fin g) (p : Fin g ⊕ Fin g) : (spTransl S * M) (Sum.inr i) p = M (Sum.inr i) p := by
  simp [spTransl, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]


theorem spPJ_mul_inr (j : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g)
    (p : Fin g ⊕ Fin g) :
    (spPJ j * M) (Sum.inr i) p = if i = j then -M (Sum.inl j) p else M (Sum.inr i) p := by
  simp only [spPJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.neg_apply, sub_mul, neg_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sum_eJ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  split_ifs with h
  · subst h
    ring
  · ring

theorem colsFixed_spTransl {k : ℕ} {S : Matrix (Fin g) (Fin g) ℤ}
    (hS : ∀ i : Fin g, (i : ℕ) < k → ∀ l, S l i = 0) : ColsFixed k (spTransl S) := by
  intro i hi
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [spTransl, Matrix.one_apply, hS i hi]

theorem colsFixed_spPJ {k : ℕ} (j : Fin g) (hj : k ≤ (j : ℕ)) : ColsFixed k (spPJ j) := by
  intro i hi
  have hij : j ≠ i := fun h => by subst h; omega
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [spPJ, Matrix.single_apply, Matrix.one_apply, hij]

theorem vecMulVec_sq {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0) : vecMulVec u v * vecMulVec u v = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  have e : ∑ l, u a * v l * (u l * v b) = u a * v b * (v ⬝ᵥ u) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, h, mul_zero]

def rkU (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) : (Matrix (Fin g) (Fin g) ℤ)ˣ where
  val := 1 + vecMulVec u v
  inv := 1 - vecMulVec u v
  val_inv := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, vecMulVec_sq h]; abel
  inv_val := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, vecMulVec_sq h]; abel

theorem rkU_val (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    ((rkU u v h : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) = 1 + vecMulVec u v := rfl

theorem rkU_inv_val (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    (((rkU u v h)⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) =
      1 - vecMulVec u v := rfl


theorem spDiag_rk_mul_inr (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spDiag (rkU u v h) * M) (Sum.inr i) p = M (Sum.inr i) p - v i * ∑ l, u l * M (Sum.inr l) p := by
  simp only [spDiag, rkU_inv_val, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => by ring)

theorem colsFixed_spDiag_rk {k : ℕ} {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0)
    (hu : ∀ i : Fin g, (i : ℕ) < k → u i = 0) (hv : ∀ i : Fin g, (i : ℕ) < k → v i = 0) :
    ColsFixed k (spDiag (rkU u v h)) := by
  intro i hi
  simp only [spDiag, rkU_val, rkU_inv_val]
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [Matrix.vecMulVec_apply, hu i hi, hv i hi, Matrix.one_apply, eq_comm]

theorem phase1 (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    ∑ j, (M (Sum.inr j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro M hM hF hn
  by_cases hb : ∀ j, M (Sum.inr j) (Sum.inl k) = 0
  · exact ⟨1, Submonoid.one_mem _, colsFixed_one _, fun j => by rw [Matrix.one_mul]; exact hb j⟩
  push_neg at hb
  obtain ⟨j0, hd⟩ := hb
  have hkj0 : (k : ℕ) ≤ (j0 : ℕ) := by
    by_contra hlt
    exact hd (low_entries hM hF (not_le.mp hlt) le_rfl).2
  set a := M (Sum.inl j0) (Sum.inl k) with ha
  set d := M (Sum.inr j0) (Sum.inl k) with hdd
  set S : Matrix (Fin g) (Fin g) ℤ := (-(a / d)) • eJ j0 with hS
  have hSsymm : S.IsSymm := by
    simp [hS, Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_single]
  have hSk : ∀ i : Fin g, (i : ℕ) < k → ∀ l, S l i = 0 := by
    intro i hi l
    have hne : j0 ≠ i := fun h => by subst h; omega
    simp [hS, Matrix.single_apply, hne]
  have hO1 : spPJ j0 * spTransl S ∈ spH g := Submonoid.mul_mem _ (spPJ_mem j0) (spTransl_mem hSsymm)
  have hspH : spH g ≤ symplecticGroup (Fin g) ℤ := Submonoid.closure_le.2 (spGens_subset g)
  have hM' : spPJ j0 * spTransl S * M ∈ symplecticGroup (Fin g) ℤ :=
    Submonoid.mul_mem _ (hspH hO1) hM
  have hF' : ColsFixed k (spPJ j0 * spTransl S * M) :=
    colsFixed_mul (colsFixed_mul (colsFixed_spPJ j0 hkj0) (colsFixed_spTransl hSk)) hF
  have hkey : (a % d).natAbs < d.natAbs := by
    have h1 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg a hd) (Int.emod_lt a hd)
    rwa [Int.natAbs_cast] at h1
  have hrow : ∀ j, (spPJ j0 * spTransl S * M) (Sum.inr j) (Sum.inl k) =
      if j = j0 then -(a % d) else M (Sum.inr j) (Sum.inl k) := by
    intro j
    rw [Matrix.mul_assoc, spPJ_mul_inr, spTransl_mul_inl, spTransl_mul_inr]
    split_ifs with hj
    · congr 1
      have e : ∑ l, S j0 l * M (Sum.inr l) (Sum.inl k) = -(a / d) * d := by
        simp only [hS, Matrix.smul_apply, smul_eq_mul, mul_assoc]
        rw [← Finset.mul_sum, sum_eJ, if_pos rfl]
      rw [e, Int.emod_def]
      ring
    · rfl
  have hlt : ∑ j, ((spPJ j0 * spTransl S * M) (Sum.inr j) (Sum.inl k)).natAbs < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro j _
      rw [hrow j]
      split_ifs with hj
      · subst hj
        rw [Int.natAbs_neg]
        exact hkey.le
      · exact le_rfl
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      rw [hrow j0, if_pos rfl, Int.natAbs_neg]
      exact hkey
  obtain ⟨O2, hO2, hF2, h2⟩ := ih _ hlt _ hM' hF' rfl
  refine ⟨O2 * (spPJ j0 * spTransl S), Submonoid.mul_mem _ hO2 hO1, colsFixed_mul hF2
    (colsFixed_mul (colsFixed_spPJ j0 hkj0) (colsFixed_spTransl hSk)), fun j => ?_⟩
  rw [Matrix.mul_assoc]
  exact h2 j

end ReciprocityTheory.ChartRestriction.G.Key.Chi
end

section
open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

private theorem symplectic_sum_pair_eq_J {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hA : A ∈ symplecticGroup (Fin g) ℤ) (p q : Fin g ⊕ Fin g) :
    ∑ b, (A (Sum.inr b) p * A (Sum.inl b) q - A (Sum.inl b) p * A (Sum.inr b) q) =
      J (Fin g) ℤ p q := by
  have h := SymplecticGroup.transpose_mem hA
  rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at h
  rw [← h]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply]
  simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

private theorem symplectic_inl_inl_eq_zero_of_colsFixed {k : ℕ} {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hA : A ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k A) {i m : Fin g} (hi : (i : ℕ) < k)
    (hm : m ≠ i) : A (Sum.inl i) (Sum.inl m) = 0 := by
  have h := symplectic_sum_pair_eq_J hA (Sum.inr i) (Sum.inl m)
  obtain ⟨-, h2⟩ := hF i hi
  simpa [h2, Matrix.one_apply, Matrix.J, Matrix.fromBlocks, Ne.symm hm] using h

theorem phase2 (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    (∀ j, M (Sum.inr j) (Sum.inl k) = 0) → ∑ j, (M (Sum.inl j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ (∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0) ∧
      ∀ i j, (O * M) (Sum.inl i) (Sum.inl k) ≠ 0 → (O * M) (Sum.inl j) (Sum.inl k) ≠ 0 → i = j := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM hF hbot hsum
  by_cases hone : ∀ i j, M (Sum.inl i) (Sum.inl k) ≠ 0 → M (Sum.inl j) (Sum.inl k) ≠ 0 → i = j
  · exact ⟨1, (spH g).one_mem, colsFixed_one _, by simpa using hbot, by simpa using hone⟩
  push_neg at hone
  obtain ⟨a, b, ha, hb, hab⟩ := hone
  wlog hle : (M (Sum.inl b) (Sum.inl k)).natAbs ≤ (M (Sum.inl a) (Sum.inl k)).natAbs generalizing a b
  · exact this b a hb ha (Ne.symm hab) (by omega)
  have hak : (k : ℕ) ≤ a := by
    by_contra hlt
    push_neg at hlt
    exact ha (symplectic_inl_inl_eq_zero_of_colsFixed hM hF hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  have hbk : (k : ℕ) ≤ b := by
    by_contra hlt
    push_neg at hlt
    exact hb (symplectic_inl_inl_eq_zero_of_colsFixed hM hF hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  let t : ℤ := M (Sum.inl a) (Sum.inl k) / M (Sum.inl b) (Sum.inl k)
  let E : Matrix (Fin g) (Fin g) ℤ :=
    Matrix.of fun c u => (if c = u then (1 : ℤ) else 0) - if c = a ∧ u = b then t else 0
  let E' : Matrix (Fin g) (Fin g) ℤ :=
    Matrix.of fun c u => (if c = u then (1 : ℤ) else 0) + if c = a ∧ u = b then t else 0
  have hEE' : E * E' = 1 := by
    ext c d
    simp [E, E', Matrix.mul_apply, Matrix.one_apply, sub_mul, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_and]
    split_ifs <;> simp_all
  have hE'E : E' * E = 1 := by
    ext c d
    simp [E, E', Matrix.mul_apply, Matrix.one_apply, add_mul, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_and]
    split_ifs <;> simp_all
  let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨E, E', hEE', hE'E⟩
  have hO1 : spDiag U ∈ spH g := spDiag_mem U
  have hF1 : ColsFixed k (spDiag U) := by
    intro i hi
    have hia : i ≠ a := fun h => by subst h; omega
    have hib : i ≠ b := fun h => by subst h; omega
    have e1 : ∀ c : Fin g, (i = c ↔ c = i) := fun c => eq_comm
    constructor <;> intro r <;> rcases r with c | c <;>
      simp [spDiag, U, E, E', Matrix.fromBlocks, Matrix.one_apply, hia, hib, e1]
  have hnew : ∀ c, (spDiag U * M) (Sum.inl c) (Sum.inl k) =
      M (Sum.inl c) (Sum.inl k) - if c = a then t * M (Sum.inl b) (Sum.inl k) else 0 := by
    intro c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp [spDiag, U, E, Matrix.fromBlocks, hbot, sub_mul, Finset.sum_sub_distrib, ite_and]
  have hbot1 : ∀ j, (spDiag U * M) (Sum.inr j) (Sum.inl k) = 0 := by
    intro j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp [spDiag, Matrix.fromBlocks, hbot]
  have hkey : (M (Sum.inl a) (Sum.inl k) - t * M (Sum.inl b) (Sum.inl k)).natAbs <
      (M (Sum.inl a) (Sum.inl k)).natAbs := by
    have he : M (Sum.inl a) (Sum.inl k) - t * M (Sum.inl b) (Sum.inl k) =
        M (Sum.inl a) (Sum.inl k) % M (Sum.inl b) (Sum.inl k) := by
      rw [Int.emod_def]
      ring
    have h1 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (M (Sum.inl a) (Sum.inl k)) hb)
      (Int.emod_lt (M (Sum.inl a) (Sum.inl k)) hb)
    have h2 : (M (Sum.inl a) (Sum.inl k) % M (Sum.inl b) (Sum.inl k)).natAbs <
        (M (Sum.inl b) (Sum.inl k)).natAbs := by
      simp only [Int.natCast_natAbs] at h1
      rwa [Int.natAbs_abs] at h1
    rw [he]
    omega
  have hlt : ∑ j, ((spDiag U * M) (Sum.inl j) (Sum.inl k)).natAbs < n := by
    rw [← hsum]
    apply Finset.sum_lt_sum
    · intro j _
      rw [hnew]
      by_cases hja : j = a
      · subst hja
        simp only [if_true]
        exact hkey.le
      · simp [hja]
    · exact ⟨a, Finset.mem_univ _, by rw [hnew]; simpa using hkey⟩
  have hM1 : spDiag U * M ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO1) hM
  obtain ⟨O2, hO2, hF2, hb2, hone2⟩ := ih _ hlt (spDiag U * M) hM1 (colsFixed_mul hF1 hF) hbot1 rfl
  refine ⟨O2 * spDiag U, (spH g).mul_mem hO2 hO1, colsFixed_mul hF2 hF1, ?_, ?_⟩
  · simpa [Matrix.mul_assoc] using hb2
  · simpa [Matrix.mul_assoc] using hone2

theorem move_col (k j : Fin g) (hjk : (k : ℕ) ≤ j) (hne : j ≠ k) (s : ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl j then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r, (O * M) r (Sum.inl k) = if r = Sum.inl k then s else 0 := by
  classical
  let P : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun a b => if Equiv.swap j k a = b then 1 else 0
  have hP : P * P = 1 := by
    ext a b
    simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (Equiv.swap j k a)]
    · simp [Equiv.swap_apply_self, eq_comm]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨P, P, hP, hP⟩
  refine ⟨spDiag U, spDiag_mem U, fun i hi => ?_, fun r => ?_⟩
  · have hik : i ≠ k := fun h => by subst h; exact lt_irrefl _ hi
    have hij : i ≠ j := fun h => by subst h; omega
    have hsw : Equiv.swap j k i = i := Equiv.swap_apply_of_ne_of_ne hij hik
    constructor <;> intro r <;> rcases r with a | a
    · have h1 : (Equiv.swap j k a = i) ↔ (a = i) := by rw [Equiv.swap_apply_eq_iff, hsw]
      simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks, h1]
    · simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks]
    · simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks]
    · have h1 : (i = a) ↔ (a = i) := eq_comm
      simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks, Matrix.transpose_apply, hsw, h1]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with a | a <;>
      simp [spDiag, U, P, hsupp, Matrix.one_apply, Matrix.fromBlocks, Equiv.swap_apply_eq_iff] <;>
      try (split_ifs <;> simp_all)

theorem sign_col (k : Fin g) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl k then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
  classical
  rcases hs with rfl | rfl
  · refine ⟨1, (spH g).one_mem, colsFixed_one _, fun r => ?_⟩
    rw [Matrix.one_mul, hsupp r, Matrix.one_apply]
  · let D : Matrix (Fin g) (Fin g) ℤ := Matrix.diagonal fun i => if i = k then -1 else 1
    have hD : D * D = 1 := by
      simp only [D, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      split_ifs <;> norm_num
    let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨D, D, hD, hD⟩
    refine ⟨spDiag U, spDiag_mem U, fun i hi => ?_, fun r => ?_⟩
    · have hik : i ≠ k := fun h => by subst h; exact lt_irrefl _ hi
      constructor <;> intro r <;> rcases r with a | a <;>
        simp [spDiag, U, D, Matrix.one_apply, Matrix.diagonal_apply, Matrix.fromBlocks] <;>
        split_ifs <;> simp_all
    · rw [Matrix.mul_apply, Fintype.sum_sum_type]
      rcases r with a | a <;>
        simp [spDiag, U, D, hsupp, Matrix.one_apply, Matrix.diagonal_apply, Matrix.fromBlocks] <;>
        split_ifs <;> simp_all

theorem col_inl_step (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
  classical
  obtain ⟨O1, hO1, hF1, hb1⟩ := phase1 k _ M hM hF rfl
  have hM1 : O1 * M ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO1) hM
  obtain ⟨O2, hO2, hF2, hb2, hone2⟩ := phase2 k _ (O1 * M) hM1 (colsFixed_mul hF1 hF) hb1 rfl
  have hA : O2 * (O1 * M) ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO2) hM1
  have hFA : ColsFixed k (O2 * (O1 * M)) := colsFixed_mul hF2 (colsFixed_mul hF1 hF)
  have hid := symplectic_sum_pair_eq_J hA (Sum.inl k) (Sum.inr k)
  simp only [hb2, zero_mul, zero_sub] at hid
  simp [Matrix.J, Matrix.fromBlocks, Finset.sum_neg_distrib] at hid
  obtain ⟨j, hj⟩ : ∃ j, (O2 * (O1 * M)) (Sum.inl j) (Sum.inl k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    simp [hcon] at hid
  have hz : ∀ c, c ≠ j → (O2 * (O1 * M)) (Sum.inl c) (Sum.inl k) = 0 := by
    intro c hc
    by_contra h
    exact hc (hone2 c j h hj)
  have hsupp : ∀ r, (O2 * (O1 * M)) r (Sum.inl k) =
      if r = Sum.inl j then (O2 * (O1 * M)) (Sum.inl j) (Sum.inl k) else 0 := by
    intro r
    rcases r with c | c
    · by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, hz c hc]
    · simp [hb2]
  rw [Finset.sum_eq_single j (fun c _ hc => by rw [hz c hc, zero_mul]) (by simp)] at hid
  have hs := Int.eq_one_or_neg_one_of_mul_eq_one hid
  have hjk : (k : ℕ) ≤ j := by
    by_contra hlt
    push_neg at hlt
    exact hj (symplectic_inl_inl_eq_zero_of_colsFixed hA hFA hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  rcases eq_or_ne j k with hjk' | hjk'
  · rw [hjk'] at hsupp hs
    obtain ⟨O3, hO3, hF3, h3⟩ := sign_col k _ hs _ hsupp
    refine ⟨O3 * O2 * O1, (spH g).mul_mem ((spH g).mul_mem hO3 hO2) hO1,
      colsFixed_mul (colsFixed_mul hF3 hF2) hF1, fun r => ?_⟩
    simpa [Matrix.mul_assoc] using h3 r
  · obtain ⟨O3, hO3, hF3, h3⟩ := move_col k j hjk hjk' _ _ hsupp
    obtain ⟨O4, hO4, hF4, h4⟩ := sign_col k _ hs _ h3
    refine ⟨O4 * O3 * O2 * O1, (spH g).mul_mem ((spH g).mul_mem ((spH g).mul_mem hO4 hO3) hO2) hO1,
      colsFixed_mul (colsFixed_mul (colsFixed_mul hF4 hF3) hF2) hF1, fun r => ?_⟩
    simpa [Matrix.mul_assoc] using h4 r

end ReciprocityTheory.ChartRestriction.G.Key.Chi
end

section
open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

theorem col_inr_step (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M)
    (hk : ∀ r, M r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) :
    ∃ O ∈ spH g, ColsFixed k O ∧
      (∀ r, O r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) ∧
      ∀ r, (O * M) r (Sum.inr k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr k) := by
  have hrow : ∀ q, M (Sum.inr k) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr k) q :=
    row_inr_of_col_inl hM hk
  have hck : M (Sum.inr k) (Sum.inr k) = 1 := by rw [hrow]; simp
  have hlow : ∀ i : Fin g, (i : ℕ) < k → M (Sum.inr i) (Sum.inr k) = 0 := by
    intro i hi
    have hik : i ≠ k := by intro h; subst h; omega
    rw [row_inr_of_col_inl hM (hF i hi).1]; simp [Matrix.one_apply, hik]
  set c' : Fin g → ℤ := fun l => if (k : ℕ) < l then M (Sum.inr l) (Sum.inr k) else 0 with hc'
  have hdot : c' ⬝ᵥ Pi.single k 1 = 0 := by rw [dotProduct_single]; simp [hc']
  have hDmem : spDiag (rkU _ _ hdot) ∈ spH g := spDiag_mem _
  have hDF : ColsFixed k (spDiag (rkU _ _ hdot)) := by
    refine colsFixed_spDiag_rk hdot (fun i hi => ?_) (fun i hi => ?_)
    · have hik : i ≠ k := by intro h; subst h; omega
      simp [Pi.single_apply, hik]
    · simp only [hc']
      rw [if_neg (by omega)]
  have hDk : ∀ r, spDiag (rkU _ _ hdot) r (Sum.inl k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
    intro r
    rcases r with l | l
    · rw [spDiag, fromBlocks_apply₁₁, rkU_val]
      simp [vecMulVec_apply, hc', Matrix.one_apply]
    · simp [spDiag]
  set M1 := spDiag (rkU _ _ hdot) * M with hM1
  have hM1sp : M1 ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hDmem) hM
  have hM1F : ColsFixed k M1 := colsFixed_mul hDF hF
  have hc1 : ∀ l, M1 (Sum.inr l) (Sum.inr k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr l) (Sum.inr k) := by
    intro l
    rw [hM1, spDiag_rk_mul_inr]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hck, mul_one, hc']
    rcases lt_trichotomy (l : ℕ) k with h | h | h
    · have hlk : l ≠ k := by intro e; subst e; omega
      rw [if_neg (by omega), hlow l h]; simp [Matrix.one_apply, hlk]
    · have e : l = k := Fin.ext h
      subst e; rw [if_neg (lt_irrefl _), hck]; simp
    · have hlk : l ≠ k := by intro e; subst e; omega
      rw [if_pos h]; simp [Matrix.one_apply, hlk]
  have ha1 : ∀ i : Fin g, (i : ℕ) < k → M1 (Sum.inl i) (Sum.inr k) = 0 := by
    intro i hi
    rw [row_inl_of_col_inr hM1sp (hM1F i hi).2]; simp [Matrix.one_apply]
  set S : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun l m =>
    if m = k then (if l = k then -M1 (Sum.inl k) (Sum.inr k) else -M1 (Sum.inl l) (Sum.inr k))
    else (if l = k then -M1 (Sum.inl m) (Sum.inr k) else 0) with hS
  have hSsym : S.IsSymm := by
    refine Matrix.IsSymm.ext (fun l m => ?_)
    simp only [hS, of_apply]
    by_cases hl : l = k <;> by_cases hm : m = k <;> simp [hl, hm]
  have hSmem : spTransl S ∈ spH g := spTransl_mem hSsym
  have hSF : ColsFixed k (spTransl S) := by
    refine colsFixed_spTransl (fun i hi l => ?_)
    have hik : i ≠ k := by intro h; subst h; omega
    simp [hS, hik, ha1 i hi]
  have hSk : ∀ r, spTransl S r (Sum.inl k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
    intro r; rcases r with l | l <;> simp [spTransl, Matrix.one_apply]
  refine ⟨spTransl S * spDiag (rkU _ _ hdot), (spH g).mul_mem hSmem hDmem, colsFixed_mul hSF hDF,
    fun r => by rw [mul_col_of_unit hDk]; exact hSk r, ?_⟩
  intro r
  rw [Matrix.mul_assoc]
  show (spTransl S * M1) r (Sum.inr k) = _
  rcases r with l | l
  · rw [spTransl_mul_inl]
    have hsum : ∑ m, S l m * M1 (Sum.inr m) (Sum.inr k) = S l k := by
      simp only [hc1, Matrix.one_apply, Sum.inr.injEq, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    simp only [hS, of_apply, if_true]
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  · rw [spTransl_mul_inr, hc1]

private theorem mem_symplecticGroup_of_mem_spH (g : ℕ) :
    ∀ O ∈ spH g, O ∈ symplecticGroup (Fin g) ℤ := by
  intro O hO
  have hle : Submonoid.closure (spGens g) ≤ symplecticGroup (Fin g) ℤ := by
    rw [Submonoid.closure_le]
    intro M hM'
    rw [SetLike.mem_coe]
    rcases hM' with ((⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ)
    · (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
      rw [spTransl, Matrix.J, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hS.eq]
    · have hU2 : (U : Matrix (Fin g) (Fin g) ℤ) * (↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ) = 1 := by
        first
        | exact Units.mul_inv U
        | exact Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U)
      have hU : ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ) * (U : Matrix (Fin g) (Fin g) ℤ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hU2, Matrix.transpose_one]
      (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
      rw [spDiag, Matrix.J, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hU, hU2]
      rw [← Matrix.transpose_mul]
      first
      | rw [Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U), Matrix.transpose_one]
      | rw [← Matrix.coe_units_inv, Units.mul_inv, Matrix.transpose_one]
    · rw [Set.mem_singleton_iff] at hJ
      rw [hJ]
      first
      | exact SymplecticGroup.J_mem
      | exact Matrix.J_mem
      | ((first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
         rw [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
           Matrix.fromBlocks_multiply]
         simp)

  exact hle hO

theorem exists_colsFixed (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) : ∀ k : ℕ, k ≤ g → ∃ O ∈ spH g, ColsFixed k (O * M) := by
  have colmul : ∀ (A N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (c : Fin g ⊕ Fin g),
      (∀ r, N r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c) →
      (∀ r, A r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c) →
      ∀ r, (A * N) r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c := by
    intro A N c hN hA r
    rw [Matrix.mul_apply]
    simp_rw [hN]
    rw [← Matrix.mul_apply, Matrix.mul_one, hA]
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨O1, hO1, hF1⟩ := ih (by omega)
    let kk : Fin g := ⟨k, by omega⟩
    have hS1 : O1 * M ∈ symplecticGroup (Fin g) ℤ := mul_mem (mem_symplecticGroup_of_mem_spH g O1 hO1) hM
    obtain ⟨O2, hO2, hF2, h2⟩ := col_inl_step kk (O1 * M) hS1 hF1
    have hS2 : O2 * (O1 * M) ∈ symplecticGroup (Fin g) ℤ := mul_mem (mem_symplecticGroup_of_mem_spH g O2 hO2) hS1
    have hF2' : ColsFixed k (O2 * (O1 * M)) := fun i hi =>
      ⟨colmul _ _ _ (hF1 i hi).1 (hF2 i hi).1, colmul _ _ _ (hF1 i hi).2 (hF2 i hi).2⟩
    obtain ⟨O3, hO3, hF3, h3inl, h3⟩ := col_inr_step kk (O2 * (O1 * M)) hS2 hF2' h2
    refine ⟨O3 * (O2 * O1), mul_mem hO3 (mul_mem hO2 hO1), ?_⟩
    rw [show O3 * (O2 * O1) * M = O3 * (O2 * (O1 * M)) by simp only [Matrix.mul_assoc]]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ⟨colmul _ _ _ (hF2' i hi).1 (hF3 i hi).1, colmul _ _ _ (hF2' i hi).2 (hF3 i hi).2⟩
    · have hik : i = kk := Fin.ext hi
      rw [hik]
      exact ⟨colmul _ _ _ h2 h3inl, h3⟩

theorem spGen : SpGenStatement := by
  intro g M hM
  obtain ⟨A, rfl⟩ : ∃ A : symplecticGroup (Fin g) ℤ,
      (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = M := ⟨⟨M, hM⟩, rfl⟩
  obtain ⟨O, hO, hF⟩ := exists_colsFixed
    ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (A⁻¹).2 g le_rfl
  have h1 : O * ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 := by
    ext r c
    rcases c with i | i
    · exact (hF i i.isLt).1 r
    · exact (hF i i.isLt).2 r
  have h2 : ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) *
      (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  have hOM : O = (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
    calc O = O * (((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) *
          (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) := by rw [h2, Matrix.mul_one]
      _ = (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← hOM]
  exact hO


end ReciprocityTheory.ChartRestriction.G.Key.Chi
end
