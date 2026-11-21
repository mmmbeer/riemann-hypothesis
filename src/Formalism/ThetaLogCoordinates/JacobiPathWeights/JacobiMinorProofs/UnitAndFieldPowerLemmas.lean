import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
import Formalism.ThetaLogCoordinates.JacobiPathWeights.ValuationProductsComponents
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathProductHighestWeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound

section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A0

def trInv {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) : (Matrix (Fin n) (Fin n) R)ˣ :=
  ⟨(↑m⁻¹ : Matrix _ _ R).transpose, (↑m : Matrix _ _ R).transpose,
    by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩

theorem trInv_val {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) :
    (↑(trInv m) : Matrix (Fin n) (Fin n) R) = (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose := rfl

theorem trInv_inv {R : Type*} [CommRing R] {n : ℕ} (m : (Matrix (Fin n) (Fin n) R)ˣ) :
    (↑(trInv m)⁻¹ : Matrix (Fin n) (Fin n) R) = (↑m : Matrix (Fin n) (Fin n) R).transpose := rfl

end A0

namespace A0

theorem trunc (R : Type*) [CommRing R] (n i : ℕ) (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ)
    (hN : i ≤ N) : ∀ I : Finset (Fin n),
    ∃ Q : Finset (Fin n) → MvPolynomial (ℕ × Fin n) R,
      (∀ I', Q I' ∈ supported R {x : ℕ × Fin n | i ≤ x.1}) ∧
      pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) N I =
        ∑ I' : Finset (Fin n),
          pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) i I' * Q I' := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro I
    refine ⟨fun I' => if I' = I then 1 else 0, fun I' => ?_, ?_⟩
    · dsimp only
      split
      · exact one_mem _
      · exact zero_mem _
    · simp
  | succ N hN ih =>
    intro I
    by_cases hch : colHeight (μ (N + 1)) c = colHeight (μ N) c
    · rw [pathWord, if_pos hch]
      exact ih I
    · rw [pathWord, if_neg hch]
      choose Q hQ1 hQ2 using ih
      have hX : ∀ m : Fin n, (X (N, m) : MvPolynomial (ℕ × Fin n) R) ∈
          supported R {x : ℕ × Fin n | i ≤ x.1} := fun m => by
        rw [supported_eq_adjoin_X]
        exact Algebra.subset_adjoin ⟨(N, m), hN, rfl⟩
      unfold stepF
      split
      · refine ⟨fun I' => ∑ m ∈ I, ((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * Q (I.erase m) I' * X (N, m),
          fun I' => ?_, ?_⟩
        · exact sum_mem fun m _ => mul_mem (mul_mem (intCast_mem _ _) (hQ1 _ _)) (hX m)
        · unfold wedgeF
          simp only [hQ2, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
          ring
      · refine ⟨fun I' => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * X (N, m) * Q (insert m I) I',
          fun I' => ?_, ?_⟩
        · exact sum_mem fun m _ => mul_mem (mul_mem (intCast_mem _ _) (hX m)) (hQ1 _ _)
        · unfold contrF
          simp only [hQ2, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
          ring

end A0

namespace A0

theorem height_full {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) {m' : Fin n} (hm : m'.val + 1 = n) {c : ℤ}
    (hc : c ≤ μ m') : colHeight μ c = n := by
  have h1 := (Paths.le_iff_lt_colHeight h c m').1 hc
  have h2 := Paths.colHeight_le μ c
  omega

theorem height_zero {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) {m' : Fin n} (hm : m'.val = 0) {c : ℤ}
    (hc : μ m' < c) : colHeight μ c = 0 := by
  by_contra h0
  have : m'.val < colHeight μ c := by omega
  exact absurd ((Paths.le_iff_lt_colHeight h c m').2 this) (not_le.2 hc)

theorem idx_univ {n : ℕ} {I : Finset (Fin n)} (h : I.card = n) : I = univ :=
  (Finset.card_eq_iff_eq_univ I).1 (by simpa using h)

end A0

namespace A0

section Weights

variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

theorem wExp_add (last : Bool) (e e' : LVar ι ζ n →₀ ℕ) :
    wExp isVec S last (e + e') = wExp isVec S last e + wExp isVec S last e' := by
  have h : ∀ e : LVar ι ζ n →₀ ℕ,
      wExp isVec S last e = e.sum fun x d => (d : ℤ) * wtX isVec S last x := fun e => rfl
  rw [h, h, h, Finsupp.sum_add_index']
  · intro x; simp
  · intro x a b; push_cast; ring

theorem wExp_weight (last : Bool) (e : LVar ι ζ n →₀ ℕ) :
    wExp isVec S last e = Finsupp.weight (wtX isVec S last) e := by
  rw [Finsupp.weight_apply]
  unfold wExp Finsupp.sum
  simp

def WGe (last : Bool) (s : ℤ) (H : MvPolynomial (LVar ι ζ n) L) (a : ℤ) : Prop :=
  ∀ e ∈ H.support, a ≤ s * wExp isVec S last e

variable {isVec S} {last : Bool} {s : ℤ}

theorem wge_zero (a : ℤ) : WGe isVec S last s (0 : MvPolynomial (LVar ι ζ n) L) a := by
  intro e he
  simp at he

theorem wge_add {H H' : MvPolynomial (LVar ι ζ n) L} {a : ℤ} (h : WGe isVec S last s H a)
    (h' : WGe isVec S last s H' a) : WGe isVec S last s (H + H') a := by
  classical
  intro e he
  rcases Finset.mem_union.1 (MvPolynomial.support_add he) with h1 | h1
  · exact h e h1
  · exact h' e h1

theorem wge_sum {κ : Type*} (t : Finset κ) (f : κ → MvPolynomial (LVar ι ζ n) L) {a : ℤ}
    (h : ∀ x ∈ t, WGe isVec S last s (f x) a) : WGe isVec S last s (∑ x ∈ t, f x) a := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using wge_zero a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact wge_add (h x (Finset.mem_insert_self _ _)) (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

theorem wge_mul {H H' : MvPolynomial (LVar ι ζ n) L} {a a' : ℤ} (h : WGe isVec S last s H a)
    (h' : WGe isVec S last s H' a') : WGe isVec S last s (H * H') (a + a') := by
  classical
  intro e he
  obtain ⟨e1, h1, e2, h2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul H H' he)
  rw [wExp_add, mul_add]
  exact add_le_add (h _ h1) (h' _ h2)

theorem wge_C (z : L) : WGe isVec S last s (C z : MvPolynomial (LVar ι ζ n) L) 0 := by
  classical
  intro e he
  have h0 : e = 0 := by
    by_contra hne
    rw [mem_support_iff, coeff_C, if_neg (Ne.symm hne)] at he
    exact he rfl
  subst h0
  simp [wExp]

theorem wge_int (z : ℤ) : WGe isVec S last s ((z : ℤ) : MvPolynomial (LVar ι ζ n) L) 0 := by
  rw [← map_intCast (C : L →+* MvPolynomial (LVar ι ζ n) L)]
  exact wge_C _

theorem wge_prod {κ : Type*} (t : Finset κ) (f : κ → MvPolynomial (LVar ι ζ n) L) (a : κ → ℤ)
    (h : ∀ x ∈ t, WGe isVec S last s (f x) (a x)) :
    WGe isVec S last s (∏ x ∈ t, f x) (∑ x ∈ t, a x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := wge_C (isVec := isVec) (S := S) (last := last) (s := s) (ζ := ζ) (n := n) (1 : L)
    simpa using this
  | insert x t hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact wge_mul (h x (Finset.mem_insert_self _ _)) (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

theorem wge_X (x : LVar ι ζ n) (hx : wtX isVec S last x = 0) :
    WGe isVec S last s (X x : MvPolynomial (LVar ι ζ n) L) 0 := by
  classical
  intro e he
  rw [mem_support_iff, coeff_X] at he
  have h1 : Finsupp.single x 1 = e := by
    by_contra hne
    rw [if_neg hne] at he
    exact he rfl
  rw [← h1, wExp_single, hx]
  simp

theorem wge_hom {H : MvPolynomial (LVar ι ζ n) L} {a w : ℤ}
    (h : IsWeightedHomogeneous (wtX isVec S last) H w) (ha : H ≠ 0 → a ≤ s * w) :
    WGe isVec S last s H a := by
  intro e he
  have hne : H ≠ 0 := by
    rintro rfl
    simp at he
  rw [wExp_weight, h (mem_support_iff.1 he)]
  exact ha hne

end Weights

theorem pathWord_card {R : Type*} [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (c : ℤ) (Xr : ℕ → Fin n → R) :
    ∀ j ≤ N, ∀ J : Finset (Fin n), pathWord isVec μ c Xr j J ≠ 0 →
      J.card = if 1 ≤ c then colHeight (μ j) c else n - colHeight (μ j) c := by
  intro j
  induction j with
  | zero =>
    intro _ J hJ
    have h0 : J = ∅ := by
      by_contra hne
      exact hJ (if_neg hne)
    rw [h0, hp.1, Paths.colHeight_zero]
    split_ifs <;> simp
  | succ j ih =>
    intro hj J hJ
    have ih' := ih (by omega)
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch] at hJ
      rw [hch]
      exact ih' J hJ
    · rw [pathWord, if_neg hch] at hJ
      have hh := Paths.path_height hp (show j < N by omega) c
      have hle := Paths.colHeight_le (μ j) c
      have hle' := Paths.colHeight_le (μ (j + 1)) c
      unfold stepF at hJ
      cases hup : (isVec j == decide (1 ≤ c))
      · rw [hup] at hJ
        simp only [Bool.false_eq_true, if_false] at hJ
        unfold contrF at hJ
        obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
        have e := ih' _ (right_ne_zero_of_mul hne)
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.1 hm)] at e
        by_cases h1 : 1 ≤ c
        · have hv : isVec j = false := by simpa [h1] using hup
          rw [hv] at hh
          simp only [Bool.false_eq_true, if_false] at hh
          rw [if_pos h1] at e ⊢
          omega
        · have hv : isVec j = true := by simpa [h1] using hup
          rw [hv] at hh
          simp only [if_true] at hh
          rw [if_neg h1] at e ⊢
          omega
      · rw [hup] at hJ
        simp only [if_true] at hJ
        unfold wedgeF at hJ
        obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
        have e := ih' _ (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
        have hpos : 0 < J.card := Finset.card_pos.2 ⟨m, hm⟩
        rw [Finset.card_erase_of_mem hm] at e
        by_cases h1 : 1 ≤ c
        · have hv : isVec j = true := by simpa [h1] using hup
          rw [hv] at hh
          simp only [if_true] at hh
          rw [if_pos h1] at e ⊢
          omega
        · have hv : isVec j = false := by simpa [h1] using hup
          rw [hv] at hh
          simp only [Bool.false_eq_true, if_false] at hh
          rw [if_neg h1] at e ⊢
          omega

theorem pathWord_congr {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr Xr' : ℕ → Fin n → R) : ∀ j : ℕ, (∀ l < j, Xr l = Xr' l) →
      pathWord isVec μ c Xr j = pathWord isVec μ c Xr' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [pathWord, pathWord, ih fun l hl => h l (by omega), h j (by omega)]

theorem act_pathWord' {A : Type} [CommRing A] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → A) (m : (Matrix (Fin n) (Fin n) A)ˣ) (j : ℕ) :
    pathWord isVec μ c (fun i => if isVec i then Matrix.vecMul (Xr i) (↑m : Matrix (Fin n) (Fin n) A)
        else Matrix.vecMul (Xr i) (↑m⁻¹ : Matrix (Fin n) (Fin n) A).transpose) j =
      actF (pathWord isVec μ c Xr j)
        (if 1 ≤ c then (↑m : Matrix (Fin n) (Fin n) A) else (↑m⁻¹ : Matrix (Fin n) (Fin n) A).transpose) := by
  by_cases h1 : 1 ≤ c
  · rw [if_pos h1]
    refine A1hw.act_pathWord actFormWedge actFormContract isVec μ c Xr _ m
      (fun i hi => ?_) (fun i hi => ?_) j
    · have : isVec i = true := by simpa [h1] using hi
      simp only [this, if_true]
    · have : isVec i = false := by simpa [h1] using hi
      simp only [this, Bool.false_eq_true, if_false]
  · rw [if_neg h1, ← trInv_val]
    refine A1hw.act_pathWord actFormWedge actFormContract isVec μ c Xr _ (trInv m)
      (fun i hi => ?_) (fun i hi => ?_) j
    · have : isVec i = false := by simpa [h1] using hi
      simp only [this, Bool.false_eq_true, if_false, trInv_val]
    · have : isVec i = true := by simpa [h1] using hi
      simp only [this, if_true, trInv_inv, Matrix.transpose_transpose]

theorem wt_word {L : Type*} [CommRing L] {n i : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ j, j < i → j ∈ S) (μ : ℕ → Fin n → ℤ) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : ∀ a : Fin n, (if last then a.val + 1 = n else a.val = 0) ↔ a = m) :
    ∀ j ≤ i, ∀ J : Finset (Fin n), IsWeightedHomogeneous (wtX (ζ := Empty) isVec S last)
      (pathWord isVec μ c (fun l a => (X (Sum.inl (l, a)) : MvPolynomial (LVar ℕ Empty n) L)) j J)
      (if m ∈ J then (if 1 ≤ c then 1 else -1) else 0) := by
  intro j
  induction j with
  | zero =>
    intro _ J
    show IsWeightedHomogeneous _ (if J = ∅ then 1 else 0) _
    split
    · rename_i h
      subst h
      simpa using isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  | succ j ih =>
    intro hj J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch]
      exact ih (by omega) J
    · rw [pathWord, if_neg hch]
      refine A1hw.wt_step _ _ m _ _ _ (ih (by omega)) (fun m' => ?_) J
      have := isWeightedHomogeneous_X L (wtX (ζ := Empty) (n := n) isVec S last) (Sum.inl (j, m'))
      convert this using 1
      have hjS : j ∈ S := hS j (by omega)
      by_cases h1 : 1 ≤ c <;> cases hv : isVec j <;> by_cases h2 : m' = m <;>
        simp [wtX, hjS, hm, h1, hv, h2]

def sgn (last : Bool) : ℤ := if last then 1 else -1

def bc (c x : ℤ) : ℤ := if 1 ≤ c then (if c ≤ x then (1 : ℤ) else 0) else (if x < c then -1 else 0)

theorem sum_bc (x : ℤ) (T : Finset ℤ) (hT : Finset.Ioc 0 x ∪ Finset.Ioc x 0 ⊆ T) : ∑ c ∈ T, bc c x = x :=
  A1hw.sum_wt x T hT

theorem col_bound {n : ℕ} {ν : Fin n → ℤ} (hν : Antitone ν) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) (J : Finset (Fin n))
    (hJ : J.card = if 1 ≤ c then colHeight ν c else n - colHeight ν c) :
    sgn last * bc c (ν m) ≤ sgn last * (if m ∈ J then (if 1 ≤ c then 1 else -1) else 0) := by
  cases last
  · simp only [Bool.false_eq_true, if_false] at hm
    by_cases h1 : 1 ≤ c
    · by_cases h2 : c ≤ ν m
      · simp only [sgn, bc, h1, h2, if_true, Bool.false_eq_true, if_false]
        split_ifs <;> norm_num
      · rw [if_pos h1, height_zero hν hm (not_le.1 h2), Finset.card_eq_zero] at hJ
        subst hJ
        simp [sgn, bc, h1, h2]
    · by_cases h2 : ν m < c
      · rw [if_neg h1, height_zero hν hm h2, Nat.sub_zero] at hJ
        rw [idx_univ hJ]
        simp [sgn, bc, h1, h2]
      · simp only [sgn, bc, h1, h2, Bool.false_eq_true, if_false]
        split_ifs <;> norm_num
  · simp only [if_true] at hm
    by_cases h1 : 1 ≤ c
    · by_cases h2 : c ≤ ν m
      · rw [if_pos h1, height_full hν hm h2] at hJ
        rw [idx_univ hJ]
        simp [sgn, bc, h1, h2]
      · simp only [sgn, bc, h1, h2, if_true, if_false]
        split_ifs <;> norm_num
    · by_cases h2 : ν m < c
      · simp only [sgn, bc, h1, h2, if_true, if_false]
        split_ifs <;> norm_num
      · rw [if_neg h1, height_full hν hm (not_lt.1 h2), Nat.sub_self, Finset.card_eq_zero] at hJ
        subst hJ
        simp [sgn, bc, h1, h2]

section Gen

variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]

def gH : MvPolynomial (ℕ × Fin n) k →+* MvPolynomial (LVar ℕ Empty n) (GenField k n) :=
  ((sharpHom isVec S (genMat k n)⁻¹ (genMat k n)).toRingHom.comp (MvPolynomial.map (genφ k n))).comp
    (rename Sum.inl : MvPolynomial (ℕ × Fin n) k →ₐ[k] MvPolynomial (LVar ℕ Empty n) k).toRingHom

def gam (n : ℕ) (τ : Type) : (Matrix (Fin n) (Fin n) (MvPolynomial τ (GenField k n)))ˣ :=
  ⟨(genMat k n)⁻¹.map C, (genMat k n).map C,
    by rw [← Matrix.map_mul, genMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, genMat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem gam_val (n : ℕ) (τ : Type) :
    (↑(gam k n τ) : Matrix (Fin n) (Fin n) (MvPolynomial τ (GenField k n))) = (genMat k n)⁻¹.map C := rfl

theorem gam_inv (n : ℕ) (τ : Type) :
    (↑(gam k n τ)⁻¹ : Matrix (Fin n) (Fin n) (MvPolynomial τ (GenField k n))) = (genMat k n).map C := rfl

theorem gH_in {j : ℕ} (hj : j ∈ S) :
    (fun a : Fin n => gH k isVec S (X (j, a))) =
      if isVec j then
        Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
          (↑(gam k n (LVar ℕ Empty n)) : Matrix (Fin n) (Fin n) _)
      else
        Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
          (↑(gam k n (LVar ℕ Empty n))⁻¹ : Matrix (Fin n) (Fin n) _).transpose := by
  funext a
  rw [gam_val, gam_inv]
  have h : gH k isVec S (X (j, a)) =
      sharpHom isVec S (genMat k n)⁻¹ (genMat k n) (X (Sum.inl (j, a))) := by
    simp [gH]
  rw [h]
  cases hv : isVec j
  · simp [sharpHom, hj, hv]
  · simp [sharpHom, hj, hv]

theorem gH_out {j : ℕ} (hj : j ∉ S) (a : Fin n) :
    gH k isVec S (X (j, a)) = X (Sum.inl (j, a)) := by
  simp [gH, sharpHom, hj]

variable {k isVec S}

theorem col_base {N i : ℕ} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} (hp : IsPath n isVec B μ N) (hi : i ≤ N)
    (hS : ∀ j, j ∈ S ↔ j < i) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) (J : Finset (Fin n)) :
    WGe isVec S last (sgn last)
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) i J))
      (sgn last * bc c (μ i m)) := by
  have hm' : ∀ a : Fin n, (if last then a.val + 1 = n else a.val = 0) ↔ a = m := by
    intro a
    cases last
    · simp only [Bool.false_eq_true, if_false] at hm ⊢
      rw [Fin.ext_iff]; omega
    · simp only [if_true] at hm ⊢
      rw [Fin.ext_iff]; omega
  rw [A1hw.map_pathWord (gH k isVec S)]
  rw [pathWord_congr isVec μ c _ _ i fun l hl => gH_in k isVec S ((hS l).2 hl)]
  rw [act_pathWord' isVec μ c
    (fun l b => (X (Sum.inl (l, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n))) (gam k n _) i]
  refine wge_sum _ _ fun I' _ => ?_
  obtain ⟨z, hz⟩ : ∃ z : GenField k n, minorF (if 1 ≤ c then
      (↑(gam k n (LVar ℕ Empty n)) : Matrix (Fin n) (Fin n) (MvPolynomial (LVar ℕ Empty n) (GenField k n)))
      else (↑(gam k n (LVar ℕ Empty n))⁻¹ : Matrix (Fin n) (Fin n) _).transpose) I' J = C z := by
    rw [gam_val, gam_inv, ← Matrix.transpose_map]
    split_ifs
    · exact ⟨_, (minorMap _ _ C n (genMat k n)⁻¹ I' J).symm⟩
    · exact ⟨_, (minorMap _ _ C n (genMat k n).transpose I' J).symm⟩
  rw [hz, ← add_zero (sgn last * bc c (μ i m))]
  refine wge_mul (wge_hom (wt_word isVec S (fun j hj => (hS j).2 hj) μ c last m hm' i le_rfl I')
    fun hne => ?_) (wge_C z)
  exact col_bound (hp.2.1 i hi) c last m hm I' (pathWord_card hp c _ i hi I' hne)

theorem col_all {i : ℕ} {μ : ℕ → Fin n → ℤ} (hS : ∀ j, j ∈ S ↔ j < i) (c : ℤ) (last : Bool) (s a : ℤ)
    (h0 : ∀ J : Finset (Fin n), WGe isVec S last s
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) i J)) a)
    (N : ℕ) (hN : i ≤ N) : ∀ J : Finset (Fin n), WGe isVec S last s
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) N J)) a := by
  induction N, hN using Nat.le_induction with
  | base => exact h0
  | succ N hN ih =>
    intro J
    by_cases hch : colHeight (μ (N + 1)) c = colHeight (μ N) c
    · rw [pathWord, if_pos hch]
      exact ih J
    · rw [pathWord, if_neg hch]
      have hout : N ∉ S := fun h => by have := (hS N).1 h; omega
      have hX : ∀ b : Fin n, WGe isVec S last s (gH k isVec S (X (N, b))) 0 := by
        intro b
        rw [gH_out k isVec S hout]
        exact wge_X _ (by simp [wtX, hout])
      unfold stepF
      split
      · unfold wedgeF
        rw [map_sum]
        refine wge_sum _ _ fun b _ => ?_
        rw [map_mul, map_mul, map_intCast]
        have := wge_mul (wge_mul (wge_int (isVec := isVec) (S := S) (last := last) (s := s)
          (L := GenField k n) (ζ := Empty) (n := n) (sg J b)) (ih (J.erase b))) (hX b)
        simpa using this
      · unfold contrF
        rw [map_sum]
        refine wge_sum _ _ fun b _ => ?_
        rw [map_mul, map_mul, map_intCast]
        have := wge_mul (wge_mul (wge_int (isVec := isVec) (S := S) (last := last) (s := s)
          (L := GenField k n) (ζ := Empty) (n := n) (sg J b)) (hX b)) (ih (insert b J))
        simpa using this

theorem psi_bound {N i : ℕ} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)}
    (hp : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) (hi : i ≤ N)
    (hS : ∀ j, j ∈ S ↔ j < i) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) :
    WGe isVec S last (sgn last) (gH k isVec S (psiPath k isVec μ N I)) (sgn last * μ i m) := by
  obtain ⟨hfin, -⟩ := pathProductDegrees k n N isVec B μ I hp hI
  have hsub : (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) k)) N (I c)) ⊆
      ↑(hfin.toFinset ∪ (Finset.Ioc 0 (μ i m) ∪ Finset.Ioc (μ i m) 0)) := by
    intro c hc
    rw [Finset.coe_union]
    exact Or.inl (by simpa using hc)
  unfold psiPath
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, map_prod]
  have := wge_prod (isVec := isVec) (S := S) (last := last) (s := sgn last)
    (hfin.toFinset ∪ (Finset.Ioc 0 (μ i m) ∪ Finset.Ioc (μ i m) 0))
    (fun c => gH k isVec S
      (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) k)) N (I c)))
    (fun c => sgn last * bc c (μ i m))
    (fun c _ => col_all hS c last _ _ (col_base hp hi hS c last m hm) N hi (I c))
  rwa [← Finset.mul_sum, sum_bc _ _ Finset.subset_union_right] at this

end Gen

end A0

theorem valuation_products_components : ValuationProductsComponents := by
  intro k _ n N i isVec B μ I hp hI hi
  constructor
  · intro m hm
    unfold valS
    refine Finset.le_min fun j hj => ?_
    obtain ⟨e, he, rfl⟩ := (gen_mem_supp isVec _ true _ j).1 hj
    have := A0.psi_bound (k := k) hp hI hi (S := {j : ℕ | j < i}) (fun j => Iff.rfl) true m
      (by simpa using hm) e he
    simp only [A0.sgn, if_true, one_mul] at this
    exact WithTop.coe_le_coe.2 this
  · intro m hm
    unfold lam1S
    refine Finset.max_le fun j hj => ?_
    obtain ⟨e, he, rfl⟩ := (gen_mem_supp isVec _ false _ j).1 hj
    have := A0.psi_bound (k := k) hp hI hi (S := {j : ℕ | j < i}) (fun j => Iff.rfl) false m
      (by simpa using hm) e he
    simp only [A0.sgn, Bool.false_eq_true, if_false] at this
    exact WithBot.coe_le_coe.2 (by linarith)

namespace A0

section Jacobi

variable {R : Type} [CommRing R] {n : ℕ}

def eps (I : Finset (Fin n)) : ℤ := ∏ a ∈ I, (-1) ^ (a.val + n + 1)

theorem eps_eq (I : Finset (Fin n)) : eps I = (-1) ^ (∑ a ∈ I, a.val + I.card * (n + 1)) := by
  unfold eps
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [add_assoc, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  ring

end Jacobi

end A0

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace ExponentSetCounting

variable {n : ℕ}

def GP (n i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) : Type :=
  {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ i ∧ (∀ j, i < j → μ j = 0) ∧ GoodW θ M (μ i)}

def ContP (i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n))) : Prop :=
  x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2

def splitEquiv {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) :
    {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} ≃
      Σ P : GP n i isVec B θ M, {x // ContP i N isVec B (P.1 i) x} where
  toFun x := ⟨⟨fun j => if j ≤ i then x.1.1.1 j else 0, by
      obtain ⟨⟨⟨μ, I⟩, ⟨h0, h1, h2⟩, h3, h4⟩, hg⟩ := x
      refine ⟨⟨by simpa using h0, ?_, ?_⟩, ?_, by simpa using hg⟩
      · intro j hj
        simpa [hj] using h1 j (hj.trans hi)
      · intro j hj
        have e1 : j ≤ i := by omega
        have e2 : j + 1 ≤ i := by omega
        simpa [e1, e2] using h2 j (by omega)
      · intro j hj
        have e1 : ¬ j ≤ i := by omega
        simp [e1]⟩,
    ⟨(fun j => if i ≤ j then x.1.1.1 j else 0, x.1.1.2), by
      obtain ⟨⟨⟨μ, I⟩, ⟨h0, h1, h2⟩, h3, h4⟩, hg⟩ := x
      refine ⟨by simp, ?_, ?_, by simpa [hi] using h4⟩
      · intro j hj
        by_cases e1 : i ≤ j
        · simpa [e1] using h3 j (by omega)
        · simp [e1]
      · intro j e1 hj
        have e2 : i ≤ j + 1 := by omega
        simpa [e1, e2] using h2 j hj⟩⟩
  invFun y := ⟨⟨(fun j => if j ≤ i then y.1.1 j else y.2.1.1 j, y.2.1.2), by
      obtain ⟨⟨μ, ⟨h0, h1, h2⟩, h3, hg⟩, ⟨⟨ν, I⟩, c0, c1, c2, c3⟩⟩ := y
      simp only at c0 c1 c2 c3 ⊢
      have key : ∀ j, i ≤ j → (if j ≤ i then μ j else ν j) = ν j := by
        intro j hj
        by_cases e : j ≤ i
        · obtain rfl : j = i := by omega
          simp [c0]
        · simp [e]
      have hr : ∀ j < N, if isVec j then
            HStrip (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (if j ≤ i then μ j else ν j) (B j)
          else HStrip (if j ≤ i then μ j else ν j) (if j + 1 ≤ i then μ (j + 1) else ν (j + 1)) (B j) := by
        intro j hj
        by_cases e : j < i
        · have e1 : j ≤ i := by omega
          have e2 : j + 1 ≤ i := by omega
          simpa [e1, e2] using h2 j e
        · rw [key j (by omega), key (j + 1) (by omega)]
          exact c2 j (by omega) hj
      have h00 : (if 0 ≤ i then μ 0 else ν 0) = 0 := by simpa using h0
      refine ⟨⟨h00, ?_, hr⟩, ?_, ?_⟩
      · exact Count.antitone_of_rules (μ := fun j => if j ≤ i then μ j else ν j)
          (by rw [h00]; exact fun _ _ _ => le_rfl) hr
      · intro j hj
        rw [key j (by omega)]
        exact c1 j (Or.inr hj)
      · rw [key N hi]
        exact c3⟩, by
      simpa using y.1.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases e : j ≤ i
      · simp [e]
      · have e' : i ≤ j := by omega
        simp [e, e']
    · rfl
  right_inv y := by
    obtain ⟨⟨μ, ⟨h0, h1, h2⟩, h3, hg⟩, ⟨⟨ν, I⟩, c0, c1, c2, c3⟩⟩ := y
    simp only at c0 c1 c2 c3
    apply Sigma.subtype_ext
    · apply Subtype.ext
      funext j
      by_cases e : j ≤ i
      · simp [e]
      · simp [e, h3 j (by omega)]
    · apply Prod.ext
      · funext j
        by_cases e : i ≤ j
        · by_cases e' : j ≤ i
          · obtain rfl : j = i := by omega
            simp [c0]
          · simp [e, e']
        · simp [e, c1 j (Or.inl (by omega))]
      · rfl

theorem card_good (hC : CountCont) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ)
    (M : WithTop ℤ) :
    Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} =
      Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
        ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  set K := ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) with hK
  have hanti : ∀ P : GP n i isVec B θ M, Antitone (P.1 i) := fun P => P.2.1.2.1 i le_rfl
  have hF : ∀ P : GP n i isVec B θ M, Finite {x // ContP i N isVec B (P.1 i) x} ∧
      Nat.card {x // ContP i N isVec B (P.1 i) x} = dGT n (P.1 i) * K :=
    fun P => hC n i N isVec B (P.1 i) hi (hanti P)
  have hG : ∀ P : GP n i isVec B θ M, Finite {x // ContP i i isVec B (P.1 i) x} ∧
      Nat.card {x // ContP i i isVec B (P.1 i) x} = dGT n (P.1 i) := by
    intro P
    have h := hC n i i isVec B (P.1 i) le_rfl (hanti P)
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [Finset.Ico_self, Finset.prod_empty, mul_one] at h2
    exact h2
  have he : ∀ P : GP n i isVec B θ M, Nonempty ({x // ContP i N isVec B (P.1 i) x} ≃
      {x // ContP i i isVec B (P.1 i) x} × Fin K) := by
    intro P
    haveI := (hF P).1
    haveI := (hG P).1
    haveI := Fintype.ofFinite {x // ContP i N isVec B (P.1 i) x}
    haveI := Fintype.ofFinite {x // ContP i i isVec B (P.1 i) x}
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      (hF P).2, (hG P).2]
  let e : ∀ P : GP n i isVec B θ M,
      {x // ContP i N isVec B (P.1 i) x} ≃ {x // ContP i i isVec B (P.1 i) x} × Fin K :=
    fun P => Classical.choice (he P)
  let d : (Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x} × Fin K) ≃
      (Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x}) × Fin K :=
    { toFun := fun y => (⟨y.1, y.2.1⟩, y.2.2)
      invFun := fun z => ⟨z.1.1, (z.1.2, z.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)}
      = Nat.card ((Σ P : GP n i isVec B θ M, {x // ContP i i isVec B (P.1 i) x}) × Fin K) :=
        Nat.card_congr (((splitEquiv hi isVec B θ M).trans (Equiv.sigmaCongrRight e)).trans d)
    _ = Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} * K := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin K), Fintype.card_fin,
          ← Nat.card_congr (splitEquiv (le_refl i) isVec B θ M)]

def expSet (n i N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {β | ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0}

theorem shift_inj (n i : ℕ) : Function.Injective (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem expSet_subset (n i N : ℕ) (B : ℕ → ℕ) :
    expSet n i N B ⊆ Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2)) ''
      {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0} := by
  intro β hβ
  have hβ' : ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0 := hβ
  have hsupp : ↑β.support ⊆ Set.range (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
    intro p hp
    obtain ⟨j, a⟩ := p
    have hpa : β (j, a) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hij : i ≤ j := by
      by_contra hlt
      have h0 := hβ' j
      rw [if_neg (fun h => hlt h.1)] at h0
      exact hpa ((Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a))
    exact ⟨(j - i, a), Prod.ext (show i + (j - i) = j by omega) rfl⟩
  refine ⟨Finsupp.comapDomain _ β (fun _ _ _ _ h => shift_inj n i h), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    intro j
    show ∑ a, β (i + j, a) = _
    rw [hβ' (i + j)]
    by_cases h : j < N - i
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · apply Finsupp.mapDomain_comapDomain
    · exact shift_inj n i
    · exact hsupp

theorem expSet_finite (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) : (expSet n i N B).Finite :=
  ((hR n (N - i) (fun j => B (i + j))).2.1.image _).subset (expSet_subset n i N B)

theorem expSet_card (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) :
    (expSet n i N B).ncard ≤ ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  have hfin : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.Finite :=
    (hR n (N - i) (fun j => B (i + j))).2.1
  have hcard : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard =
      ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) :=
    (hR n (N - i) (fun j => B (i + j))).1
  calc (expSet n i N B).ncard
      ≤ ((Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2))) ''
          {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}).ncard :=
        Set.ncard_le_ncard (expSet_subset n i N B) (hfin.image _)
    _ ≤ {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard :=
        Set.ncard_image_le hfin
    _ = ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) := hcard
    _ = ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
        (Finset.prod_Ico_eq_prod_range (fun l => (n + B l - 1).choose (B l)) i N).symm

theorem psiFam_mem (k : Type) [Field k] (N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    psiFam k n N isVec B x ∈ polB k n N B := by
  rw [polB, Submodule.mem_iInf]
  intro j
  exact (pathProductDegrees k n N isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1).2 j

theorem psiFam_good (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (θ : WithBot ℤ) (M : WithTop ℤ) (x : PathIdx n N isVec B) (hx : GoodW θ M (x.1.1 i)) :
    GoodG isVec i θ M (psiFam k n N isVec B x) := by
  obtain ⟨h1, h2⟩ := valuation_products_components k n N i isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1 hi
  constructor
  · intro t ht
    have a1 := hx.1 ⟨n - 1, by omega⟩ (by simp only; omega)
    have a2 := h1 ⟨n - 1, by omega⟩ (by simp only; omega)
    rw [ht, WithBot.coe_le_coe] at a1
    exact (WithTop.coe_le_coe.2 a1).trans a2
  · intro t ht
    have a1 := hx.2 ⟨0, by omega⟩ rfl
    have a2 := h2 ⟨0, by omega⟩ rfl
    rw [ht, WithTop.coe_le_coe] at a1
    exact a2.trans (WithBot.coe_le_coe.2 a1)

def prodFam (k : Type) [Field k] (n i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (p : {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) : MvPolynomial (ℕ × Fin n) k :=
  psiFam k n i isVec B p.1.1 * monomial p.2.1 1

theorem mem_spanProd (hT : LemmaA3top) (hF : FactSplit) (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (G : MvPolynomial (ℕ × Fin n) k)
    (hG : G ∈ polB k n N B) (hg : GoodG isVec i θ M G) :
    G ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
  obtain ⟨T, Gc, hTβ, hGc, hsum, hgood⟩ := hF k n N i isVec B θ M G hi hG
  rw [hsum]
  refine Submodule.sum_mem _ fun β hβ => ?_
  have hβe : β ∈ expSet n i N B := hTβ β hβ
  have hsp := hT k n i isVec B θ M (Gc β) hn (hGc β hβ) (hgood hg β hβ)
  have key : ∀ P ∈ Submodule.span k (psiFam k n i isVec B '' {x | GoodW θ M (x.1.1 i)}),
      P * monomial β 1 ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨y, hy⟩, ⟨β, hβe⟩), rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ a hx
  exact key _ hsp

theorem a3one_of_factSplit_of_countCont (hI : LemmaA2indep) (hfin : PathIdxFinite) (hR : PolBRank) (hT : LemmaA3top) (hF : FactSplit)
    (hC : CountCont) : LemmaA3one := by
  intro k _ n N i isVec B θ M G hn hi hG hg
  classical
  set S : Set (PathIdx n N isVec B) := {x | GoodW θ M (x.1.1 i)} with hS
  have hli : LinearIndependent k (psiFam k n N isVec B) := hI k n N isVec B
  haveI : Finite (PathIdx n N isVec B) := hfin n N isVec B
  haveI : Finite (PathIdx n i isVec B) := hfin n i isVec B
  haveI : Finite (expSet n i N B) := (expSet_finite hR n i N B).to_subtype
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype ({x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) :=
    Fintype.ofFinite _
  have hle : Submodule.span k (psiFam k n N isVec B '' S) ≤
      Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_spanProd hT hF k hn hi isVec B θ M _ (psiFam_mem k N isVec B x)
      (psiFam_good k hn hi isVec B θ M x hx)
  haveI hfd : FiniteDimensional k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M))) := by
    first
      | exact FiniteDimensional.span_of_finite k (Set.finite_range _)
      | exact FiniteDimensional.span_of_finite (Set.finite_range _)
      | exact Module.Finite.span_of_finite k (Set.finite_range _)
      | infer_instance
  have hr1 : Module.finrank k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M))) ≤
      Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} := by
    calc Module.finrank k (Submodule.span k (Set.range (prodFam k n i N isVec B θ M)))
        ≤ Fintype.card ({x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} × expSet n i N B) :=
          finrank_range_le_card (b := prodFam k n i N isVec B θ M)
      _ = Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} * Nat.card (expSet n i N B) := by
          rw [← Nat.card_eq_fintype_card, Nat.card_prod]
      _ ≤ Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
            ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
          Nat.mul_le_mul le_rfl (by
            first
              | (rw [Nat.card_coe_set_eq]; exact expSet_card hR n i N B)
              | exact expSet_card hR n i N B)
      _ = Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} :=
          (card_good hC hi isVec B θ M).symm
  have hr2 : Module.finrank k (Submodule.span k (psiFam k n N isVec B '' S)) =
      Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} := by
    have h := finrank_span_eq_card
      (hli.comp (Subtype.val : S → PathIdx n N isVec B) Subtype.val_injective)
    rw [Set.range_comp, Subtype.range_coe, ← Nat.card_eq_fintype_card] at h
    exact h
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [hr2]; exact hr1)
  rw [heq]
  exact mem_spanProd hT hF k hn hi isVec B θ M G hG hg

theorem good_zero (k : Type) [Field k] (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) :
    GoodG isVec i θ M (0 : MvPolynomial (ℕ × Fin n) k) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩
  · simp [valP, valS]
  · simp [lamP, lam1S]

theorem good_smul_add (k : Type) [Field k] (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (c : k)
    (G H : MvPolynomial (ℕ × Fin n) k) (hG : GoodG isVec i θ M G) (hH : GoodG isVec i θ M H) :
    GoodG isVec i θ M (c • G + H) := by
  constructor
  · intro t ht
    have h := (cornerValSubmodule k ℕ Empty n isVec {j : ℕ | j < i} (t : WithTop ℤ) ⊥ c (rename Sum.inl G)
      (rename Sum.inl H)).1 (hG.1 t ht) (hH.1 t ht)
    rw [valP, map_add, map_smul]
    exact h
  · intro t ht
    have h := (cornerValSubmodule k ℕ Empty n isVec {j : ℕ | j < i} ⊤ (t : WithBot ℤ) c (rename Sum.inl G)
      (rename Sum.inl H)).2 (hG.2 t ht) (hH.2 t ht)
    rw [lamP, map_add, map_smul]
    exact h

theorem mem_span_inter {k V ι κ : Type*} [Field k] [AddCommGroup V] [Module k V] {v : ι → V}
    (hv : LinearIndependent k v) (A : κ → Set ι) (i₀ : κ) (G : V)
    (h : ∀ i, G ∈ Submodule.span k (v '' A i)) : G ∈ Submodule.span k (v '' {x | ∀ i, x ∈ A i}) := by
  have h' : ∀ i, ∃ l ∈ Finsupp.supported k k (A i), Finsupp.linearCombination k v l = G := by
    intro i
    have hi := h i
    rw [Finsupp.mem_span_image_iff_linearCombination] at hi
    exact hi
  choose l hl hlG using h'
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨l i₀, ?_, hlG i₀⟩
  rw [Finsupp.mem_supported]
  intro x hx i
  have e : l i = l i₀ := hv ((hlG i).trans (hlG i₀).symm)
  have hs := (Finsupp.mem_supported k (l i)).mp (hl i)
  exact hs (by rw [e]; exact hx)

theorem a3field_of_a2indep_of_a3one (hI : LemmaA2indep) (h1 : LemmaA3one) : LemmaA3field := by
  intro k _ n N isVec B θ M G hn
  have hli : LinearIndependent k (psiFam k n N isVec B) := hI k n N isVec B
  constructor
  · rintro ⟨hG, hg⟩
    have hsp : ∀ i : {i : ℕ // i ≤ N}, G ∈ Submodule.span k
        (psiFam k n N isVec B '' {x | GoodW (θ i.1) (M i.1) (x.1.1 i.1)}) :=
      fun i => h1 k n N i.1 isVec B (θ i.1) (M i.1) G hn i.2 hG (hg i.1 i.2)
    have hint : G ∈ Submodule.span k (psiFam k n N isVec B ''
        {x | ∀ i : {i : ℕ // i ≤ N}, GoodW (θ i.1) (M i.1) (x.1.1 i.1)}) :=
      mem_span_inter hli (fun i : {i : ℕ // i ≤ N} => {x | GoodW (θ i.1) (M i.1) (x.1.1 i.1)})
        ⟨0, Nat.zero_le _⟩ G hsp
    have hset : {x : PathIdx n N isVec B | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)} =
        {x | ∀ i : {i : ℕ // i ≤ N}, GoodW (θ i.1) (M i.1) (x.1.1 i.1)} := by
      ext x
      simp only [Set.mem_setOf_eq, Subtype.forall]
    rw [hset]
    exact hint
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨psiFam_mem k N isVec B y, fun i hi => psiFam_good k hn hi isVec B (θ i) (M i) y (hy i hi)⟩
    | zero => exact ⟨Submodule.zero_mem _, fun i _ => good_zero k isVec i (θ i) (M i)⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun i hi => ?_⟩
      have hxy := good_smul_add k isVec i (θ i) (M i) 1 x y (hx.2 i hi) (hy.2 i hi)
      rwa [one_smul] at hxy
    | smul a x _ hx =>
      refine ⟨Submodule.smul_mem _ a hx.1, fun i hi => ?_⟩
      have hax := good_smul_add k isVec i (θ i) (M i) a x 0 (hx.2 i hi) (good_zero k isVec i (θ i) (M i))
      rwa [add_zero] at hax

end ExponentSetCounting



end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end
