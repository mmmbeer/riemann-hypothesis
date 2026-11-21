import Mathlib

section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac

structure JSetup (K : Type*) [Field K] where
  σ : K →+* K
  O : Subring K
  p : K
  hp0 : p ≠ 0
  hpO : p ∈ O
  hσp : σ p = p
  hσO : ∀ x ∈ O, σ x ∈ O
  hσσ : ∀ x ∈ O, σ (σ x) = x
  hinv : ∀ x ∈ O, (¬ ∃ y ∈ O, x = p * y) → x⁻¹ ∈ O
  hone : ¬ ∃ y ∈ O, (1 : K) = p * y
  htwo : (2 : K)⁻¹ ∈ O
  h2 : (2 : K) ≠ 0
  hnorm : ∀ u ∈ O, σ u = u → (¬ ∃ y ∈ O, u = p * y) → ∃ w ∈ O, σ w * w = u
  hsep : ∀ x ∈ O, x ≠ 0 → ∃ N : ℕ, ¬ ∃ y ∈ O, x = p ^ N * y

variable {K : Type*} [Field K] (S : JSetup K)

namespace JSetup

def NU (x : K) : Prop := ∃ y ∈ S.O, x = S.p * y

theorem NU_zero : S.NU 0 := ⟨0, S.O.zero_mem, by rw [mul_zero]⟩

theorem NU_add {x y : K} (hx : S.NU x) (hy : S.NU y) : S.NU (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, S.O.add_mem ha hb, by rw [mul_add]⟩

theorem NU_neg {x : K} (hx : S.NU x) : S.NU (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, S.O.neg_mem ha, by rw [mul_neg]⟩

theorem NU_mul {x z : K} (hz : z ∈ S.O) (hx : S.NU x) : S.NU (z * x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨z * a, S.O.mul_mem hz ha, by ring⟩

theorem NU_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, S.NU (f i)) : S.NU (∑ i ∈ s, f i) := by
  exact Finset.sum_induction _ S.NU (fun _ _ => S.NU_add) S.NU_zero h

theorem ne_zero_of_not_NU {x : K} (hx : ¬ S.NU x) : x ≠ 0 := by
  rintro rfl
  exact hx S.NU_zero

theorem NU_σ {x : K} (hx : S.NU x) : S.NU (S.σ x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨S.σ a, S.hσO a ha, by rw [map_mul, S.hσp]⟩

theorem not_NU_σ {x : K} (hxO : x ∈ S.O) (hx : ¬ S.NU x) : ¬ S.NU (S.σ x) := by
  intro h
  apply hx
  have h2 := S.NU_σ h
  rwa [S.hσσ x hxO] at h2




variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IntV (x : ι → K) : Prop := ∀ i, x i ∈ S.O

def IntM (Γ : Matrix ι ι K) : Prop := ∀ i j, Γ i j ∈ S.O

def cv (x : ι → K) : ι → K := fun i => S.σ (x i)

def Herm (Γ : Matrix ι ι K) : Prop := ∀ i j, S.σ (Γ i j) = Γ j i

def hf (Γ : Matrix ι ι K) (x y : ι → K) : K := S.cv x ⬝ᵥ (Γ *ᵥ y)

def UM (Γ : Matrix ι ι K) : Prop :=
  ∀ x : ι → K, S.IntV x → (∀ i, S.NU ((Γ *ᵥ x) i)) → ∃ x', S.IntV x' ∧ Γ *ᵥ x = S.p • (Γ *ᵥ x')

theorem IntV_mulVec {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) {x : ι → K} (hx : S.IntV x) : S.IntV (Γ *ᵥ x) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.O.sum_mem fun j _ => S.O.mul_mem (hΓ i j) (hx j)

theorem IntV_cv {x : ι → K} (hx : S.IntV x) : S.IntV (S.cv x) := fun i => S.hσO (x i) (hx i)

theorem hf_mem {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) :
    S.hf Γ x y ∈ S.O := by
  unfold hf
  simp only [dotProduct]
  exact S.O.sum_mem fun i _ => S.O.mul_mem (S.IntV_cv hx i) (S.IntV_mulVec hΓ hy i)

theorem hf_swap {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hH : S.Herm Γ) {x y : ι → K} (hx : S.IntV x)
    (hy : S.IntV y) : S.hf Γ y x = S.σ (S.hf Γ x y) := by
  unfold hf cv
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [S.hσσ _ (hx _), hH]
  ring

theorem σ_mulVec {Γ : Matrix ι ι K} (hH : S.Herm Γ) (a : ι → K) (i : ι) :
    S.σ ((Γ *ᵥ a) i) = (S.cv a ᵥ* Γ) i := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, cv, hH i]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem σ_vecMul {Γ : Matrix ι ι K} (hH : S.Herm Γ) {a : ι → K} (ha : S.IntV a) (j : ι) :
    S.σ ((S.cv a ᵥ* Γ) j) = (Γ *ᵥ a) j := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, cv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.hσσ _ (ha i), hH i j, mul_comm]

end JSetup

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end

section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IntV_single (j : ι) {t : K} (ht : t ∈ S.O) : S.IntV (Pi.single j t) := by
  intro i
  rw [Pi.single_apply]
  split_ifs
  · exact ht
  · exact S.O.zero_mem

theorem IntV_add {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) : S.IntV (x + y) := fun i => S.O.add_mem (hx i) (hy i)

theorem IntV_sub {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) : S.IntV (x - y) := fun i => S.O.sub_mem (hx i) (hy i)

theorem IntV_smul {x : ι → K} {c : K} (hc : c ∈ S.O) (hx : S.IntV x) : S.IntV (c • x) := fun i => S.O.mul_mem hc (hx i)

theorem cv_add (x y : ι → K) : S.cv (x + y) = S.cv x + S.cv y := by
  funext k
  show S.σ (x k + y k) = S.σ (x k) + S.σ (y k)
  exact map_add _ _ _

theorem cv_sub (x y : ι → K) : S.cv (x - y) = S.cv x - S.cv y := by
  funext k
  show S.σ (x k - y k) = S.σ (x k) - S.σ (y k)
  exact map_sub _ _ _

theorem cv_smul (c : K) (x : ι → K) : S.cv (c • x) = S.σ c • S.cv x := by
  funext k
  show S.σ (c * x k) = S.σ c * S.σ (x k)
  exact map_mul _ _ _

theorem cv_single (j : ι) (t : K) : S.cv (Pi.single j t) = Pi.single j (S.σ t) := by
  funext k
  show S.σ ((Pi.single j t : ι → K) k) = (Pi.single j (S.σ t) : ι → K) k
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem hf_add_left (Γ : Matrix ι ι K) (x x' y : ι → K) : S.hf Γ (x + x') y = S.hf Γ x y + S.hf Γ x' y := by
  unfold hf
  rw [cv_add, add_dotProduct]

theorem hf_add_right (Γ : Matrix ι ι K) (x y y' : ι → K) : S.hf Γ x (y + y') = S.hf Γ x y + S.hf Γ x y' := by
  unfold hf
  rw [mulVec_add, dotProduct_add]

theorem hf_smul_left (Γ : Matrix ι ι K) (c : K) (x y : ι → K) : S.hf Γ (c • x) y = S.σ c * S.hf Γ x y := by
  unfold hf
  rw [cv_smul, smul_dotProduct, smul_eq_mul]

theorem hf_smul_right (Γ : Matrix ι ι K) (c : K) (x y : ι → K) : S.hf Γ x (c • y) = c * S.hf Γ x y := by
  unfold hf
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem mulVec_single_apply_hermitian_block_frames (Γ : Matrix ι ι K) (i j : ι) (t : K) :
    (Γ *ᵥ Pi.single j t) i = Γ i j * t := by
  show ∑ k, Γ i k * (Pi.single j t : ι → K) k = Γ i j * t
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem hf_single (Γ : Matrix ι ι K) (i j : ι) (s t : K) :
    S.hf Γ (Pi.single i s) (Pi.single j t) = S.σ s * (Γ i j * t) := by
  unfold hf
  rw [cv_single, ← mulVec_single_apply_hermitian_block_frames Γ i j t]
  show ∑ k, (Pi.single i (S.σ s) : ι → K) k * (Γ *ᵥ Pi.single j t) k = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem exists_not_NU {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hU : S.UM Γ) (h0 : Γ ≠ 0) :
    ∃ i j, ¬ S.NU (Γ i j) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, j, hij⟩ : ∃ i j, Γ i j ≠ 0 := by
    by_contra h
    push Not at h
    apply h0
    ext a b
    simp [h a b]
  have hdiv : ∀ x : ι → K, S.IntV x → ∀ k, S.NU ((Γ *ᵥ x) k) := by
    intro x hx k
    show S.NU (∑ l, Γ k l * x l)
    apply S.NU_sum
    intro l _
    rw [mul_comm]
    exact S.NU_mul (hx l) (hcon k l)
  have key : ∀ N : ℕ, ∃ x', S.IntV x' ∧
      Γ *ᵥ Pi.single j (1 : K) = S.p ^ N • (Γ *ᵥ x') := by
    intro N
    induction N with
    | zero => exact ⟨Pi.single j 1, S.IntV_single j S.O.one_mem, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      obtain ⟨x', hx', hx'eq⟩ := ih
      obtain ⟨x'', hx'', he⟩ := hU x' hx' (hdiv x' hx')
      refine ⟨x'', hx'', ?_⟩
      rw [hx'eq, he, smul_smul, pow_succ]
  obtain ⟨N, hN⟩ := S.hsep _ (hΓ i j) hij
  obtain ⟨x', hx', heq⟩ := key N
  apply hN
  refine ⟨(Γ *ᵥ x') i, S.IntV_mulVec hΓ hx' i, ?_⟩
  have h1 := congrFun heq i
  rw [Pi.smul_apply, smul_eq_mul, mulVec_single_apply_hermitian_block_frames, mul_one] at h1
  exact h1

theorem exists_unit_vec {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hH : S.Herm Γ) (hU : S.UM Γ) (h0 : Γ ≠ 0) :
    ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by

  have key : ∀ (v : ι → K) (k : ι), S.IntV v → v k = 1 → S.hf Γ v v ∈ S.O →
      S.σ (S.hf Γ v v) = S.hf Γ v v → ¬ S.NU (S.hf Γ v v) →
      ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by
    intro v k hv hk hO hσ hn
    have hu0 : S.hf Γ v v ≠ 0 := by
      intro hz
      apply hn
      unfold NU
      exact ⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩
    have hinvO : (S.hf Γ v v)⁻¹ ∈ S.O := S.hinv _ hO hn
    have hinvσ : S.σ (S.hf Γ v v)⁻¹ = (S.hf Γ v v)⁻¹ := by
      rw [map_inv₀, hσ]
    have hinvn : ¬ ∃ y ∈ S.O, (S.hf Γ v v)⁻¹ = S.p * y := by
      rintro ⟨y, hy, hyeq⟩
      apply S.hone
      refine ⟨y * S.hf Γ v v, S.O.mul_mem hy hO, ?_⟩
      rw [← mul_assoc, ← hyeq, inv_mul_cancel₀ hu0]
    obtain ⟨w, hwO, hw⟩ := S.hnorm _ hinvO hinvσ hinvn
    refine ⟨w • v, k, S.IntV_smul hwO hv, ?_, ?_⟩
    · rw [Pi.smul_apply, hk, smul_eq_mul, mul_one]
      intro hwn
      unfold NU at hwn
      obtain ⟨y, hy, hyeq⟩ := hwn
      apply hinvn
      refine ⟨S.σ w * y, S.O.mul_mem (S.hσO w hwO) hy, ?_⟩
      rw [← hw, hyeq]
      ring
    · rw [S.hf_smul_left, S.hf_smul_right, ← mul_assoc, hw, inv_mul_cancel₀ hu0]
  have hσ2 : S.σ 2 = 2 := by
    rw [← one_add_one_eq_two, map_add, map_one]
  have h2O : (2 : K) ∈ S.O := by
    have h11 := S.O.add_mem S.O.one_mem S.O.one_mem
    rwa [one_add_one_eq_two] at h11

  have diag : ∀ m : ι, ¬ S.NU (Γ m m) →
      ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by
    intro m hm
    have e : S.hf Γ (Pi.single m 1) (Pi.single m 1) = Γ m m := by
      rw [S.hf_single, map_one, one_mul, mul_one]
    refine key (Pi.single m 1) m (S.IntV_single m S.O.one_mem) (Pi.single_eq_same m 1) ?_ ?_ ?_
    · rw [e]; exact hΓ m m
    · rw [e]; exact hH m m
    · rw [e]; exact hm
  obtain ⟨i, j, hij⟩ := S.exists_not_NU hΓ hU h0
  by_cases hi : S.NU (Γ i i)
  swap
  · exact diag i hi
  by_cases hj : S.NU (Γ j j)
  swap
  · exact diag j hj

  have hne : i ≠ j := by
    rintro rfl
    exact hij hi
  have ht0 : Γ i j ≠ 0 := by
    intro hz
    apply hij
    unfold NU
    exact ⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩
  have hcO : (Γ i j)⁻¹ ∈ S.O := S.hinv _ (hΓ i j) hij
  have h1 : Γ i j * (Γ i j)⁻¹ = 1 := mul_inv_cancel₀ ht0
  have h2 : S.σ (Γ i j)⁻¹ * S.σ (Γ i j) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
  have hval : S.hf Γ (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) =
      Γ i i + 2 + S.σ (Γ i j)⁻¹ * Γ j j * (Γ i j)⁻¹ := by
    rw [S.hf_add_left, S.hf_add_right, S.hf_add_right, S.hf_single, S.hf_single, S.hf_single,
      S.hf_single, map_one, ← hH i j]
    linear_combination h1 + h2
  refine key (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) i
    (S.IntV_add (S.IntV_single i S.O.one_mem) (S.IntV_single j hcO)) ?_ ?_ ?_ ?_
  · rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero]
  · rw [hval]
    exact S.O.add_mem (S.O.add_mem (hΓ i i) h2O) (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) (hΓ j j)) hcO)
  · rw [hval]
    simp only [map_add, map_mul, hH i i, hH j j, S.hσσ (Γ i j)⁻¹ hcO, hσ2]
    ring
  · rw [hval]
    intro hn
    unfold NU at hn hi hj
    obtain ⟨y, hy, hyeq⟩ := hn
    obtain ⟨a, ha, hae⟩ := hi
    obtain ⟨b, hb, hbe⟩ := hj
    rw [hae, hbe] at hyeq
    have h2inv : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ S.h2
    apply S.hone
    refine ⟨(y - a - S.σ (Γ i j)⁻¹ * b * (Γ i j)⁻¹) * 2⁻¹,
      S.O.mul_mem (S.O.sub_mem (S.O.sub_mem hy ha)
        (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) hb) hcO)) S.htwo, ?_⟩
    linear_combination (2 : K)⁻¹ * hyeq - h2inv

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end

section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Γp (Γ : Matrix ι ι K) (a : ι → K) : Matrix ι ι K := Γ - vecMulVec (Γ *ᵥ a) (S.cv a ᵥ* Γ)

def proj (Γ : Matrix ι ι K) (a y : ι → K) : ι → K := y - S.hf Γ a y • a

theorem hf_eq_vecMul (Γ : Matrix ι ι K) (x y : ι → K) : S.hf Γ x y = (S.cv x ᵥ* Γ) ⬝ᵥ y :=
  dotProduct_mulVec _ _ _

private theorem vecMulVec_mulVec_hermitian_block_frames (u v y : ι → K) : vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem Γp_mulVec (Γ : Matrix ι ι K) (a y : ι → K) :
    S.Γp Γ a *ᵥ y = Γ *ᵥ y - S.hf Γ a y • (Γ *ᵥ a) := by
  rw [Γp, sub_mulVec, vecMulVec_mulVec_hermitian_block_frames, hf_eq_vecMul]

private theorem vecMul_vecMulVec' (u v x : ι → K) : x ᵥ* vecMulVec u v = (x ⬝ᵥ u) • v := by
  ext j
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecMul_Γp (Γ : Matrix ι ι K) (a x : ι → K) :
    S.cv x ᵥ* S.Γp Γ a = S.cv x ᵥ* Γ - S.hf Γ x a • (S.cv a ᵥ* Γ) := by
  rw [Γp, vecMul_sub, vecMul_vecMulVec']
  rfl

theorem hf_Γp (Γ : Matrix ι ι K) (a x y : ι → K) :
    S.hf (S.Γp Γ a) x y = S.hf Γ x y - S.hf Γ a y * S.hf Γ x a := by
  show S.cv x ⬝ᵥ (S.Γp Γ a *ᵥ y) = _
  rw [Γp_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rfl

variable {Γ : Matrix ι ι K} {a : ι → K}

theorem Γp_mulVec_self (haa : S.hf Γ a a = 1) : S.Γp Γ a *ᵥ a = 0 := by
  rw [Γp_mulVec, haa, one_smul, sub_self]

theorem vecMul_Γp_self (haa : S.hf Γ a a = 1) : S.cv a ᵥ* S.Γp Γ a = 0 := by
  rw [vecMul_Γp, haa, one_smul, sub_self]

theorem IntM_Γp (hΓ : S.IntM Γ) (ha : S.IntV a) : S.IntM (S.Γp Γ a) := by
  intro i j
  have h1 : (Γ *ᵥ a) i ∈ S.O := S.IntV_mulVec hΓ ha i
  have h2 : (S.cv a ᵥ* Γ) j ∈ S.O := by
    simp only [vecMul, dotProduct]
    exact S.O.sum_mem fun k _ => S.O.mul_mem (S.IntV_cv ha k) (hΓ k j)
  simp only [Γp, Matrix.sub_apply, vecMulVec_apply]
  exact S.O.sub_mem (hΓ i j) (S.O.mul_mem h1 h2)

theorem Herm_Γp (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) : S.Herm (S.Γp Γ a) := by
  intro i j
  simp only [Γp, Matrix.sub_apply, vecMulVec_apply, map_sub, map_mul, hH i j, S.σ_mulVec hH,
    S.σ_vecMul hH ha]
  ring

theorem mulVec_proj (Γ : Matrix ι ι K) (a y : ι → K) : Γ *ᵥ S.proj Γ a y = S.Γp Γ a *ᵥ y := by
  rw [proj, mulVec_sub, mulVec_smul, Γp_mulVec]

theorem IntV_proj (hΓ : S.IntM Γ) (ha : S.IntV a) {y : ι → K} (hy : S.IntV y) : S.IntV (S.proj Γ a y) :=
  S.IntV_sub hy (S.IntV_smul (S.hf_mem hΓ ha hy) ha)

private theorem sub_smul_vecMul (x b : ι → K) (c : K) (M : Matrix ι ι K) :
    (x - c • b) ᵥ* M = x ᵥ* M - c • (b ᵥ* M) := by
  ext j
  simp only [vecMul, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

private theorem hf_proj_right_eq_hf_Γp (Γ : Matrix ι ι K) (a x y : ι → K) :
    S.hf Γ x (S.proj Γ a y) = S.hf (S.Γp Γ a) x y := by
  show S.cv x ⬝ᵥ (Γ *ᵥ S.proj Γ a y) = S.cv x ⬝ᵥ (S.Γp Γ a *ᵥ y)
  rw [mulVec_proj]

theorem hf_proj_proj (haa : S.hf Γ a a = 1) (x y : ι → K) :
    S.hf Γ (S.proj Γ a x) (S.proj Γ a y) = S.hf (S.Γp Γ a) x y := by
  rw [hf_proj_right_eq_hf_Γp, hf_eq_vecMul, hf_eq_vecMul, proj, cv_sub, cv_smul,
    sub_smul_vecMul, S.vecMul_Γp_self haa, smul_zero, sub_zero]

theorem hf_self_proj (haa : S.hf Γ a a = 1) (y : ι → K) : S.hf Γ a (S.proj Γ a y) = 0 := by
  rw [hf_proj_right_eq_hf_Γp, hf_Γp, haa, mul_one, sub_self]

theorem hf_proj_self (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) (haa : S.hf Γ a a = 1) {y : ι → K}
    (hy : S.IntV y) : S.hf Γ (S.proj Γ a y) a = 0 := by
  rw [S.hf_swap hΓ hH ha (S.IntV_proj hΓ ha hy), S.hf_self_proj haa, map_zero]

theorem vecMul_proj (hΓ : S.IntM Γ) (hH : S.Herm Γ) (ha : S.IntV a) {y : ι → K} (hy : S.IntV y) :
    S.cv (S.proj Γ a y) ᵥ* Γ = S.cv y ᵥ* S.Γp Γ a := by
  rw [proj, cv_sub, cv_smul, sub_smul_vecMul, vecMul_Γp, S.hf_swap hΓ hH ha hy]

theorem UM_Γp (hΓ : S.IntM Γ) (hH : S.Herm Γ) (hU : S.UM Γ) (ha : S.IntV a) (haa : S.hf Γ a a = 1) :
    S.UM (S.Γp Γ a) := by
  intro x hx hPx
  have hz := S.IntV_proj hΓ ha hx
  have hΓz : ∀ i, S.NU ((Γ *ᵥ S.proj Γ a x) i) := by
    intro i
    rw [mulVec_proj]
    exact hPx i
  obtain ⟨z, hz', hzz⟩ := hU _ hz hΓz
  refine ⟨z, hz', ?_⟩
  have h0 : S.hf Γ a z = 0 := by
    have h1 : S.hf Γ a (S.proj Γ a x) = S.p * S.hf Γ a z := by
      show S.cv a ⬝ᵥ (Γ *ᵥ S.proj Γ a x) = S.p * (S.cv a ⬝ᵥ (Γ *ᵥ z))
      rw [hzz, dotProduct_smul, smul_eq_mul]
    rw [S.hf_self_proj haa] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left S.hp0
  rw [← S.mulVec_proj Γ a x, hzz, Γp_mulVec, h0, zero_smul, sub_zero]

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end

section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

theorem sum_mulVec' {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι K) (x : ι → K) :
    (∑ c ∈ s, A c) *ᵥ x = ∑ c ∈ s, A c *ᵥ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, add_mulVec, ih]

theorem vecMul_sum' {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι K) (x : ι → K) :
    x ᵥ* (∑ c ∈ s, A c) = ∑ c ∈ s, x ᵥ* A c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, vecMul_add, ih]

section Drop

variable {m : ℕ} (i : Fin (m + 1))

def ins (x : Fin m → K) : Fin (m + 1) → K := Fin.insertNth i 0 x

omit S in
theorem ins_same (x : Fin m → K) : ins i x i = 0 := Fin.insertNth_apply_same _ _ _

omit S in
theorem ins_succAbove (x : Fin m → K) (s : Fin m) : ins i x (i.succAbove s) = x s :=
  Fin.insertNth_apply_succAbove _ _ _ _

omit S in
theorem mulVec_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x : Fin m → K) (s : Fin m) :
    (G *ᵥ ins i x) (i.succAbove s) = (G.submatrix i.succAbove i.succAbove *ᵥ x) s := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, ins_same, ins_succAbove, mul_zero, zero_add,
    submatrix_apply]

omit S in
theorem vecMul_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x : Fin m → K) (s : Fin m) :
    (ins i x ᵥ* G) (i.succAbove s) = (x ᵥ* G.submatrix i.succAbove i.succAbove) s := by
  simp only [vecMul, dotProduct, Fin.sum_univ_succAbove _ i, ins_same, ins_succAbove, zero_mul, zero_add,
    submatrix_apply]

theorem cv_ins (x : Fin m → K) : S.cv (ins i x) = ins i (S.cv x) := by
  funext r
  rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
  · simp [cv, ins_same]
  · simp [cv, ins_succAbove]

theorem hf_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x y : Fin m → K) :
    S.hf G (ins i x) (ins i y) = S.hf (G.submatrix i.succAbove i.succAbove) x y := by
  rw [hf, hf, S.cv_ins, dotProduct, dotProduct, Fin.sum_univ_succAbove _ i]
  simp only [ins_same, ins_succAbove, zero_mul, zero_add, mulVec_ins]

theorem IntV_ins {x : Fin m → K} (hx : S.IntV x) : S.IntV (ins i x) := by
  intro r
  rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
  · rw [ins_same]; exact S.O.zero_mem
  · rw [ins_succAbove]; exact hx s

theorem ext_drop {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) K} {a : Fin (m + 1) → K} (ha : a i ≠ 0)
    (hσa : S.σ (a i) ≠ 0) (hM : M *ᵥ a = 0) (hN : N *ᵥ a = 0) (hM' : S.cv a ᵥ* M = 0)
    (hN' : S.cv a ᵥ* N = 0)
    (h : ∀ s t, M (i.succAbove s) (i.succAbove t) = N (i.succAbove s) (i.succAbove t)) : M = N := by
  have hcol : ∀ s, M (i.succAbove s) i = N (i.succAbove s) i := by
    intro s
    have e1 := congrFun hM (i.succAbove s)
    have e2 := congrFun hN (i.succAbove s)
    simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, Pi.zero_apply] at e1 e2
    simp only [h] at e1
    have : (M (i.succAbove s) i - N (i.succAbove s) i) * a i = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' ha
  have hrow : ∀ s j, M (i.succAbove s) j = N (i.succAbove s) j := by
    intro s j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨t, rfl⟩
    · exact hcol s
    · exact h s t
  ext r j
  rcases Fin.eq_self_or_eq_succAbove i r with hr | ⟨s, rfl⟩
  · rw [hr]
    have e1 := congrFun hM' j
    have e2 := congrFun hN' j
    simp only [vecMul, dotProduct, Fin.sum_univ_succAbove _ i, Pi.zero_apply, cv] at e1 e2
    simp only [hrow] at e1
    have : S.σ (a i) * (M i j - N i j) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hσa
    · exact sub_eq_zero.mp h'
  · exact hrow s j

theorem UM_drop {G : Matrix (Fin (m + 1)) (Fin (m + 1)) K} {a : Fin (m + 1) → K} (hU : S.UM G)
    (ha : S.IntV a) (hai : ¬ S.NU (a i)) (hGa : G *ᵥ a = 0) (haG : S.cv a ᵥ* G = 0) :
    S.UM (G.submatrix i.succAbove i.succAbove) := by
  intro x hx hNU
  have hall : ∀ s, S.NU ((G *ᵥ ins i x) (i.succAbove s)) := fun s => by rw [mulVec_ins]; exact hNU s
  have hσO := S.hσO _ (ha i)
  have hσn := S.not_NU_σ (ha i) hai
  have hne : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU hσn
  have hNU' : ∀ r, S.NU ((G *ᵥ ins i x) r) := by
    intro r
    rcases Fin.eq_self_or_eq_succAbove i r with hr | ⟨s, rfl⟩
    · rw [hr]
      have e := congrArg (fun v => v ⬝ᵥ ins i x) haG
      simp only [zero_dotProduct] at e
      rw [← dotProduct_mulVec, dotProduct, Fin.sum_univ_succAbove _ i] at e
      have e' : S.σ (a i) * (G *ᵥ ins i x) i
          = -(∑ s, S.cv a (i.succAbove s) * (G *ᵥ ins i x) (i.succAbove s)) := by
        simp only [cv] at e ⊢; linear_combination e
      have hv : (G *ᵥ ins i x) i
          = (S.σ (a i))⁻¹ * -(∑ s, S.cv a (i.succAbove s) * (G *ᵥ ins i x) (i.succAbove s)) := by
        rw [← e', ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rw [hv]
      exact S.NU_mul (S.hinv _ hσO hσn) (S.NU_neg (S.NU_sum _ _ fun s _ =>
        S.NU_mul (S.IntV_cv ha _) (hall s)))
    · exact hall s
  obtain ⟨x', hx', hxx⟩ := hU (ins i x) (S.IntV_ins i hx) hNU'
  have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
  set y := x' - (x' i * (a i)⁻¹) • a with hy_def
  have hyI : S.IntV y := S.IntV_sub hx' (S.IntV_smul (S.O.mul_mem (hx' i) (S.hinv _ (ha i) hai)) ha)
  have hyi : y i = 0 := by
    simp only [hy_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp; ring
  have hGy : G *ᵥ y = G *ᵥ x' := by
    rw [hy_def, mulVec_sub, mulVec_smul, hGa, smul_zero, sub_zero]
  have hins : ins i (fun s => y (i.succAbove s)) = y := by
    funext r
    rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
    · rw [ins_same, hyi]
    · rw [ins_succAbove]
  refine ⟨fun s => y (i.succAbove s), fun s => hyI _, ?_⟩
  funext s
  rw [← mulVec_ins, hxx, Pi.smul_apply, Pi.smul_apply, ← mulVec_ins, hins, hGy]

end Drop

theorem jac_fin : ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) K), S.IntM Γ → S.Herm Γ → S.UM Γ →
    ∃ (k : ℕ) (v : Fin k → Fin m → K), (∀ c, S.IntV (v c)) ∧
      (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
      ∑ c, vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ
  | 0, Γ, _, _, _ => ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by ext i; exact i.elim0⟩
  | m + 1, Γ, hΓ, hH, hU => by
    by_cases h0 : Γ = 0
    · exact ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by simp [h0]⟩
    obtain ⟨a, i, ha, hai, haa⟩ := S.exists_unit_vec hΓ hH hU h0
    have hG := S.IntM_Γp hΓ ha
    have hHG := S.Herm_Γp hΓ hH ha
    have hUG := S.UM_Γp hΓ hH hU ha haa
    have hGa := S.Γp_mulVec_self (Γ := Γ) haa
    have haG := S.vecMul_Γp_self (Γ := Γ) haa
    set G := S.Γp Γ a with hG_def
    obtain ⟨k, v'', hvI, hvo, hvs⟩ := jac_fin m (G.submatrix i.succAbove i.succAbove)
      (fun s t => hG _ _) (fun s t => hHG _ _) (S.UM_drop i hUG ha hai hGa haG)
    have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
    have hσa : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU (S.not_NU_σ (ha i) hai)
    set v' : Fin k → Fin (m + 1) → K := fun c => ins i (v'' c) with hv'_def
    have hv'I : ∀ c, S.IntV (v' c) := fun c => S.IntV_ins i (hvI c)
    have hv'o : ∀ c c', S.hf G (v' c) (v' c') = if c = c' then 1 else 0 := fun c c' => by
      rw [hv'_def, S.hf_ins, hvo]
    have hv's : ∑ c, vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) = G := by
      apply S.ext_drop i hai0 hσa _ hGa _ haG
      · intro s t
        rw [Matrix.sum_apply]
        conv_rhs => rw [← submatrix_apply G i.succAbove i.succAbove s t, ← hvs, Matrix.sum_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [vecMulVec_apply, hv'_def, S.cv_ins, mulVec_ins, vecMul_ins]
      · rw [sum_mulVec']
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [vecMulVec_mulVec, ← dotProduct_mulVec, hGa, dotProduct_zero, op_smul_eq_smul, zero_smul]
      · rw [vecMul_sum']
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [vecMul_vecMulVec, dotProduct_mulVec, haG, zero_dotProduct, zero_smul]
    refine ⟨k + 1, Fin.cons a (fun c => S.proj Γ a (v' c)), ?_, ?_, ?_⟩
    · intro c
      refine Fin.cases ?_ (fun c => ?_) c
      · simpa using ha
      · simpa using S.IntV_proj hΓ ha (hv'I c)
    · intro c c'
      refine Fin.cases ?_ (fun c => ?_) c <;> refine Fin.cases ?_ (fun c' => ?_) c'
      · simpa using haa
      · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_self_proj haa]
        rw [if_neg (Fin.succ_ne_zero c').symm]
      · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_proj_self hΓ hH ha haa (hv'I c)]
        rw [if_neg (Fin.succ_ne_zero c)]
      · simp only [Fin.cons_succ, S.hf_proj_proj haa, Fin.succ_inj]
        exact hv'o c c'
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have : ∀ c, vecMulVec (Γ *ᵥ S.proj Γ a (v' c)) (S.cv (S.proj Γ a (v' c)) ᵥ* Γ)
          = vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) := fun c => by
        rw [S.mulVec_proj, S.vecMul_proj hΓ hH ha (hv'I c)]
      rw [Finset.sum_congr rfl (fun c _ => this c), hv's, hG_def, Γp]
      abel

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end
