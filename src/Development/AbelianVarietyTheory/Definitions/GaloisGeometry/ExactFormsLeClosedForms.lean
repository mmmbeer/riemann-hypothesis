import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcFormLocFormChernFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BasSingleMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.GoodMetric (coordVec)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Topology

namespace GlobalTheory.CxForm

section Point

variable {n m : ℕ}

def par (n : ℕ) : Alt n →ₐ[ℂ] Alt n := PullType.scale n (-1) (-1)

def HasDeg (k : ℕ) (α : Alt n) : Prop := ∀ S, (bas n).repr α S ≠ 0 → S.card = k

def degPart (n k : ℕ) : Alt n →ₗ[ℂ] Alt n := (bas n).constr ℂ fun S => if S.card = k then bas n S else 0

theorem repr_scale_self (t : ℂ) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (PullType.scale n t t α) S = t ^ S.card * (bas n).repr α S := by
  rw [PullType.repr_scale, ← pow_add, ← Finset.card_filter_add_card_filter_not (s := S) (·.val < n)]
  simp only [not_lt]

theorem hasDeg_iff_scale (k : ℕ) (α : Alt n) : HasDeg k α ↔ PullType.scale n 2 2 α = (2 : ℂ) ^ k • α := by
  constructor
  · intro h
    refine (bas n).ext_elem fun S => ?_
    rw [repr_scale_self, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hS : (bas n).repr α S = 0
    · simp [hS]
    · rw [h S hS]
  · intro h S hS
    have e := congrArg (fun β => (bas n).repr β S) h
    simp only [repr_scale_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at e
    have : (2 : ℕ) ^ S.card = 2 ^ k := by exact_mod_cast mul_right_cancel₀ hS e
    exact Nat.pow_right_injective le_rfl this

theorem HasDeg.mul {k l : ℕ} {α β : Alt n} (hα : HasDeg k α) (hβ : HasDeg l β) : HasDeg (k + l) (α * β) := by
  rw [hasDeg_iff_scale] at hα hβ ⊢
  rw [map_mul, hα, hβ, smul_mul_smul_comm, pow_add]

theorem HasDeg.zero (k : ℕ) : HasDeg k (0 : Alt n) := fun S h => by simp at h

theorem HasDeg.add {k : ℕ} {α β : Alt n} (hα : HasDeg k α) (hβ : HasDeg k β) : HasDeg k (α + β) := by
  rw [hasDeg_iff_scale] at hα hβ ⊢
  rw [map_add, hα, hβ, smul_add]

theorem HasDeg.smul {k : ℕ} {α : Alt n} (c : ℂ) (hα : HasDeg k α) : HasDeg k (c • α) := by
  rw [hasDeg_iff_scale] at hα ⊢
  rw [map_smul, hα, smul_comm]

theorem HasDeg.sum {k : ℕ} {ι : Type} {t : Finset ι} {α : ι → Alt n} (h : ∀ i ∈ t, HasDeg k (α i)) :
    HasDeg k (∑ i ∈ t, α i) :=
  Finset.sum_induction _ _ (fun _ _ => HasDeg.add) (.zero k) h

theorem HasDeg.pull {k : ℕ} {α : Alt m} (L : V n →L[ℂ] V m) (hα : HasDeg k α) : HasDeg k (pull L α) := by
  rw [hasDeg_iff_scale] at hα ⊢
  rw [PullType.scale_pull, hα, map_smul]

theorem hasDeg_bas (S : Finset (Fin (n + n))) : HasDeg S.card (bas n S) := fun T hT => by
  rw [Module.Basis.repr_self, Finsupp.single_apply] at hT
  split_ifs at hT with h
  exacts [h ▸ rfl, (hT rfl).elim]

theorem hasDeg_algebraMap (c : ℂ) : HasDeg 0 (algebraMap ℂ (Alt n) c) := by
  rw [hasDeg_iff_scale, AlgHom.commutes, pow_zero, one_smul]

theorem HasDeg.eq_algebraMap {α : Alt n} (h : HasDeg 0 α) : α = algebraMap ℂ _ ((bas n).repr α ∅) := by
  rw [Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine (bas n).ext_elem fun S => ?_
  by_cases hS : ∅ = S
  · subst hS; simp
  · have : (bas n).repr α S = 0 := by
      by_contra h'
      exact hS (Finset.card_eq_zero.1 (h S h')).symm
    simp [this, hS]

theorem scale_ι (t : ℂ) (u : Fin n ⊕ Fin n → ℂ) :
    PullType.scale n t t (ExteriorAlgebra.ι ℂ u) = t • ExteriorAlgebra.ι ℂ u := by
  rw [← map_smul]
  refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ ?_)
  rw [← smul_zero t, ← Matrix.fromBlocks_smul, Matrix.fromBlocks_one]
  simp

theorem hasDeg_ι (u : Fin n ⊕ Fin n → ℂ) : HasDeg 1 (ExteriorAlgebra.ι ℂ u) := by
  rw [hasDeg_iff_scale, scale_ι, pow_one]

theorem hasDeg_iff_mem (k : ℕ) (α : Alt n) : HasDeg k α ↔ α ∈ ⋀[ℂ]^k (Fin n ⊕ Fin n → ℂ) := by
  constructor
  · intro h
    rw [← (bas n).sum_repr α]
    refine Submodule.sum_mem _ fun S _ => ?_
    by_cases hS : (bas n).repr α S = 0
    · simp [hS]
    · refine Submodule.smul_mem _ _ ?_
      rw [← h S hS, bas, ExteriorAlgebra.basis_apply]
      exact ExteriorAlgebra.ιMulti_range _ _ ⟨_, rfl⟩
  · intro h
    induction h using Submodule.pow_induction_on_left' with
    | algebraMap r => exact hasDeg_algebraMap r
    | add x y i _ _ hx hy => exact hx.add hy
    | mem_mul u hu i x _ hx =>
      obtain ⟨u, rfl⟩ := hu
      rw [Nat.succ_eq_one_add]
      exact (hasDeg_ι u).mul hx

theorem repr_degPart (k : ℕ) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (degPart n k α) S = if S.card = k then (bas n).repr α S else 0 := by
  conv_lhs => rw [← (bas n).sum_repr α]
  simp only [map_sum, map_smul, degPart, Module.Basis.constr_basis, Finsupp.finset_sum_apply, Finsupp.smul_apply]
  rw [Finset.sum_eq_single S (fun T _ h => by split_ifs <;> simp [h]) (by simp)]
  split_ifs <;> simp

theorem hasDeg_degPart (k : ℕ) (α : Alt n) : HasDeg k (degPart n k α) := fun S hS => by
  rw [repr_degPart] at hS
  by_contra h
  exact hS (if_neg h)

theorem HasDeg.degPart_eq {j : ℕ} {α : Alt n} (h : HasDeg j α) (k : ℕ) : degPart n k α = if j = k then α else 0 := by
  refine (bas n).ext_elem fun S => ?_
  rw [repr_degPart]
  by_cases hS : (bas n).repr α S = 0
  · split_ifs <;> simp [hS]
  · rw [h S hS]
    split_ifs <;> simp

theorem degPart_pull (L : V n →L[ℂ] V m) (k : ℕ) (α : Alt m) : degPart n k (pull L α) = pull L (degPart m k α) := by
  have : degPart n k ∘ₗ (pull L).toLinearMap = (pull L).toLinearMap ∘ₗ degPart m k := (bas m).ext fun S => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [((hasDeg_bas S).pull L).degPart_eq, (hasDeg_bas S).degPart_eq, apply_ite (pull L), map_zero]
  exact LinearMap.congr_fun this α

theorem degPart_ι_mul (u : Fin n ⊕ Fin n → ℂ) (k : ℕ) (α : Alt n) :
    degPart n (k + 1) (ExteriorAlgebra.ι ℂ u * α) = ExteriorAlgebra.ι ℂ u * degPart n k α ∧
      degPart n 0 (ExteriorAlgebra.ι ℂ u * α) = 0 := by
  have h₁ : degPart n (k + 1) ∘ₗ LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ u) =
      LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ u) ∘ₗ degPart n k := (bas n).ext fun S => by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [((hasDeg_ι u).mul (hasDeg_bas S)).degPart_eq, (hasDeg_bas S).degPart_eq, add_comm 1]
    simp
  have h₂ : degPart n 0 ∘ₗ LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ u) = 0 := (bas n).ext fun S => by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [((hasDeg_ι u).mul (hasDeg_bas S)).degPart_eq]
    simp
  exact ⟨LinearMap.congr_fun h₁ α, LinearMap.congr_fun h₂ α⟩

theorem par_ι (u : Fin n ⊕ Fin n → ℂ) : par n (ExteriorAlgebra.ι ℂ u) = -ExteriorAlgebra.ι ℂ u := by
  rw [par, scale_ι, neg_one_smul]

theorem HasDeg.par_eq {k : ℕ} {α : Alt n} (h : HasDeg k α) : par n α = (-1 : ℂ) ^ k • α := by
  refine (bas n).ext_elem fun S => ?_
  rw [par, repr_scale_self, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hS : (bas n).repr α S = 0
  · simp [hS]
  · rw [h S hS]

theorem par_par (α : Alt n) : par n (par n α) = α := by
  refine (bas n).ext_elem fun S => ?_
  rw [par, repr_scale_self, repr_scale_self, ← mul_assoc, ← mul_pow]
  simp

theorem ι_mul_eq (u : Fin n ⊕ Fin n → ℂ) (α : Alt n) :
    ExteriorAlgebra.ι ℂ u * α = par n α * ExteriorAlgebra.ι ℂ u := by
  induction α using ExteriorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι x => rw [par_ι, neg_mul]; exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u x)
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, map_mul, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

theorem HasDeg.mul_comm {k l : ℕ} {α β : Alt n} (hα : HasDeg k α) (hβ : HasDeg l β) :
    α * β = (-1 : ℂ) ^ (k * l) • (β * α) := by
  rw [hasDeg_iff_mem] at hα
  induction hα using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [zero_mul, pow_zero, one_smul, Algebra.commutes]
  | add x y i _ _ hx hy => rw [add_mul, mul_add, hx, hy, smul_add]
  | mem_mul u hu i x _ hx =>
    obtain ⟨u, rfl⟩ := hu
    rw [mul_assoc, hx, mul_smul_comm, ← mul_assoc, ι_mul_eq, hβ.par_eq, smul_mul_assoc, smul_mul_assoc, smul_smul,
      ← pow_add, mul_assoc, Nat.succ_mul]

theorem mul_mem_holGe {p q : ℕ} {α β : Alt n} (hα : α ∈ holGe n p) (hβ : β ∈ holGe n q) : α * β ∈ holGe n (p + q) := by
  have key (S : Finset (Fin (n + n))) : bas n S * β ∈ holGe n (holCount S + q) := by
    induction S using Finset.induction_on with
    | empty => simpa [bas_empty, holCount] using hβ
    | insert a s ha ih =>
      obtain ⟨ε, e⟩ := bas_insert_eq ha
      rw [e, holCount_insert ha, Units.smul_def, smul_mul_assoc, mul_assoc, add_right_comm]
      exact zsmul_mem (bas_single_mul_mem a ih) _
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    exact holGe_anti (Nat.add_le_add_right hS _) (key S)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem holCount_le (S : Finset (Fin (n + n))) : holCount S ≤ n := by
  refine (Finset.card_le_card_of_injOn (t := Finset.range n) Fin.val (fun a ha => ?_)
    Fin.val_injective.injOn).trans_eq (Finset.card_range n)
  simpa using (Finset.mem_filter.1 ha).2

end Point

section Coord

variable {n : ℕ} {v : V n}

def dirD (i : Fin n ⊕ Fin n) (f : V n → ℂ) (v : V n) : ℂ :=
  match i with
  | .inl a => del f v (coordVec a)
  | .inr a => dbar f v (coordVec a)

def opAt (s : Fin n → Fin n ⊕ Fin n) (F : V n → Alt n) (v : V n) : Alt n :=
  ∑ a, ExteriorAlgebra.ι ℂ (Pi.single (s a) 1) * coefwise (fun f => dirD (s a) f v) F

theorem dirD_sum_mul (i : Fin n ⊕ Fin n) {ι : Type} [Fintype ι] {f : ι → V n → ℂ} (hf : ∀ p, DifferentiableAt ℝ (f p) v)
    (c : ι → ℂ) : dirD i (fun x => ∑ p, c p • f p x) v = ∑ p, c p • dirD i (f p) v := by
  rcases i with a | a
  · simp only [dirD]
    rw [del_sum fun p _ => (hf p).fun_const_smul (c p), ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [del_const_smul _ (hf p)]; rfl
  · simp only [dirD]
    rw [dbar_sum fun p _ => (hf p).fun_const_smul (c p), ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [dbar_const_smul _ (hf p)]; rfl

theorem dirD_zero (i : Fin n ⊕ Fin n) : dirD i (fun _ => 0) v = 0 := by
  rcases i with a | a <;> simp [dirD]

theorem dirD_comm {f : V n → ℂ} (hf : ContDiffAt ℝ 2 f v) (i j : Fin n ⊕ Fin n) :
    dirD i (dirD j f) v = dirD j (dirD i f) v := by
  rcases i with a | a <;> rcases j with b | b
  · exact SecForm.DdcLoc.del_del_comm hf _ _
  · exact (ddbar_eq_del_dbar hf _ _).symm.trans (ddbar_eq_dbar_del hf _ _)
  · exact (ddbar_eq_dbar_del hf _ _).symm.trans (ddbar_eq_del_dbar hf _ _)
  · exact SecForm.DdcLoc.dbar_dbar_comm hf _ _

theorem differentiableAt_dirD {f : V n → ℂ} (hf : ContDiffAt ℝ 2 f v) (i : Fin n ⊕ Fin n) :
    DifferentiableAt ℝ (dirD i f) v := by
  rcases i with a | a
  · exact (SecForm.DdcLoc.contDiffAt_del_at (j := 1) hf (by norm_num) _).differentiableAt one_ne_zero
  · exact (SecForm.DdcLoc.contDiffAt_dbar_at (j := 1) hf (by norm_num) _).differentiableAt one_ne_zero

theorem repr_linear (L : Alt n →ₗ[ℂ] Alt n) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (L α) S = ∑ T, (bas n).repr (L (bas n T)) S • (bas n).repr α T := by
  conv_lhs => rw [← (bas n).sum_repr α]
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem coefwise_dirD_linear (i : Fin n ⊕ Fin n) (L : Alt n →ₗ[ℂ] Alt n) {F : V n → Alt n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) :
    coefwise (fun f => dirD i f v) (fun x => L (F x)) = L (coefwise (fun f => dirD i f v) F) := by
  refine (bas n).ext_elem fun S => ?_
  rw [FormMul.repr_coefwise, repr_linear L (coefwise _ F)]
  simp only [repr_linear L (F _), FormMul.repr_coefwise]
  exact dirD_sum_mul i hF _

theorem opAt_opAt (s t : Fin n → Fin n ⊕ Fin n) {F : V n → Alt n}
    (hF : ∀ S, ContDiffAt ℝ 2 (fun x => (bas n).repr (F x) S) v) :
    opAt s (opAt t F) v = ∑ a, ∑ b, ExteriorAlgebra.ι ℂ (Pi.single (s a) 1) * ExteriorAlgebra.ι ℂ (Pi.single (t b) 1) *
      coefwise (fun f => dirD (s a) (dirD (t b) f) v) F := by
  have hd (b : Fin n) (S) : DifferentiableAt ℝ (fun x => (bas n).repr (coefwise (fun f => dirD (t b) f x) F) S) v := by
    simp only [FormMul.repr_coefwise]
    exact differentiableAt_dirD (hF S) _
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : opAt t F = fun x => ∑ b, LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single (t b) 1))
    (coefwise (fun f => dirD (t b) f x) F) := rfl
  rw [e, coefwise_sum_of, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [coefwise_dirD_linear _ _ (hd b), LinearMap.mulLeft_apply, mul_assoc]
    congr 2
    refine (bas n).ext_elem fun S => ?_
    simp only [FormMul.repr_coefwise]
  · intro S
    have := dirD_sum_mul (s a) (v := v) (f := fun b x => (bas n).repr (LinearMap.mulLeft ℂ
      (ExteriorAlgebra.ι ℂ (Pi.single (t b) 1)) (coefwise (fun f => dirD (t b) f x) F)) S) (fun b => by
        simp only [repr_linear (LinearMap.mulLeft ℂ _) (coefwise _ F)]
        exact DifferentiableAt.fun_sum fun T _ => (hd b T).fun_const_smul _) 1
    simpa only [Pi.one_apply, one_smul] using this

theorem opAt_anticomm (s t : Fin n → Fin n ⊕ Fin n) {F : V n → Alt n}
    (hF : ∀ S, ContDiffAt ℝ 2 (fun x => (bas n).repr (F x) S) v) :
    opAt s (opAt t F) v + opAt t (opAt s F) v = 0 := by
  rw [opAt_opAt s t hF, opAt_opAt t s hF, Finset.sum_comm (f := fun a b =>
    ExteriorAlgebra.ι ℂ (Pi.single (t a) 1) * _ * _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : coefwise (fun f => dirD (t b) (dirD (s a) f) v) F = coefwise (fun f => dirD (s a) (dirD (t b) f) v) F :=
    (bas n).ext_elem fun S => by rw [FormMul.repr_coefwise, FormMul.repr_coefwise, dirD_comm (hF S)]
  rw [this, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem delAt_dbarAt_sq {F : V n → Alt n} (hF : ∀ S, ContDiffAt ℝ 2 (fun x => (bas n).repr (F x) S) v) :
    delAt (delAt F) v = 0 ∧ dbarAt (dbarAt F) v = 0 ∧ delAt (dbarAt F) v + dbarAt (delAt F) v = 0 := by
  have h2 {y : Alt n} (h : y + y = 0) : y = 0 := by
    rw [← two_smul ℂ] at h
    exact (smul_eq_zero.1 h).resolve_left two_ne_zero
  exact ⟨h2 (opAt_anticomm .inl .inl hF), h2 (opAt_anticomm .inr .inr hF), opAt_anticomm .inl .inr hF⟩

theorem delAt_dbarAt_mul {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x * G x) v = delAt F v * G v + par n (F v) * delAt G v ∧
      dbarAt (fun x => F x * G x) v = dbarAt F v * G v + par n (F v) * dbarAt G v :=
  have h := FormMul.leibniz_of_comm n F G v (par n (F v)) hF hG
  ⟨h.1 fun _ => ι_mul_eq _ _, h.2 fun _ => ι_mul_eq _ _⟩

theorem opAt_par (s : Fin n → Fin n ⊕ Fin n) {F : V n → Alt n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) :
    opAt s (fun x => par n (F x)) v = -par n (opAt s F v) := by
  rw [opAt, opAt, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, par_ι, neg_mul, neg_neg]
  exact congrArg _ (coefwise_dirD_linear (s a) (par n).toLinearMap hF)

theorem degPart_opAt (s : Fin n → Fin n ⊕ Fin n) (k : ℕ) {F : V n → Alt n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) :
    degPart n (k + 1) (opAt s F v) = opAt s (fun x => degPart n k (F x)) v ∧ degPart n 0 (opAt s F v) = 0 := by
  rw [opAt, opAt, map_sum, map_sum]
  refine ⟨Finset.sum_congr rfl fun a _ => ?_, Finset.sum_eq_zero fun a _ => (degPart_ι_mul _ k _).2⟩
  rw [(degPart_ι_mul _ k _).1, coefwise_dirD_linear _ _ hF]

theorem hasDeg_opAt (s : Fin n → Fin n ⊕ Fin n) {k : ℕ} {F : V n → Alt n} (hF : ∀ x, HasDeg k (F x)) :
    HasDeg (k + 1) (opAt s F v) := by
  refine HasDeg.sum fun a _ => add_comm 1 k ▸ (hasDeg_ι _).mul fun S hS => ?_
  by_contra h
  have : (fun x => (bas n).repr (F x) S) = fun _ => 0 := funext fun x => by
    by_contra h'
    exact h (hF x S h')
  rw [FormMul.repr_coefwise, this, dirD_zero] at hS
  exact hS rfl

theorem opAt_mem_holGe (s : Fin n → Fin n ⊕ Fin n) {p : ℕ} {F : V n → Alt n} (hF : ∀ x, F x ∈ holGe n p) :
    opAt s F v ∈ holGe n p := by
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [← bas_singleton]
  refine holGe_anti (Nat.le_add_right _ _) (bas_single_mul_mem _ ((mem_holGe_iff _).2 fun S hS => ?_))
  by_contra h
  have : (fun x => (bas n).repr (F x) S) = fun _ => 0 := funext fun x => by
    by_contra h'
    exact h ((mem_holGe_iff _).1 (hF x) S h')
  rw [FormMul.repr_coefwise, this, dirD_zero] at hS
  exact hS rfl

end Coord

namespace HolAtlas

variable {M M' M'' : Type} [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace M''] {n n' n'' : ℕ}
  (A : HolAtlas M n) (A' : HolAtlas M' n') (A'' : HolAtlas M'' n'')

def dExt (α : A.Fld) : A.Fld := A.del α + A.dbar α

def IsDeg (k : ℕ) (α : A.Fld) : Prop := ∀ x, HasDeg k (α x)

def parFld : A.Fld →ₐ[ℂ] A.Fld := AlgHom.pi fun x => (par n).comp (Pi.evalAlgHom ℂ _ x)

def degFld (k : ℕ) : A.Fld →ₗ[ℂ] A.Fld := (degPart n k).compLeft A.Pt

@[simp] theorem parFld_apply (α : A.Fld) (x : A.Pt) : A.parFld α x = par n (α x) := rfl

@[simp] theorem degFld_apply (k : ℕ) (α : A.Fld) (x : A.Pt) : A.degFld k α x = degPart n k (α x) := rfl

def forms : Subalgebra ℂ A.Fld where
  carrier := {α | A.IsForm α}
  mul_mem' ha hb := ((isForm_algebra M n A).2 1 _ _ ha hb).2.1
  add_mem' ha hb := ((isForm_algebra M n A).2 1 _ _ ha hb).1
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact ((isForm_algebra M n A).2 c _ _ (isForm_algebra M n A).1 (isForm_algebra M n A).1).2.2

variable {A} in

@[simp] theorem mem_forms {α : A.Fld} : α ∈ A.forms ↔ A.IsForm α := Iff.rfl

variable {A}

theorem loc_linear (L : Alt n →ₗ[ℂ] Alt n) (α : A.Fld) (i : A.ι) :
    A.loc (fun x => L (α x)) i = fun v => L (A.loc α i v) := by
  funext v
  unfold loc
  split_ifs
  exacts [rfl, (map_zero L).symm]

theorem IsForm.linear {α : A.Fld} (hα : A.IsForm α) (L : Alt n →ₗ[ℂ] Alt n)
    (hL : ∀ (T : V n →L[ℂ] V n) (β : Alt n), L (pull T β) = pull T (L β)) : A.IsForm fun x => L (α x) := by
  refine ⟨fun i S => ?_, fun x x' h => by rw [hα.compat x x' h, hL]⟩
  simp only [loc_linear, repr_linear L (A.loc α i _)]
  exact ContDiffOn.sum fun T _ => (hα.smooth i T).const_smul _

theorem IsForm.parFld {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.parFld α) :=
  hα.linear (par n).toLinearMap fun T β => PullType.scale_pull T _ _ β

theorem IsForm.degFld {α : A.Fld} (hα : A.IsForm α) (k : ℕ) : A.IsForm (A.degFld k α) :=
  hα.linear (degPart n k) fun T β => degPart_pull T k β

theorem IsForm.dExt {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.dExt α) :=
  A.forms.add_mem (A.isForm_del_dbar hα).1 (A.isForm_del_dbar hα).2

theorem dExt_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.dExt (α + β) = A.dExt α + A.dExt β := by
  obtain ⟨h₁, h₂, -, -⟩ := (del_dbar_linear M n A).2 1 α β hα hβ
  rw [dExt, h₁, h₂, add_add_add_comm]
  rfl

theorem dExt_smul (c : ℂ) {α : A.Fld} (hα : A.IsForm α) : A.dExt (c • α) = c • A.dExt α := by
  obtain ⟨-, -, h₁, h₂⟩ := (del_dbar_linear M n A).2 c α α hα hα
  rw [dExt, h₁, h₂, ← smul_add]
  rfl

variable (A) in

def dForms : A.forms →ₗ[ℂ] A.forms where
  toFun α := ⟨A.dExt α, IsForm.dExt α.2⟩
  map_add' α β := Subtype.ext (dExt_add α.2 β.2)
  map_smul' c α := Subtype.ext (dExt_smul c α.2)

variable (A) in

def parForms : A.forms →ₐ[ℂ] A.forms := (A.parFld.comp A.forms.val).codRestrict _ fun α => IsForm.parFld α.2

@[simp] theorem coe_dForms (α : A.forms) : (A.dForms α : A.Fld) = A.dExt α := rfl

@[simp] theorem coe_parForms (α : A.forms) : (A.parForms α : A.Fld) = A.parFld α := rfl

variable (A) in

@[simp] theorem dExt_zero : A.dExt 0 = 0 := congrArg Subtype.val (map_zero A.dForms)

variable (A) in

@[simp] theorem dExt_one : A.dExt 1 = 0 := by
  rw [dExt, (del_dbar_linear M n A).1.1, (del_dbar_linear M n A).1.2, add_zero]

theorem loc_op_eventuallyEq (T : (V n → Alt n) → V n → Alt n) (α : A.Fld) (x : A.Pt) :
    A.loc (fun y => T (A.loc α y.1.1) y.crd) x.1.1 =ᶠ[𝓝 x.crd] T (A.loc α x.1.1) := by
  filter_upwards [GlobLin.target_mem_nhds A x] with v hv
  rw [loc, dif_pos hv]
  exact congrArg (T _) ((A.e x.1.1).right_inv hv)

theorem del_dbar_sq {α : A.Fld} (hα : A.IsForm α) :
    A.del (A.del α) = 0 ∧ A.dbar (A.dbar α) = 0 ∧ A.del (A.dbar α) + A.dbar (A.del α) = 0 := by
  have key (x : A.Pt) : A.del (A.del α) x = 0 ∧ A.dbar (A.dbar α) x = 0 ∧
      A.del (A.dbar α) x + A.dbar (A.del α) x = 0 := by
    have h := delAt_dbarAt_sq (v := x.crd) (F := A.loc α x.1.1) fun S =>
      ((hα.smooth x.1.1 S).contDiffAt (GlobLin.target_mem_nhds A x)).of_le (by norm_cast)
    have hg := (delAt_dbarAt_linear_local n x.crd).2.2.2.1
    have h₁ := hg _ _ (loc_op_eventuallyEq delAt α x)
    have h₂ := hg _ _ (loc_op_eventuallyEq dbarAt α x)
    exact ⟨h₁.1.trans h.1, h₂.2.trans h.2.1, (congrArg₂ (· + ·) h₂.1 h₁.2).trans h.2.2⟩
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2.1, funext fun x => (key x).2.2⟩

theorem dExt_dExt {α : A.Fld} (hα : A.IsForm α) : A.dExt (A.dExt α) = 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := del_dbar_sq hα
  rw [dExt.eq_1 A α, dExt_add (A.isForm_del_dbar hα).1 (A.isForm_del_dbar hα).2, dExt, dExt, h₁, h₂, zero_add, add_zero,
    add_comm, h₃]

theorem del_dbar_mul {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.del (α * β) = A.del α * β + A.parFld α * A.del β ∧ A.dbar (α * β) = A.dbar α * β + A.parFld α * A.dbar β := by
  have key (x : A.Pt) := delAt_dbarAt_mul (A.loc_diffAt hα x) (A.loc_diffAt hβ x)
  simp only [← A.loc_mul, A.loc_crd] at key
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2⟩

theorem dExt_mul {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.dExt (α * β) = A.dExt α * β + A.parFld α * A.dExt β := by
  rw [dExt, (del_dbar_mul hα hβ).1, (del_dbar_mul hα hβ).2, dExt, dExt, add_mul, mul_add, add_add_add_comm]

theorem dExt_apply (α : A.Fld) (x : A.Pt) :
    A.dExt α x = opAt .inl (A.loc α x.1.1) x.crd + opAt .inr (A.loc α x.1.1) x.crd := rfl

theorem dExt_parFld {α : A.Fld} (hα : A.IsForm α) : A.dExt (A.parFld α) = -A.parFld (A.dExt α) := by
  funext x
  have h := loc_linear (par n).toLinearMap α x.1.1
  rw [dExt_apply, show A.loc (A.parFld α) x.1.1 = _ from h, Pi.neg_apply, parFld_apply, dExt_apply, map_add, neg_add]
  exact congrArg₂ _ (opAt_par _ (A.loc_diffAt hα x)) (opAt_par _ (A.loc_diffAt hα x))

theorem degFld_dExt {α : A.Fld} (hα : A.IsForm α) (k : ℕ) :
    A.degFld (k + 1) (A.dExt α) = A.dExt (A.degFld k α) ∧ A.degFld 0 (A.dExt α) = 0 := by
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · have h := loc_linear (degPart n k) α x.1.1
    rw [dExt_apply, show A.loc (A.degFld k α) x.1.1 = _ from h, degFld_apply, dExt_apply, map_add,
      (degPart_opAt _ k (A.loc_diffAt hα x)).1, (degPart_opAt _ k (A.loc_diffAt hα x)).1]
  · rw [degFld_apply, dExt_apply, map_add, (degPart_opAt _ k (A.loc_diffAt hα x)).2,
      (degPart_opAt _ k (A.loc_diffAt hα x)).2, add_zero, Pi.zero_apply]

variable (A) in

theorem isDga : GlobalTheory.PD.IsDga A.parForms A.dForms where
  sg_sg α := Subtype.ext (funext fun x => par_par (α.1 x))
  d_sg α := Subtype.ext (dExt_parFld α.2)
  d_mul α β := Subtype.ext (dExt_mul α.2 β.2)
  d_d α := Subtype.ext (dExt_dExt α.2)

theorem loc_prop {P : Alt n → Prop} (h₀ : P 0) {α : A.Fld} (hα : ∀ x, P (α x)) (i : A.ι) (v : V n) : P (A.loc α i v) := by
  unfold loc
  split_ifs
  exacts [hα _, h₀]

theorem IsDeg.dExt {k : ℕ} {α : A.Fld} (hα : A.IsDeg k α) : A.IsDeg (k + 1) (A.dExt α) := fun x =>
  (hasDeg_opAt .inl (loc_prop (.zero k) hα x.1.1)).add (hasDeg_opAt .inr (loc_prop (.zero k) hα x.1.1))

theorem IsDeg.mul {k l : ℕ} {α β : A.Fld} (hα : A.IsDeg k α) (hβ : A.IsDeg l β) : A.IsDeg (k + l) (α * β) :=
  fun x => (hα x).mul (hβ x)

theorem isDeg_degFld (k : ℕ) (α : A.Fld) : A.IsDeg k (A.degFld k α) := fun x => hasDeg_degPart k (α x)

theorem IsDeg.degFld_eq {k : ℕ} {α : A.Fld} (hα : A.IsDeg k α) : A.degFld k α = α :=
  funext fun x => ((hα x).degPart_eq k).trans (if_pos rfl)

theorem IsDeg.parFld_eq {k : ℕ} {α : A.Fld} (hα : A.IsDeg k α) : A.parFld α = (-1 : ℂ) ^ k • α :=
  funext fun x => (hα x).par_eq

theorem IsDeg.mul_comm {k l : ℕ} {α β : A.Fld} (hα : A.IsDeg k α) (hβ : A.IsDeg l β) :
    α * β = (-1 : ℂ) ^ (k * l) • (β * α) :=
  funext fun x => (hα x).mul_comm (hβ x)

theorem typeGe_iff {p : ℕ} {α : A.Fld} : A.TypeGe p α ↔ ∀ x, α x ∈ holGe n p :=
  forall_congr' fun x => (mem_holGe_iff (α x)).symm

theorem TypeGe.mul {p q : ℕ} {α β : A.Fld} (hα : A.TypeGe p α) (hβ : A.TypeGe q β) : A.TypeGe (p + q) (α * β) :=
  typeGe_iff.2 fun x => mul_mem_holGe (typeGe_iff.1 hα x) (typeGe_iff.1 hβ x)

theorem TypeGe.dExt {p : ℕ} {α : A.Fld} (hα : A.TypeGe p α) : A.TypeGe p (A.dExt α) :=
  typeGe_iff.2 fun x => add_mem (opAt_mem_holGe .inl (loc_prop (zero_mem _) (typeGe_iff.1 hα) x.1.1))
    (opAt_mem_holGe .inr (loc_prop (zero_mem _) (typeGe_iff.1 hα) x.1.1))

theorem TypeGe.eq_zero {p : ℕ} {α : A.Fld} (hα : A.TypeGe p α) (hp : n < p) : α = 0 :=
  funext fun x => (bas n).ext_elem fun S => by
    by_contra h
    exact ((hα x S (by simpa using h)).trans (holCount_le S)).not_gt hp

variable {A' A''}

theorem IsHolo.comp {f : M' → M} {g : M'' → M'} (hf : A.IsHolo A' f) (hg : A'.IsHolo A'' g) : A.IsHolo A'' (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun l i v hv => ?_⟩
  obtain ⟨j, hj⟩ := A'.cover (g ((A''.e l).symm v))
  have hU := (A''.e l).isOpen_inter_preimage_symm ((A'.e j).open_source.preimage hg.1)
  have hW := (A'.e j).isOpen_inter_preimage_symm ((A.e i).open_source.preimage hf.1)
  have d₁ := (hg.2 l j).differentiableAt (hU.mem_nhds ⟨hv.1, hj⟩)
  have d₂ := (hf.2 j i).differentiableAt (hW.mem_nhds (x := A'.e j (g ((A''.e l).symm v)))
    ⟨(A'.e j).map_source hj, by rw [Set.mem_preimage, (A'.e j).left_inv hj]; exact hv.2⟩)
  refine ((d₂.comp v d₁).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hU.mem_nhds ⟨hv.1, hj⟩] with w hw
  have hw' : g ((A''.e l).symm w) ∈ (A'.e j).source := hw.2
  simp only [Function.comp, (A'.e j).left_inv hw']

variable (A A') in

def pullbackAlg (f : M' → M) : A.Fld →ₐ[ℂ] A'.Fld :=
  AlgHom.pi fun x => (pull (fderiv ℂ (A.e (A.cover (f x.pt)).choose ∘ f ∘ x.ch.symm) x.crd)).comp
    (Pi.evalAlgHom ℂ _ ⟨(_, f x.pt), (A.cover (f x.pt)).choose_spec⟩)

@[simp] theorem pullbackAlg_apply (f : M' → M) (α : A.Fld) : A.pullbackAlg A' f α = A.pullback A' f α := rfl

theorem IsForm.pullback {f : M' → M} (hf : A.IsHolo A' f) {α : A.Fld} (hα : A.IsForm α) : A'.IsForm (A.pullback A' f α) :=
  PullbackForm.isForm_pullback M M' n n' A A' f α hf hα

theorem dExt_pullback {f : M' → M} (hf : A.IsHolo A' f) {α : A.Fld} (hα : A.IsForm α) :
    A'.dExt (A.pullback A' f α) = A.pullback A' f (A.dExt α) := by
  rw [dExt, (pullback_del_dbar A A' f α hf hα).1, (pullback_del_dbar A A' f α hf hα).2]
  exact (map_add (A.pullbackAlg A' f) (A.del α) (A.dbar α)).symm

theorem IsDeg.pullback (f : M' → M) {k : ℕ} {α : A.Fld} (hα : A.IsDeg k α) : A'.IsDeg k (A.pullback A' f α) :=
  fun _ => (hα _).pull _

theorem TypeGe.pullback (f : M' → M) {p : ℕ} {α : A.Fld} (hα : A.TypeGe p α) : A'.TypeGe p (A.pullback A' f α) :=
  typeGe_iff.2 fun _ => pull_mem_holGe _ (typeGe_iff.1 hα _)

end HolAtlas

end GlobalTheory.CxForm
end
end

section
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' M'' : Type} [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace M''] {n n' n'' : ℕ}
  (A : HolAtlas M n) (A' : HolAtlas M' n') (A'' : HolAtlas M'' n'')

def closedForms (k : ℕ) : Submodule ℂ A.Fld where
  carrier := {α | A.IsForm α ∧ A.IsDeg k α ∧ A.dExt α = 0}
  add_mem' ha hb := ⟨A.forms.add_mem ha.1 hb.1, fun x => (ha.2.1 x).add (hb.2.1 x),
    by rw [dExt_add ha.1 hb.1, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨A.forms.zero_mem, fun _ => .zero k, A.dExt_zero⟩
  smul_mem' c _ ha := ⟨A.forms.smul_mem ha.1 c, fun x => (ha.2.1 x).smul c, by rw [dExt_smul c ha.1, ha.2.2, smul_zero]⟩

def exactForms (k : ℕ) : Submodule ℂ A.Fld where
  carrier := {α | A.IsDeg k α ∧ ∃ η, A.IsForm η ∧ α = A.dExt η}
  add_mem' ha hb := by
    obtain ⟨h₁, η, hη, rfl⟩ := ha
    obtain ⟨h₂, η', hη', rfl⟩ := hb
    exact ⟨fun x => (h₁ x).add (h₂ x), η + η', A.forms.add_mem hη hη', (dExt_add hη hη').symm⟩
  zero_mem' := ⟨fun _ => .zero k, 0, A.forms.zero_mem, A.dExt_zero.symm⟩
  smul_mem' c _ ha := by
    obtain ⟨h₁, η, hη, rfl⟩ := ha
    exact ⟨fun x => (h₁ x).smul c, c • η, A.forms.smul_mem hη c, (dExt_smul c hη).symm⟩

variable {A}

theorem mem_closedForms {k : ℕ} {α : A.Fld} : α ∈ A.closedForms k ↔ A.IsForm α ∧ A.IsDeg k α ∧ A.dExt α = 0 := Iff.rfl


theorem mem_exactForms_succ {k : ℕ} {α : A.Fld} :
    α ∈ A.exactForms (k + 1) ↔ ∃ η, A.IsForm η ∧ A.IsDeg k η ∧ α = A.dExt η := by
  constructor
  · rintro ⟨h, η, hη, rfl⟩
    exact ⟨A.degFld k η, hη.degFld k, isDeg_degFld k η, (h.degFld_eq.symm.trans (degFld_dExt hη k).1)⟩
  · rintro ⟨η, hη, hk, rfl⟩
    exact ⟨hk.dExt, η, hη, rfl⟩

variable (A) in

theorem exactForms_zero : A.exactForms 0 = ⊥ := by
  refine eq_bot_iff.2 fun α ⟨h, η, hη, e⟩ => ?_
  rw [Submodule.mem_bot, ← h.degFld_eq, e]
  exact (degFld_dExt hη 0).2


variable (A) in

def HSm (k : ℕ) : Type := A.closedForms k ⧸ (A.exactForms k).submoduleOf (A.closedForms k)

instance (k : ℕ) : AddCommGroup (A.HSm k) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (k : ℕ) : Module ℂ (A.HSm k) := inferInstanceAs (Module ℂ (_ ⧸ _))

namespace HSm

variable (A) in

def mk (k : ℕ) : A.closedForms k →ₗ[ℂ] A.HSm k := Submodule.mkQ _

theorem mk_surjective (k : ℕ) : Function.Surjective (mk A k) := Submodule.mkQ_surjective _

theorem mk_eq_zero {k : ℕ} (α : A.closedForms k) : mk A k α = 0 ↔ (α : A.Fld) ∈ A.exactForms k :=
  (Submodule.Quotient.mk_eq_zero _).trans Iff.rfl

@[elab_as_elim] theorem induction_on {k : ℕ} {P : A.HSm k → Prop} (c : A.HSm k) (h : ∀ α, P (mk A k α)) : P c := by
  obtain ⟨α, rfl⟩ := mk_surjective k c
  exact h α

variable (A) in

def fil (p k : ℕ) : Submodule ℂ (A.HSm k) where
  carrier := {c | ∃ α : A.closedForms k, A.TypeGe p α ∧ mk A k α = c}
  add_mem' := by
    rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
    exact ⟨α + β, typeGe_iff.2 fun x => add_mem (typeGe_iff.1 hα x) (typeGe_iff.1 hβ x), map_add _ _ _⟩
  zero_mem' := ⟨0, typeGe_iff.2 fun _ => zero_mem _, map_zero _⟩
  smul_mem' c := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨c • α, typeGe_iff.2 fun x => Submodule.smul_mem _ c (typeGe_iff.1 hα x), map_smul _ _ _⟩

variable (A) in

theorem fil_zero (k : ℕ) : fil A 0 k = ⊤ :=
  eq_top_iff.2 fun c _ => induction_on c fun α => ⟨α, fun _ _ _ => Nat.zero_le _, rfl⟩

variable (A) in

theorem fil_eq_bot {p : ℕ} (hp : n < p) (k : ℕ) : fil A p k = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨α, hα, rfl⟩
  rw [Submodule.mem_bot, show α = 0 from Subtype.ext (hα.eq_zero hp), map_zero]

variable (A) in

def mulClosed (k l : ℕ) : A.closedForms k →ₗ[ℂ] A.closedForms l →ₗ[ℂ] A.closedForms (k + l) :=
  LinearMap.mk₂ ℂ (fun α β => ⟨α * β, A.forms.mul_mem α.2.1 β.2.1, α.2.2.1.mul β.2.2.1,
      by rw [dExt_mul α.2.1 β.2.1, α.2.2.2, β.2.2.2, zero_mul, mul_zero, add_zero]⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _)) (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _)) (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

theorem exact_mul {k l : ℕ} {α β : A.Fld} (hα : α ∈ A.exactForms k) (hβ : β ∈ A.closedForms l) :
    α * β ∈ A.exactForms (k + l) := by
  obtain ⟨h, η, hη, rfl⟩ := hα
  refine ⟨h.mul hβ.2.1, η * β, A.forms.mul_mem hη hβ.1, ?_⟩
  rw [dExt_mul hη hβ.1, hβ.2.2, mul_zero, add_zero]

theorem mul_exact {k l : ℕ} {α β : A.Fld} (hα : α ∈ A.closedForms k) (hβ : β ∈ A.exactForms l) :
    α * β ∈ A.exactForms (k + l) := by
  obtain ⟨h, η, hη, rfl⟩ := hβ
  refine ⟨hα.2.1.mul h, A.parFld α * η, A.forms.mul_mem hα.1.parFld hη, ?_⟩
  rw [dExt_mul hα.1.parFld hη, dExt_parFld hα.1, hα.2.2, map_zero, neg_zero, zero_mul, zero_add]
  exact congrArg (· * _) (funext fun x => (par_par (α x)).symm)

variable (A) in

def cup (k l : ℕ) : A.HSm k →ₗ[ℂ] A.HSm l →ₗ[ℂ] A.HSm (k + l) :=
  LinearMap.liftQ₂ _ _ ((mulClosed A k l).compr₂ (mk A (k + l)))
    (fun α hα => LinearMap.ext fun β => (mk_eq_zero _).2 (exact_mul hα β.2))
    (fun β hβ => LinearMap.ext fun α => (mk_eq_zero _).2 (mul_exact α.2 hβ))

variable (A) in

def oneClosed : A.closedForms 0 := ⟨1, A.forms.one_mem, fun _ => by simpa using hasDeg_algebraMap (n := n) 1, A.dExt_one⟩

variable (A) in

def one : A.HSm 0 := mk A 0 (oneClosed A)

variable {A'}

def pullClosed {f : M' → M} (hf : A.IsHolo A' f) (k : ℕ) : A.closedForms k →ₗ[ℂ] A'.closedForms k where
  toFun α := ⟨A.pullback A' f α, α.2.1.pullback hf, α.2.2.1.pullback f,
    by rw [dExt_pullback hf α.2.1, α.2.2.2]; exact map_zero (A.pullbackAlg A' f)⟩
  map_add' α β := Subtype.ext (map_add (A.pullbackAlg A' f) (α : A.Fld) β)
  map_smul' c α := Subtype.ext (map_smul (A.pullbackAlg A' f) c (α : A.Fld))

theorem pullback_exact {f : M' → M} (hf : A.IsHolo A' f) {k : ℕ} {α : A.Fld} (hα : α ∈ A.exactForms k) :
    A.pullback A' f α ∈ A'.exactForms k := by
  obtain ⟨h, η, hη, rfl⟩ := hα
  exact ⟨h.pullback f, A.pullback A' f η, hη.pullback hf, (dExt_pullback hf hη).symm⟩

def pull {f : M' → M} (hf : A.IsHolo A' f) (k : ℕ) : A.HSm k →ₗ[ℂ] A'.HSm k :=
  Submodule.mapQ _ _ (pullClosed hf k) fun α hα => pullback_exact hf hα

end HSm

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem hasDeg_zero_dim (α : Alt 0) : HasDeg 0 α := fun S _ =>
  Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a _ => absurd a.2 (by simp))

def pt₀ : (std 0).Pt := ⟨((), 0), Set.mem_univ _⟩

theorem eq_pt₀ (x : (std 0).Pt) : x = pt₀ := Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))

theorem isForm_std₀ (α : (std 0).Fld) : (std 0).IsForm α := by
  refine ⟨fun i S => contDiffOn_const.congr fun v _ => congrArg (fun w => (bas 0).repr ((std 0).loc α i w) S)
    (Subsingleton.elim v 0), fun x x' _ => ?_⟩
  rw [eq_pt₀ x', eq_pt₀ x, (hasDeg_zero_dim (α pt₀)).eq_algebraMap, AlgHom.commutes]

theorem dExt_std₀ (α : (std 0).Fld) : (std 0).dExt α = 0 :=
  funext fun x => by simp [dExt_apply, opAt]

theorem mem_closedForms_std₀ (α : (std 0).Fld) : α ∈ (std 0).closedForms 0 :=
  ⟨isForm_std₀ α, fun x => hasDeg_zero_dim _, dExt_std₀ α⟩

def evStd₀ : (std 0).closedForms 0 →ₗ[ℂ] ℂ :=
  (bas 0).coord ∅ ∘ₗ LinearMap.proj pt₀ ∘ₗ ((std 0).closedForms 0).subtype

def HSm.std₀Equiv : (std 0).HSm 0 ≃ₗ[ℂ] ℂ := by
  refine LinearEquiv.ofBijective (Submodule.liftQ _ evStd₀ fun α hα => ?_) ⟨?_, fun z => ?_⟩
  · have h : (α : (std 0).Fld) ∈ (std 0).exactForms 0 := hα
    rw [exactForms_zero, Submodule.mem_bot] at h
    simp [evStd₀, h]
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    induction c using HSm.induction_on with
    | h α =>
      have e : (α : (std 0).Fld) = 0 := funext fun x => by
        rw [eq_pt₀ x, (hasDeg_zero_dim (α.1 pt₀)).eq_algebraMap]
        have : (bas 0).repr (α.1 pt₀) ∅ = 0 := hc
        rw [this, map_zero]; rfl
      rw [show α = 0 from Subtype.ext e]
      exact map_zero _
  · refine ⟨HSm.mk _ 0 ⟨z • 1, mem_closedForms_std₀ _⟩, ?_⟩
    change (bas 0).repr ((z • (1 : (std 0).Fld)) pt₀) ∅ = z
    rw [Pi.smul_apply, Pi.one_apply, ← bas_empty, map_smul, Module.Basis.repr_self]
    simp

theorem HSm.std₀Equiv_one : HSm.std₀Equiv (HSm.one (std 0)) = 1 := by
  change (bas 0).repr ((1 : (std 0).Fld) pt₀) ∅ = 1
  rw [Pi.one_apply, ← bas_empty, Module.Basis.repr_self]
  simp

theorem HSm.finrank_std₀ : Module.finrank ℂ ((std 0).HSm 0) = 1 :=
  (HSm.std₀Equiv.finrank_eq).trans (Module.finrank_self ℂ)

def zFld : (std 1).Fld := fun x => algebraMap ℂ (Alt 1) (x.crd 0)


theorem dExt_zFld (x : (std 1).Pt) : (std 1).dExt zFld x = dz 0 := by
  have hl : (std 1).loc zFld x.1.1 = fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v • bas 1 ∅ := funext fun v => by
    rw [loc, dif_pos (show v ∈ ((std 1).e x.1.1).target from Set.mem_univ v)]
    unfold zFld
    rw [Algebra.algebraMap_eq_smul_one, bas_empty]
    rfl
  have hd : DifferentiableAt ℂ (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) x.crd :=
    (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).differentiableAt
  rw [dExt_apply, hl, opAt, opAt, Fin.sum_univ_one, Fin.sum_univ_one,
    coefwise_smul (T := fun f => dirD (Sum.inl 0) f x.crd) (dirD_zero _) (fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v) ∅,
    coefwise_smul (T := fun f => dirD (Sum.inr 0) f x.crd) (dirD_zero _) (fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v) ∅]
  simp only [Fin.sum_univ_one, dirD, del_eq_fderiv hd, dbar_eq_zero hd, ContinuousLinearMap.fderiv, zero_smul,
    ContinuousLinearMap.zero_apply, mul_zero, add_zero, bas_empty, coordVec]
  simp [dz]

theorem dExt_zFld_ne_zero : (std 1).dExt zFld ≠ 0 := fun h => by
  let x₀ : (std 1).Pt := ⟨(((std 1).cover 0).choose, 0), ((std 1).cover 0).choose_spec⟩
  have e : (0 : Alt 1) = dz 0 := by rw [← dExt_zFld x₀, h]; rfl
  rw [dz, ← bas_singleton] at e
  exact (bas 1).ne_zero _ e.symm

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}}

def algAtlas (p : X ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] (σ : k →+* ℂ) : HolAtlas (CxPts p σ) D where
  ι := AlgChart p σ D
  e c := c.e
  cover y := AlgChart.exists_mem_source y
  holo c c' := c.holo_trans c'


end GlobalTheory.CxForm

namespace GlobalTheory.CxForm.HolAtlas

example : Module.finrank ℂ ((std 0).HSm 0) = 1 := HSm.finrank_std₀

example : (std 1).dExt zFld ≠ 0 := dExt_zFld_ne_zero

example {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β)
    (h : A.IsDeg 1 α) : A.dExt (α * β) = A.dExt α * β - α * A.dExt β := by
  rw [dExt_mul hα hβ, h.parFld_eq, pow_one, neg_one_smul, neg_mul, sub_eq_add_neg]

example {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (k : ℕ) : HSm.fil A 0 k = ⊤ := HSm.fil_zero A k

end GlobalTheory.CxForm.HolAtlas
end
end
