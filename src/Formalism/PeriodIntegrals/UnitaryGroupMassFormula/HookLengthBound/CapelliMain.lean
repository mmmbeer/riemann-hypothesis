import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf

section
noncomputable section

namespace PI.HookSteps.Cap

open MvPolynomial

section Abs

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

def xw (x : I → S → 𝒰) {k : ℕ} (r : Fin k → I) (s : Fin k → S) : 𝒰 :=
  (List.ofFn fun j => x (r j) (s j)).prod

def dw (d : I → S → 𝒰) {k : ℕ} (g : Fin k → I) (s : Fin k → S) : 𝒰 :=
  (List.ofFn fun j => d (g j) (s j)).prod

def Pn (x d : I → S → 𝒰) {k : ℕ} (r g : Fin k → I) : 𝒰 :=
  ∑ s : Fin k → S, xw x r s * dw d g s

def Eop (x d : I → S → 𝒰) (a b : I) : 𝒰 := ∑ t : S, x a t * d b t

def Lw (x d : I → S → 𝒰) {k : ℕ} (r g : Fin k → I) : 𝒰 :=
  (List.ofFn fun j : Fin k =>
    Eop x d (r j) (g j) + if r j = g j then ((k : 𝒰) - 1 - ((j : ℕ) : 𝒰)) else 0).prod

end Abs

def CapAbsMain : Prop :=
  ∀ (𝒰 : Type) [Ring 𝒰] (I S : Type) [DecidableEq I] [Fintype S] [DecidableEq S]
    (x d : I → S → 𝒰), (∀ a s b t, x a s * x b t = x b t * x a s) →
    (∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) →
    ∀ (k : ℕ) (r g : Fin k → I),
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (Lw x d (fun j => r (σ j)) g - Pn x d (fun j => r (σ j)) g) = 0

def xo (N : ℕ) (a s : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  LinearMap.mulLeft ℚ (X (a, s))

def dop (N : ℕ) (b s : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  (pderiv (b, s) : Derivation ℚ _ _).toLinearMap

def CapSquare : Prop :=
  ∀ N : ℕ, LinearMap.mulLeft ℚ (detX N) * detD N =
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • Pn (xo N) (dop N) (fun j => σ j) id

def CapLeft : Prop :=
  ∀ N : ℕ, Formalism.CohomologicalDescent.HeightDescentMinors.capelli (polE N) (algebraMap ℚ _ ((N : ℚ) - 1)) =
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • Lw (xo N) (dop N) (fun j => σ j) id

def CapRel : Prop :=
  ∀ N : ℕ, (∀ a s b t, xo N a s * xo N b t = xo N b t * xo N a s) ∧
    (∀ a s b t, dop N b t * xo N a s = xo N a s * dop N b t + if a = b ∧ s = t then 1 else 0)

theorem detDetId_of (hA : CapAbsMain) (hS : CapSquare) (hL : CapLeft) (hR : CapRel) :
    DetDetId := by
  intro N
  obtain ⟨h1, h2⟩ := hR N
  have h := hA (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) (Fin N) (Fin N) (xo N) (dop N)
    h1 h2 N id id
  simp only [id_eq, smul_sub, Finset.sum_sub_distrib] at h
  rw [hS N, hL N]
  exact (sub_eq_zero.1 h).symm

end PI.HookSteps.Cap
end
end

section
noncomputable section

namespace PI.HookSteps.Cap

open Finset

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

theorem xw_succ (x : I → S → 𝒰) {k : ℕ} (r : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    xw x r s = x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
  unfold xw
  rw [List.ofFn_succ, List.prod_cons]

theorem dw_succ (d : I → S → 𝒰) {k : ℕ} (g : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    dw d g s = d (g 0) (s 0) * dw d (fun i => g i.succ) (fun i => s i.succ) := by
  unfold dw
  rw [List.ofFn_succ, List.prod_cons]

theorem xw_zero (x : I → S → 𝒰) (r : Fin 0 → I) (s : Fin 0 → S) : xw x r s = 1 := by
  unfold xw
  simp

theorem sum_fun_succ {M : Type} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → S) → M) :
    ∑ s, f s = ∑ t : S, ∑ s : Fin k → S, f (Fin.cons t s) := by
  rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
  rfl


theorem dx_key (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) :
    ∀ (k : ℕ) (r : Fin k → I) (s : Fin k → S) (a b : I) (t : S),
      x a t * (d b t * xw x r s) = x a t * xw x r s * d b t +
        ∑ j, if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0 := by
  intro k
  induction k with
  | zero =>
    intro r s a b t
    simp [xw_zero]
  | succ k ih =>
    intro r s a b t
    have h1 : xw x (Function.update r 0 a) s =
        x a (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
      have hf : (fun i : Fin k => Function.update r 0 a i.succ) = fun i => r i.succ :=
        funext fun i => by rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]
      rw [xw_succ, hf, Function.update_apply, if_pos rfl]
    have h2 : ∀ j : Fin k, xw x (Function.update r j.succ a) s =
        x (r 0) (s 0) * xw x (Function.update (fun i => r i.succ) j a) (fun i => s i.succ) := by
      intro j
      have hf : (fun i : Fin k => Function.update r j.succ a i.succ) =
          Function.update (fun i => r i.succ) j a :=
        Function.update_comp_eq_of_injective r (Fin.succ_injective k) j a
      rw [xw_succ, hf, Function.update_apply, if_neg (Fin.succ_ne_zero j).symm]
    have key : x a t * (x (r 0) (s 0) * (d b t * xw x (fun i => r i.succ) (fun i => s i.succ))) =
        x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) +
        ∑ j : Fin k, if r j.succ = b ∧ s j.succ = t then
          xw x (Function.update r j.succ a) s else 0 := by
      rw [← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih, mul_add,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2 j, mul_ite, mul_zero]
    have c0 : x a t * ((if r 0 = b ∧ s 0 = t then (1 : 𝒰) else 0) *
        xw x (fun i => r i.succ) (fun i => s i.succ)) =
        if r 0 = b ∧ s 0 = t then xw x (Function.update r 0 a) s else 0 := by
      split_ifs with h
      · rw [h1, h.2, one_mul]
      · rw [zero_mul, mul_zero]
    have m : x (r 0) (s 0) * (x a t * xw x (fun i => r i.succ) (fun i => s i.succ) * d b t) =
        x a t * (x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ)) * d b t := by
      simp only [mul_assoc]
      rw [← mul_assoc, hxx (r 0) (s 0) a t, mul_assoc]
    rw [xw_succ x r s, Fin.sum_univ_succ, ← c0, ← mul_assoc (d b t), hdx (r 0) (s 0) b t,
      add_mul, mul_add, mul_assoc (x (r 0) (s 0)) (d b t), key, m]
    abel

theorem E_Pn (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (r g : Fin k → I) (a b : I) :
    Eop x d a b * Pn x d r g = Pn x d (Fin.cons a r) (Fin.cons b g) +
      ∑ j, if r j = b then Pn x d (Function.update r j a) g else 0 := by
  have first : Pn x d (Fin.cons a r) (Fin.cons b g) =
      ∑ t, ∑ s : Fin k → S, x a t * xw x r s * (d b t * dw d g s) := by
    unfold Pn
    rw [sum_fun_succ]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    rw [xw_succ, dw_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_assoc]
  have second : ∀ j : Fin k, (if r j = b then Pn x d (Function.update r j a) g else 0) =
      ∑ t, ∑ s : Fin k → S,
        (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s := by
    intro j
    rw [Finset.sum_comm]
    unfold Pn
    split_ifs with h
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp [h]
    · simp [h]
  have term : ∀ (t : S) (s : Fin k → S), x a t * d b t * (xw x r s * dw d g s) =
      x a t * xw x r s * (d b t * dw d g s) +
      ∑ j, (if r j = b ∧ s j = t then xw x (Function.update r j a) s else 0) * dw d g s := by
    intro t s
    rw [mul_assoc (x a t), ← mul_assoc (d b t), ← mul_assoc (x a t), dx_key x d hxx hdx k r s a b t,
      add_mul, Finset.sum_mul, mul_assoc (x a t * xw x r s)]
  rw [first]
  simp_rw [second]
  unfold Eop Pn
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, term, Finset.sum_add_distrib]
  congr 1
  exact (Finset.sum_congr rfl fun t _ => Finset.sum_comm).trans Finset.sum_comm

end PI.HookSteps.Cap
end
end

section
noncomputable section

namespace PI.HookSteps.Cap

open Finset

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

theorem Lw_succ (x d : I → S → 𝒰) {k : ℕ} (w g : Fin (k + 1) → I) :
    Lw x d w g = (Eop x d (w 0) (g 0) + if w 0 = g 0 then (k : 𝒰) else 0) *
      Lw x d (fun i => w i.succ) (fun i => g i.succ) := by
  unfold Lw
  rw [List.ofFn_succ, List.prod_cons]
  congr 1
  · simp
  · congr 2
    funext j
    split_ifs
    · push_cast [Fin.val_succ]
      abel
    · rfl

theorem Pn_succ (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (w g : Fin (k + 1) → I) :
    Pn x d w g = Eop x d (w 0) (g 0) * Pn x d (fun i => w i.succ) (fun i => g i.succ) -
      ∑ j : Fin k, if w j.succ = g 0 then
        Pn x d (Function.update (fun i => w i.succ) j (w 0)) (fun i => g i.succ) else 0 := by
  have h := E_Pn x d hxx hdx (fun i => w i.succ) (fun i => g i.succ) (w 0) (g 0)
  have hw : (Fin.cons (w 0) (fun i => w i.succ) : Fin (k + 1) → I) = w := Fin.cons_self_tail w
  have hg : (Fin.cons (g 0) (fun i => g i.succ) : Fin (k + 1) → I) = g := Fin.cons_self_tail g
  rw [hw, hg] at h
  rw [h]
  abel

theorem D_succ (x d : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0)
    {k : ℕ} (w g : Fin (k + 1) → I) :
    Lw x d w g - Pn x d w g =
      (Eop x d (w 0) (g 0) + if w 0 = g 0 then (k : 𝒰) else 0) *
        (Lw x d (fun i => w i.succ) (fun i => g i.succ) -
          Pn x d (fun i => w i.succ) (fun i => g i.succ)) +
      (k : ℕ) • (if w 0 = g 0 then Pn x d (fun i => w i.succ) (fun i => g i.succ) else 0) +
      ∑ j : Fin k, if w j.succ = g 0 then
        Pn x d (Function.update (fun i => w i.succ) j (w 0)) (fun i => g i.succ) else 0 := by
  rw [Lw_succ, Pn_succ x d hxx hdx]
  have hc : (if w 0 = g 0 then (k : 𝒰) else 0) * Pn x d (fun i => w i.succ) (fun i => g i.succ) =
      (k : ℕ) • (if w 0 = g 0 then Pn x d (fun i => w i.succ) (fun i => g i.succ) else 0) := by
    split_ifs <;> simp [nsmul_eq_mul]
  rw [mul_sub, add_mul (Eop x d (w 0) (g 0)),
    add_mul (Eop x d (w 0) (g 0)) _ (Pn x d (fun i => w i.succ) (fun i => g i.succ)), hc]
  abel

theorem alt_first {k : ℕ} (F : I → 𝒰) (Δ : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I)
    (hIH : ∀ r' : Fin k → I,
      ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun j => r' (τ j)) = 0) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      (F (r (σ 0)) * Δ (fun i => r (σ i.succ))) = 0 := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp only [Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  have h0 : ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      Δ (fun i => r (Equiv.swap 0 p (τ i).succ)) = 0 := hIH (fun j => r (Equiv.swap 0 p j.succ))
  calc _ = F (r p) * (((if p = 0 then 1 else -1 : ℤˣ) : ℤ) • ∑ τ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun i => r (Equiv.swap 0 p (τ i).succ))) := by
        rw [Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Units.val_mul, mul_smul, mul_smul_comm, mul_smul_comm]
    _ = 0 := by rw [h0, smul_zero, mul_zero]

theorem alt_contract {k : ℕ} (Q : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I) (b : I) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) = 0 := by
  obtain ⟨A, hA⟩ : ∃ A : Equiv.Perm (Fin (k + 1)) → 𝒰,
      ∀ σ, A σ = if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0 := ⟨_, fun _ => rfl⟩
  have hB : ∀ (σ : Equiv.Perm (Fin (k + 1))) (j : Fin k),
      (if r (σ j.succ) = b then Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) =
        A (σ * Equiv.swap 0 j.succ) := by
    intro σ j
    have hf : Function.update (fun i => r (σ i.succ)) j (r (σ 0)) =
        fun i => r (σ (Equiv.swap 0 j.succ i.succ)) := by
      funext i
      by_cases h : i = j
      · subst h
        rw [Function.update_apply, if_pos rfl, Equiv.swap_apply_right]
      · rw [Function.update_apply, if_neg h, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
          (fun e => h (Fin.succ_injective _ e))]
    rw [hA]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [hf]
  have hS : ∀ j : Fin k, ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      A (σ * Equiv.swap 0 j.succ) =
      -∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A σ := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (k + 1)) j.succ)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (Fin.succ_ne_zero j).symm, Units.val_mul, Units.val_neg, Units.val_one,
      mul_neg_one, neg_smul]
  have e : ∀ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      ((k : ℕ) • (if r (σ 0) = b then Q (fun i => r (σ i.succ)) else 0) +
        ∑ j : Fin k, if r (σ j.succ) = b then
          Q (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) else 0) =
      (k : ℕ) • (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A σ) +
        ∑ j : Fin k, ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • A (σ * Equiv.swap 0 j.succ) := by
    intro σ
    rw [smul_add, Finset.smul_sum, smul_comm ((Equiv.Perm.sign σ : ℤˣ) : ℤ) (k : ℕ), ← hA σ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB σ j]
  rw [Finset.sum_congr rfl fun σ _ => e σ, Finset.sum_add_distrib, Finset.sum_comm,
    ← Finset.smul_sum]
  simp_rw [hS]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_neg, add_neg_cancel]

theorem capelli_absolute_value : CapAbsMain := by
  unfold CapAbsMain
  intro 𝒰 _ I S _ _ _ x d hxx hdx k
  induction k with
  | zero =>
    intro r g
    simp only [Lw, Pn, xw, dw]
    simp
  | succ k ih =>
    intro r g
    have h1 := alt_first (fun a => Eop x d a (g 0) + if a = g 0 then (k : 𝒰) else 0)
      (fun w' => Lw x d w' (fun i => g i.succ) - Pn x d w' (fun i => g i.succ)) r
      (fun r' => ih r' (fun i => g i.succ))
    have h2 := alt_contract (fun w' => Pn x d w' (fun i => g i.succ)) r (g 0)
    calc _ = ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            ((Eop x d (r (σ 0)) (g 0) + if r (σ 0) = g 0 then (k : 𝒰) else 0) *
              (Lw x d (fun i => r (σ i.succ)) (fun i => g i.succ) -
                Pn x d (fun i => r (σ i.succ)) (fun i => g i.succ))) +
          ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            ((k : ℕ) • (if r (σ 0) = g 0 then Pn x d (fun i => r (σ i.succ)) (fun i => g i.succ)
                else 0) +
              ∑ j : Fin k, if r (σ j.succ) = g 0 then
                Pn x d (Function.update (fun i => r (σ i.succ)) j (r (σ 0))) (fun i => g i.succ)
                else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← smul_add, D_succ x d hxx hdx, add_assoc]
      _ = 0 + 0 := congrArg₂ (· + ·) h1 h2
      _ = 0 := add_zero 0

end PI.HookSteps.Cap
end
end
