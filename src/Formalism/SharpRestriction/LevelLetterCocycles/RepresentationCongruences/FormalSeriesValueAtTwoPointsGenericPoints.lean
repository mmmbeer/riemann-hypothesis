import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Filtration
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Log.Base

section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

open PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

def T (O : Type*) [CommRing O] [IsLocalRing O] (N : ℕ) : Ideal O⟦X⟧ where
  carrier := {x | ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m)}
  add_mem' {a b} ha hb m := by
    simpa only [map_add] using Ideal.add_mem _ (ha m) (hb m)
  zero_mem' m := by simp
  smul_mem' c x hx m := by
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h2 : p.2 ≤ m := by have := Finset.mem_antidiagonal.mp hp; omega
    exact Ideal.pow_le_pow_right (by omega) (hx p.2)

theorem mem_T {N : ℕ} {x : O⟦X⟧} :
    x ∈ T O N ↔ ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := Iff.rfl

theorem T_anti {N N' : ℕ} (h : N ≤ N') : T O N' ≤ T O N := by
  intro x hx
  rw [mem_T] at hx ⊢
  exact fun m => Ideal.pow_le_pow_right (by omega) (hx m)

theorem T_mul {a b : ℕ} {x y : O⟦X⟧} (hx : x ∈ T O a) (hy : y ∈ T O b) : x * y ∈ T O (a + b) := by
  rw [mem_T] at hx hy ⊢
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have h := Finset.mem_antidiagonal.mp hp
  have h2 := Ideal.mul_mem_mul (hx p.1) (hy p.2)
  rw [← pow_add] at h2
  exact Ideal.pow_le_pow_right (by omega) h2

private theorem maximalIdeal_pow_smul_whole_ring_eq_self (n : ℕ) :
    ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O) = (IsLocalRing.maximalIdeal O) ^ n := by
  first
    | rw [Ideal.smul_eq_mul, Ideal.mul_top]
    | simp [Ideal.smul_eq_mul]
    | simp

theorem eq_zero_of_forall_mem_coeffFiltration {x : O⟦X⟧} (hx : ∀ N, x ∈ T O N) : x = 0 := by
  have H : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  ext m
  rw [map_zero]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero, maximalIdeal_pow_smul_whole_ring_eq_self]
  have h := (mem_T.mp (hx (n + m))) m
  rwa [Nat.add_sub_cancel] at h

variable {g : O⟦X⟧}

theorem mem_T_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : g ∈ T O 1 := by
  rw [mem_T]
  intro m
  rcases m with _ | m
  · rw [Nat.sub_zero, pow_one, coeff_zero_eq_constantCoeff_apply]
    exact hg
  · rw [show 1 - (m + 1) = 0 by omega, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem pow_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (N : ℕ) : g ^ N ∈ T O N := by
  induction N with
  | zero =>
    rw [pow_zero, mem_T]
    intro m
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    rw [pow_succ]
    exact T_mul ih (mem_T_one hg)

theorem aeval_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) {N : ℕ} {p : Polynomial O}
    (hp : ∀ d < N, p.coeff d = 0) : Polynomial.aeval g p ∈ T O N := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d < N
  · rw [hp d hd, zero_smul]
    exact Submodule.zero_mem _
  · rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _
      (T_anti (not_lt.mp hd) (pow_mem_coeffFiltration hg d))

noncomputable def S (g : O⟦X⟧) (N : ℕ) (f : O⟦X⟧) : O⟦X⟧ := Polynomial.aeval g (trunc N f)

theorem S_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) {N N' : ℕ}
    (h : N ≤ N') : S g N' f - S g N f ∈ T O N := by
  unfold S
  rw [← map_sub (Polynomial.aeval (R := O) g)]
  refine aeval_mem_coeffFiltration hg fun d hd => ?_
  have hd' : d < N' := lt_of_lt_of_le hd h
  simp [coeff_trunc, hd, hd']

theorem exists_lim (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (m : ℕ) :
    ∃ L : O, ∀ N, coeff m (S g N f) - L ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := by
  have hC : IsPrecomplete (IsLocalRing.maximalIdeal O) O := inferInstance
  obtain ⟨L, hL⟩ := hC.prec (f := fun k => coeff m (S g (k + m) f)) (fun {a b} hab => by
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self]
    have h1 := S_sub_mem hg f (show a + m ≤ b + m by omega) m
    rw [map_sub, Nat.add_sub_cancel] at h1
    have h2 := neg_mem h1
    rw [neg_sub] at h2
    exact h2)
  refine ⟨L, fun N => ?_⟩
  rcases le_or_gt m N with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    have h3 := hL k
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self] at h3
    rw [Nat.add_sub_cancel]
    exact h3
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

noncomputable def subst (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) : O⟦X⟧ :=
  PowerSeries.mk fun m => Classical.choose (exists_lim hg f m)

theorem subst_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (N : ℕ) :
    subst hg f - S g N f ∈ T O N := by
  rw [mem_T]
  intro m
  rw [map_sub]
  simp only [subst, coeff_mk]
  have h1 := Classical.choose_spec (exists_lim hg f m) N
  have h2 := neg_mem h1
  rwa [neg_sub] at h2

theorem subst_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f y : O⟦X⟧) (N0 : ℕ)
    (hy : ∀ N, N0 ≤ N → y - S g N f ∈ T O N) : y = subst hg f := by
  have key : ∀ N, y - subst hg f ∈ T O N := fun N => by
    have h1 := hy (N + N0) (by omega)
    have h2 := subst_sub_mem hg f (N + N0)
    have h3 := sub_mem h1 h2
    rw [sub_sub_sub_cancel_right] at h3
    exact T_anti (by omega) h3
  exact sub_eq_zero.mp (eq_zero_of_forall_mem_coeffFiltration key)

private theorem truncEval_add (N : ℕ) (f f' : O⟦X⟧) :
    S g N (f + f') = S g N f + S g N f' := by
  have h : trunc N (f + f') = trunc N f + trunc N f' := map_add (trunc N) f f'
  simp only [S, h, map_add]

theorem subst_add (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f + f') = subst hg f + subst hg f' := by
  refine (subst_eq hg (f + f') _ 0 fun N _ => ?_).symm
  rw [truncEval_add, add_sub_add_comm]
  exact add_mem (subst_sub_mem hg f N) (subst_sub_mem hg f' N)

private theorem truncEval_smul (N : ℕ) (r : O) (f : O⟦X⟧) :
    S g N (r • f) = r • S g N f := by
  have h : trunc N (r • f) = r • trunc N f := by
    first
      | exact map_smul (trunc N) r f
      | (ext d; simp only [coeff_trunc, Polynomial.coeff_smul, coeff_smul]; split_ifs <;> simp)
  simp only [S, h, map_smul]

theorem subst_smul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (r : O) (f : O⟦X⟧) :
    subst hg (r • f) = r • subst hg f := by
  refine (subst_eq hg (r • f) _ 0 fun N _ => ?_).symm
  rw [truncEval_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ r (subst_sub_mem hg f N)

private theorem coeff_trunc_mul_trunc_of_lt {N d : ℕ} (hd : d < N) (f f' : O⟦X⟧) :
    (trunc N f * trunc N f').coeff d = coeff d (f * f') := by
  rw [Polynomial.coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_antidiagonal.mp hx
  have h1 : x.1 < N := by omega
  have h2 : x.2 < N := by omega
  simp [coeff_trunc, h1, h2]

theorem subst_mul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f * f') = subst hg f * subst hg f' := by
  refine (subst_eq hg (f * f') _ 0 fun N _ => ?_).symm
  have hA := subst_sub_mem hg f N
  have hB := subst_sub_mem hg f' N
  have hT : S g N f * S g N f' - S g N (f * f') ∈ T O N := by
    unfold S
    rw [← map_mul (Polynomial.aeval (R := O) g), ← map_sub (Polynomial.aeval (R := O) g)]
    refine aeval_mem_coeffFiltration hg fun d hd => ?_
    rw [Polynomial.coeff_sub, coeff_trunc_mul_trunc_of_lt hd]
    simp [coeff_trunc, hd]
  have key : subst hg f * subst hg f' - S g N (f * f') =
      (subst hg f - S g N f) * subst hg f' +
        S g N f * (subst hg f' - S g N f') +
        (S g N f * S g N f' - S g N (f * f')) := by ring
  rw [key]
  exact add_mem (add_mem (Ideal.mul_mem_right _ _ hA) (Ideal.mul_mem_left _ _ hB)) hT

theorem subst_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (1 : O⟦X⟧) = 1 := by
  refine (subst_eq hg 1 1 1 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_one, map_one, sub_self]
  exact Submodule.zero_mem _

theorem subst_X (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (X : O⟦X⟧) = g := by
  refine (subst_eq hg X g 2 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_X, Polynomial.aeval_X, sub_self]
  exact Submodule.zero_mem _

noncomputable def substAlgHom (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : O⟦X⟧ →ₐ[O] O⟦X⟧ :=
  AlgHom.ofLinearMap
    { toFun := subst hg
      map_add' := subst_add hg
      map_smul' := subst_smul hg }
    (subst_one hg) (subst_mul hg)

theorem exists_algHom_X_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g := ⟨substAlgHom hg, subst_X hg⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS
end

section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierD

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def wd (g : O⟦X⟧) : ℕ := (g.map (IsLocalRing.residue O)).order.toNat

theorem constantCoeff_mem {g : O⟦X⟧} (hD : 1 ≤ wd g) :
    constantCoeff g ∈ IsLocalRing.maximalIdeal O := by
  have h0 : coeff 0 (g.map (IsLocalRing.residue O)) = 0 :=
    coeff_of_lt_order_toNat 0 (by unfold wd at hD; omega)
  rwa [coeff_map, coeff_zero_eq_constantCoeff_apply, IsLocalRing.residue_eq_zero_iff] at h0

noncomputable def poly {D : ℕ} (a : Fin D → O) : Polynomial O :=
  ∑ i : Fin D, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

theorem coeff_poly {D : ℕ} (a : Fin D → O) (n : ℕ) :
    (poly a).coeff n = if h : n < D then a ⟨n, h⟩ else 0 := by
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩ (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm)))
      (by simp)]
    simp
  · exact Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem coe_poly {D : ℕ} (a : Fin D → O) :
    ((poly a : Polynomial O) : O⟦X⟧) = ∑ i : Fin D, C (a i) * X ^ (i : ℕ) := by
  ext n
  simp only [Polynomial.coeff_coe, poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    map_sum, PowerSeries.coeff_C_mul_X_pow]

theorem degree_poly_lt {D : ℕ} (a : Fin D → O) : (poly a).degree < D :=
  Polynomial.degree_sum_fin_lt a

theorem poly_of_degree {D : ℕ} {p : Polynomial O} (hp : p.degree < D) :
    poly (fun i : Fin D => p.coeff i) = p := by
  ext n
  rw [coeff_poly]
  split_ifs with h
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hp (by exact_mod_cast (not_lt.mp h)))).symm

theorem h_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using h.commutes a

theorem sum_split {D : ℕ} (h : O⟦X⟧ →ₐ[O] O⟦X⟧) {g : O⟦X⟧} (hX : h X = g)
    (c : Fin D → O⟦X⟧) :
    ∑ i : Fin D, X ^ (i : ℕ) * h (c i) =
      ((poly fun i => constantCoeff (c i) : Polynomial O) : O⟦X⟧) +
        g * ∑ i : Fin D, X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i)) := by
  rw [coe_poly, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [eq_X_mul_shift_add_const (c i)]
  rw [map_add, map_mul, hX, h_C]
  ring

variable {g : O⟦X⟧} (hg : g.map (IsLocalRing.residue O) ≠ 0)
include hg

theorem coeff_eq_zero_of_sum_eq_zero (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) :
    ∀ n, ∀ c : Fin (wd g) → O⟦X⟧, ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0 → ∀ i, coeff n (c i) = 0 := by
  have HW := IsWeierstrassDivisor.of_map_ne_zero hg
  have step : ∀ c : Fin (wd g) → O⟦X⟧, ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0 →
      (∀ i, constantCoeff (c i) = 0) ∧
        ∑ i : Fin (wd g), X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i)) = 0 := by
    intro c hc
    rw [sum_split h hX] at hc
    have h2 : g * (∑ i : Fin (wd g), X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i))) =
        ((-poly fun i => constantCoeff (c i) : Polynomial O) : O⟦X⟧) := by
      rw [Polynomial.coe_neg]
      exact eq_neg_of_add_eq_zero_right hc
    obtain ⟨hq, hr⟩ := HW.eq_zero_of_mul_eq
      (by rw [Polynomial.degree_neg]; exact degree_poly_lt (D := wd g) _) h2
    refine ⟨fun i => ?_, hq⟩
    have := congrArg (fun p => Polynomial.coeff p i) (neg_eq_zero.mp hr)
    simpa [coeff_poly] using this
  intro n
  induction n with
  | zero =>
    intro c hc i
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (step c hc).1 i
  | succ n ih =>
    intro c hc i
    have := ih _ (step c hc).2 i
    rwa [coeff_mk] at this

theorem eq_zero_of_sum_eq_zero (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (c : Fin (wd g) → O⟦X⟧)
    (hc : ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0) : c = 0 :=
  funext fun i => PowerSeries.ext fun n => by
    simpa using coeff_eq_zero_of_sum_eq_zero hg h hX n c hc i

theorem decomp_unique (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (c c' : Fin (wd g) → O⟦X⟧)
    (hc : ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c' i)) : c = c' := by
  have := eq_zero_of_sum_eq_zero hg h hX (c - c') (by
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, hc, sub_self])
  exact sub_eq_zero.mp this

theorem injective (hD : 1 ≤ wd g) (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) :
    Function.Injective h := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have := eq_zero_of_sum_eq_zero hg h hX (fun i => if (i : ℕ) = 0 then a else 0) (by
    rw [Finset.sum_eq_single ⟨0, hD⟩ (fun j _ hj => by
      rw [if_neg (fun e => hj (Fin.ext e)), map_zero, mul_zero]) (by simp)]
    simp [ha])
  simpa using congrFun this ⟨0, hD⟩

omit hg in

noncomputable def cf (g : O⟦X⟧) (f : O⟦X⟧) (i : ℕ) : O⟦X⟧ :=
  mk fun n => ((fun q => q /ʷ g)^[n] f %ʷ g).coeff i

omit hg in
theorem constantCoeff_cf (f : O⟦X⟧) (i : ℕ) : constantCoeff (cf g f i) = (f %ʷ g).coeff i := by
  rw [← coeff_zero_eq_constantCoeff_apply, cf, coeff_mk, Function.iterate_zero_apply]

omit hg in
theorem shift_cf (f : O⟦X⟧) (i : ℕ) :
    (mk fun p => coeff (p + 1) (cf g f i)) = cf g (f /ʷ g) i := by
  ext n
  simp only [cf, coeff_mk, Function.iterate_succ_apply]

theorem exists_decomp (hD : 1 ≤ wd g) (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (f : O⟦X⟧) :
    ∃ c : Fin (wd g) → O⟦X⟧, f = ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) := by
  have hg0 := constantCoeff_mem hD
  let E : O⟦X⟧ → O⟦X⟧ := fun f => f - ∑ i : Fin (wd g), X ^ (i : ℕ) * h (cf g f i)
  have hE : ∀ f, E f = g * E (f /ʷ g) := by
    intro f
    have hs := sum_split h hX (fun i : Fin (wd g) => cf g f i)
    simp only [constantCoeff_cf, shift_cf] at hs
    rw [poly_of_degree (D := wd g) (degree_weierstrassMod_lt f g)] at hs
    have hf := eq_mul_weierstrassDiv_add_weierstrassMod f hg
    simp only [E]
    rw [hs]
    linear_combination hf
  have hmem : ∀ N f, E f ∈ Ideal.span {g ^ N} := by
    intro N
    induction N with
    | zero => intro f; simp
    | succ N ih =>
      intro f
      rw [hE, Ideal.mem_span_singleton, pow_succ']
      exact mul_dvd_mul_left g (Ideal.mem_span_singleton.mp (ih _))
  have h0 : E f = 0 := eq_zero_of_forall_mem_coeffFiltration fun N =>
    (Ideal.span_singleton_le_iff_mem _).mpr (pow_mem_coeffFiltration hg0 N) (hmem N f)
  exact ⟨fun i => cf g f i, sub_eq_zero.mp h0⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierD
end

section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def wdeg (g : O⟦X⟧) : ℕ := (g.map (IsLocalRing.residue O)).order.toNat

def IsDist (g : O⟦X⟧) : Prop := g.map (IsLocalRing.residue O) ≠ 0

theorem exists_weierstrass_substitution (g : O⟦X⟧) (hg : IsDist g) (hD : 1 ≤ wdeg g) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g ∧ Function.Injective h ∧
      ∀ f : O⟦X⟧, ∃! c : Fin (wdeg g) → O⟦X⟧, f = ∑ i : Fin (wdeg g), X ^ (i : ℕ) * h (c i) := by
  have hg0 : constantCoeff g ∈ IsLocalRing.maximalIdeal O := WeierD.constantCoeff_mem (g := g) hD
  obtain ⟨h, hX⟩ := WeierS.exists_algHom_X_eq hg0
  refine ⟨h, hX, WeierD.injective (g := g) hg hD h hX, fun f => ?_⟩
  obtain ⟨c, hc⟩ := WeierD.exists_decomp (g := g) hg hD h hX f
  exact ⟨c, hc, fun c' hc' => WeierD.decomp_unique (g := g) hg h hX c' c (hc'.symm.trans hc)⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end

section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def cont (ϖ : O) (g f : O⟦X⟧) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ k, g}), (k : ℕ∞)

theorem Cont.enat_le_of_forall {a b : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ a → (k : ℕ∞) ≤ b) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  have hb : b ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ a := by
    have h2 := (ENat.add_one_le_iff hb).2 hlt
    exact_mod_cast h2
  have h2 := h (n + 1) h1
  norm_cast at h2
  omega

theorem Cont.mem_pair_mono (ϖ : O) (g f : O⟦X⟧) {j k : ℕ} (hjk : j ≤ k)
    (h : f ∈ Ideal.span {C ϖ ^ k, g}) : f ∈ Ideal.span {C ϖ ^ j, g} := by
  refine (Ideal.span_le.2 ?_) h
  intro x hx
  rcases hx with rfl | rfl
  · have e : C ϖ ^ k = C ϖ ^ j * C ϖ ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)

theorem Cont.mem_zero (ϖ : O) (g f : O⟦X⟧) : f ∈ Ideal.span {C ϖ ^ 0, g} := by
  have h1 : (1 : O⟦X⟧) ∈ Ideal.span {C ϖ ^ 0, g} := Ideal.subset_span (by simp)
  simpa using Ideal.mul_mem_left _ f h1

theorem Cont.mem_iff_le (ϖ : O) (g f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  unfold cont
  constructor
  · intro h
    exact le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h
  · intro hk
    by_contra hnot
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hnot (Cont.mem_zero ϖ g f)
    have hbound : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      apply iSup₂_le
      intro j hj
      have hj' : j ≤ k - 1 := by
        by_contra hjk
        push_neg at hjk
        exact hnot (Cont.mem_pair_mono ϖ g f (by omega) hj)
      exact_mod_cast hj'
    have h3 := le_trans hk hbound
    norm_cast at h3
    omega

theorem Cont.residue_unif {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := by
  exact (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit

theorem Cont.C_unif_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  have h1 := congrArg PowerSeries.constantCoeff h
  simpa using h1

theorem Cont.C_dvd_of_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) (f : O⟦X⟧)
    (hf : f.map (IsLocalRing.residue O) = 0) : C ϖ ∣ f := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hc : ∀ n, ∃ c, PowerSeries.coeff n f = ϖ * c := by
    intro n
    have h1 : IsLocalRing.residue O (PowerSeries.coeff n f) = 0 := by
      have h2 := congrArg (PowerSeries.coeff n) hf
      simpa [PowerSeries.coeff_map] using h2
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

theorem Cont.prime_C_unif {ϖ : O} (hϖ : Irreducible ϖ) : Prime (C ϖ : O⟦X⟧) := by
  refine ⟨Cont.C_unif_ne_zero hϖ, ?_, ?_⟩
  · intro hu
    have h1 := hu.map (PowerSeries.constantCoeff (R := O))
    rw [PowerSeries.constantCoeff_C] at h1
    exact hϖ.not_isUnit h1
  · intro f g hfg
    have hmap : (f * g).map (IsLocalRing.residue O) = 0 := by
      obtain ⟨h, hh⟩ := hfg
      rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]
    rw [map_mul] at hmap
    rcases mul_eq_zero.1 hmap with h | h
    · exact Or.inl (Cont.C_dvd_of_map_eq_zero hϖ f h)
    · exact Or.inr (Cont.C_dvd_of_map_eq_zero hϖ g h)

theorem Cont.not_C_dvd {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) : ¬ (C ϖ ∣ g) := by
  rintro ⟨h, hh⟩
  apply hg
  rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]

theorem Cont.mem_of_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) (n : ℕ)
    (h : O⟦X⟧) (hm : C ϖ ^ n * h ∈ Ideal.span {g}) : h ∈ Ideal.span {g} := by
  induction n generalizing h with
  | zero => simpa using hm
  | succ n ih =>
    apply ih
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hm
    have hdvd : C ϖ ∣ q * g := ⟨C ϖ ^ n * h, by rw [hq, pow_succ]; ring⟩
    rcases (Cont.prime_C_unif hϖ).2.2 q g hdvd with ⟨q', rfl⟩ | hg'
    · rw [Ideal.mem_span_singleton']
      refine ⟨q', ?_⟩
      have h1 : C ϖ * (q' * g) = C ϖ * (C ϖ ^ n * h) := by
        calc C ϖ * (q' * g) = C ϖ * q' * g := by ring
          _ = C ϖ ^ (n + 1) * h := hq
          _ = C ϖ * (C ϖ ^ n * h) := by ring
      exact mul_left_cancel₀ (Cont.C_unif_ne_zero hϖ) h1
    · exact absurd hg' (Cont.not_C_dvd hϖ hg)

theorem Cont.smul_mk (g : O⟦X⟧) (r : O) (a : O⟦X⟧) :
    r • Ideal.Quotient.mk (Ideal.span {g}) a = Ideal.Quotient.mk (Ideal.span {g}) (C r * a) := by
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
  rfl

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem C2' {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    (∃ (a : O⟦X⟧) (n : ℕ), C ϖ ^ n * (f - C ϖ ^ k * a) ∈ Ideal.span {g}) ↔
      f ∈ Ideal.span {C ϖ ^ k, g} := by
  constructor
  · rintro ⟨a, n, h⟩
    have h1 := Cont.mem_of_pow_mul_mem hϖ hg n _ h
    have h2 : f = C ϖ ^ k * a + (f - C ϖ ^ k * a) := by ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.span_mono (Set.subset_insert _ _) h1)
  · intro hf
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hf
    refine ⟨u, 0, ?_⟩
    rw [pow_zero, one_mul, ← huv, Ideal.mem_span_singleton']
    exact ⟨v, by ring⟩

theorem mem_iff_le_cont {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  exact Cont.mem_iff_le ϖ g f k

theorem C0 {g : O⟦X⟧} (hg : IsDist g) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι O (O⟦X⟧ ⧸ Ideal.span {g})) (f : O⟦X⟧) :
    cont ϖ g f = ⨅ i, IsDiscreteValuationRing.addVal O (b.repr (Ideal.Quotient.mk _ f) i) := by
  have key : ∀ k : ℕ, f ∈ Ideal.span {C ϖ ^ k, g} ↔
      ∀ i, ϖ ^ k ∣ b.repr (Ideal.Quotient.mk (Ideal.span {g}) f) i := by
    intro k
    constructor
    · intro h
      obtain ⟨a, d, had⟩ := Ideal.mem_span_pair.mp h
      have hq : Ideal.Quotient.mk (Ideal.span {g}) f = ϖ ^ k • Ideal.Quotient.mk (Ideal.span {g}) a := by
        rw [Cont.smul_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton']
        exact ⟨d, by rw [map_pow]; linear_combination had⟩
      intro i
      rw [hq, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    · intro h
      choose c hc using h
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (b.equivFun.symm c)
      have hx : Ideal.Quotient.mk (Ideal.span {g}) f = ϖ ^ k • Ideal.Quotient.mk (Ideal.span {g}) a := by
        apply b.repr.injective
        ext i
        have e1 := congrFun (b.equivFun.apply_symm_apply c) i
        rw [Module.Basis.equivFun_apply] at e1
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hc i, ha, e1]
      rw [Cont.smul_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hx
      obtain ⟨d, hd⟩ := hx
      rw [map_pow] at hd
      exact Ideal.mem_span_pair.mpr ⟨a, d, by linear_combination hd⟩
  have key2 : ∀ k : ℕ, (k : ℕ∞) ≤ cont ϖ g f ↔
      (k : ℕ∞) ≤ ⨅ i, IsDiscreteValuationRing.addVal O (b.repr (Ideal.Quotient.mk _ f) i) := by
    intro k
    rw [← Cont.mem_iff_le ϖ g f k, key k, le_iInf_iff]
    apply forall_congr'
    intro i
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  exact le_antisymm (Cont.enat_le_of_forall fun k hk => (key2 k).mp hk)
    (Cont.enat_le_of_forall fun k hk => (key2 k).mpr hk)

theorem m1 {g g' : O⟦X⟧} (hg : IsDist g) (hg' : IsDist g') (hdvd : g ∣ g') (f : O⟦X⟧) :
    cont ϖ g' f ≤ cont ϖ g f := by
  apply Cont.enat_le_of_forall
  intro k hk
  have h1 := (Cont.mem_iff_le ϖ g' f k).2 hk
  apply (Cont.mem_iff_le ϖ g f k).1
  refine (Ideal.span_le.2 ?_) h1
  intro x hx
  rcases hx with rfl | rfl
  · exact Ideal.subset_span (by simp)
  · obtain ⟨c, rfl⟩ := hdvd
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem m2 {g : O⟦X⟧} (hg : IsDist g) (k f : O⟦X⟧) : cont ϖ g f ≤ cont ϖ g (k * f) := by
  apply Cont.enat_le_of_forall
  intro j hj
  exact (Cont.mem_iff_le ϖ g _ j).1 (Ideal.mul_mem_left _ k ((Cont.mem_iff_le ϖ g f j).2 hj))

theorem m3 {g f : O⟦X⟧} (hg : IsDist g) (hf : IsDist f) (hlt : wdeg f < wdeg g) :
    cont ϖ g f = 0 := by
  by_contra hne
  have h1 : ((1 : ℕ) : ℕ∞) ≤ cont ϖ g f := by
    rw [Nat.cast_one]
    exact ENat.one_le_iff_ne_zero.2 hne
  have h2 := (Cont.mem_iff_le ϖ g f 1).2 h1
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 h2
  have hmap : f.map (IsLocalRing.residue O) =
      v.map (IsLocalRing.residue O) * g.map (IsLocalRing.residue O) := by
    rw [← huv, map_add, map_mul, map_mul, pow_one, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero,
      mul_zero, zero_add]
  have hord : (g.map (IsLocalRing.residue O)).order ≤ (f.map (IsLocalRing.residue O)).order := by
    rw [hmap, PowerSeries.order_mul]
    exact le_add_self
  have hf0 : (f.map (IsLocalRing.residue O)).order ≠ ⊤ := fun h => hf (PowerSeries.order_eq_top.1 h)
  have h3 := ENat.toNat_le_toNat hord hf0
  unfold wdeg at hlt
  omega

omit hϖ in

theorem m5 {R : Type*} [CommRing R] (x x' t : R) (a s : ℕ) (hs : 1 ≤ s)
    (h : x - x' ∈ Ideal.span {t}) : x ^ (a + s - 1) ∈ Ideal.span {x' ^ a, t ^ s} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have hx : x = x' + t * y := by linear_combination (-1 : R) * hy
  rw [hx, add_pow]
  apply Ideal.sum_mem
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases ham : a ≤ m
  · have e : x' ^ m = x' ^ a * x' ^ (m - a) := by rw [← pow_add, Nat.add_sub_cancel' ham]
    rw [e]
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_right
    exact Ideal.subset_span (by simp)
  · push_neg at ham
    have hs' : s ≤ a + s - 1 - m := by omega
    have e : (t * y) ^ (a + s - 1 - m) = t ^ s * (t ^ (a + s - 1 - m - s) * y ^ (a + s - 1 - m)) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs']
    rw [e]
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_left
    apply Ideal.mul_mem_right
    exact Ideal.subset_span (by simp)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end

section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

section ContMAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ContM_dvd_iff_residue {ϖ : O} (hϖ : Irreducible ϖ) (a : O) :
    ϖ ∣ a ↔ IsLocalRing.residue O a = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem ContM_dvd_of_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) {a : O⟦X⟧}
    (ha : a.map (IsLocalRing.residue O) = 0) : C ϖ ∣ a := by
  have hc : ∀ n, ϖ ∣ coeff n a := fun n => by
    rw [ContM_dvd_iff_residue hϖ]
    have h := congrArg (coeff n) ha
    rwa [coeff_map, map_zero] at h
  choose b hb using hc
  refine ⟨PowerSeries.mk b, ?_⟩
  ext n
  rw [coeff_C_mul, coeff_mk, hb n]

theorem ContM_map_C_unif {ϖ : O} (hϖ : Irreducible ϖ) :
    (C ϖ : O⟦X⟧).map (IsLocalRing.residue O) = 0 := by
  rw [map_C, (ContM_dvd_iff_residue hϖ ϖ).1 dvd_rfl, map_zero]

theorem ContM_cancel_unif {ϖ : O} (hϖ : Irreducible ϖ) {G : O⟦X⟧} (hG : IsDist G) (k : ℕ) :
    ∀ {x a : O⟦X⟧}, C ϖ ^ k * x = a * G → G ∣ x := by
  induction k with
  | zero =>
    intro x a h
    rw [pow_zero, one_mul] at h
    exact ⟨a, by rw [h, mul_comm]⟩
  | succ k ih =>
    intro x a h
    have hmapC := ContM_map_C_unif hϖ
    have hdvd : C ϖ ∣ a * G := ⟨C ϖ ^ k * x, by rw [← h]; ring⟩
    have hmap0 : (a * G).map (IsLocalRing.residue O) = 0 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, map_mul, hmapC, zero_mul]
    rw [map_mul] at hmap0
    rcases mul_eq_zero.1 hmap0 with ha0 | hG0
    · obtain ⟨a', rfl⟩ := ContM_dvd_of_map_eq_zero hϖ ha0
      apply ih (a := a')
      have hne : (C ϖ : O⟦X⟧) ≠ 0 := by
        intro h0
        apply hϖ.ne_zero
        have h1 := congrArg (coeff 0) h0
        simpa using h1
      apply mul_left_cancel₀ hne
      linear_combination h
    · exact absurd hG0 hG

theorem ContM_mem_of_unif_mul {ϖ : O} (hϖ : Irreducible ϖ) {G : O⟦X⟧} (hG : IsDist G) (k : ℕ)
    {H : O⟦X⟧} (h : C ϖ ^ k * H ∈ Ideal.span {G, C ϖ ^ (k + 1)}) :
    H ∈ Ideal.span {G, C ϖ} := by
  rw [Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  have h2 : C ϖ ^ k * (H - b * C ϖ) = a * G := by linear_combination -hab
  obtain ⟨t, ht⟩ := ContM_cancel_unif hϖ hG k h2
  rw [Ideal.mem_span_pair]
  exact ⟨t, b, by linear_combination -ht⟩

theorem ContM_order_unit {K : Type*} [Field K] {w : K⟦X⟧} (hw : IsUnit w) : w.order = 0 := by
  obtain ⟨v, rfl⟩ := hw
  have h := order_mul (v : K⟦X⟧) (↑v⁻¹ : K⟦X⟧)
  rw [Units.mul_inv, order_one] at h
  exact (add_eq_zero.1 h.symm).1

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem dvd_coeffs_of_mem_span_distinguished {ϖ : O} (hϖ : Irreducible ϖ) {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg)
    (S : Finset ℕ) (y : ℕ) (hS : ∀ i ∈ S, i < y) (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ S, IsUnit (u i))
    (c : ℕ → O) (h : (∑ i ∈ S, u i * C (c i) * Xg ^ i) ∈ Ideal.span {Xg ^ y, C ϖ}) :
    ∀ i ∈ S, ϖ ∣ c i := by
  classical
  set f := IsLocalRing.residue O with hfdef
  set g := Xg.map f with hgdef
  have hg0 : g ≠ 0 := hX
  have hord : g.order = (wdeg Xg : ℕ∞) := by
    unfold wdeg
    rw [ENat.natCast_toNat]
    exact order_eq_top.not.2 hg0
  have hfϖ : f ϖ = 0 := (ContM_dvd_iff_residue hϖ ϖ).1 dvd_rfl
  rw [Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  have himg : (∑ i ∈ S, (u i).map f * C (f (c i)) * g ^ i) = a.map f * g ^ y := by
    have h1 := congrArg (PowerSeries.map f) hab
    simp only [map_add, map_mul, map_pow, map_sum, map_C, hfϖ, map_zero, mul_zero, add_zero] at h1
    exact h1.symm
  intro i hi
  by_contra hnd
  have hT : (S.filter fun i => f (c i) ≠ 0).Nonempty :=
    ⟨i, Finset.mem_filter.2 ⟨hi, fun h0 => hnd ((ContM_dvd_iff_residue hϖ _).2 h0)⟩⟩
  obtain ⟨i₀, hi₀T, hmin⟩ := Finset.exists_min_image _ id hT
  rw [Finset.mem_filter] at hi₀T
  have hlt : i₀ * wdeg Xg < y * wdeg Xg := by nlinarith [hS i₀ hi₀T.1]
  have hL : coeff (i₀ * wdeg Xg) (a.map f * g ^ y) = 0 := by
    apply coeff_of_lt_order
    rw [order_mul, order_pow, hord]
    calc ((i₀ * wdeg Xg : ℕ) : ℕ∞) < ((y * wdeg Xg : ℕ) : ℕ∞) := by exact_mod_cast hlt
      _ = y • (wdeg Xg : ℕ∞) := by
        rw [nsmul_eq_mul]
        push_cast
        rfl
      _ ≤ (a.map f).order + y • (wdeg Xg : ℕ∞) := le_add_self
  have hterm : ∀ i ∈ S, f (c i) ≠ 0 →
      ((u i).map f * C (f (c i)) * g ^ i).order = ((i * wdeg Xg : ℕ) : ℕ∞) := by
    intro i hi hci
    rw [order_mul, order_mul, order_pow, hord, ContM_order_unit ((hu i hi).map (PowerSeries.map f)),
      ContM_order_unit ((isUnit_iff_ne_zero.2 hci).map C), zero_add, zero_add, nsmul_eq_mul]
    push_cast
    rfl
  have hR : coeff (i₀ * wdeg Xg) (∑ i ∈ S, (u i).map f * C (f (c i)) * g ^ i) ≠ 0 := by
    rw [map_sum, Finset.sum_eq_single i₀]
    · have ho := hterm i₀ hi₀T.1 hi₀T.2
      have hne : ((u i₀).map f * C (f (c i₀)) * g ^ i₀) ≠ 0 := by
        intro h0
        rw [h0, order_zero] at ho
        exact ENat.top_ne_natCast _ ho
      have h1 := coeff_order hne
      rwa [ho, ENat.toNat_natCast] at h1
    · intro j hj hne
      by_cases hcj : f (c j) = 0
      · rw [hcj, map_zero, mul_zero, zero_mul, map_zero]
      · apply coeff_of_lt_order
        rw [hterm j hj hcj]
        have hle : i₀ ≤ j := hmin j (Finset.mem_filter.2 ⟨hj, hcj⟩)
        have hlt' : i₀ < j := lt_of_le_of_ne hle (Ne.symm hne)
        have hD' : 1 ≤ wdeg Xg := hD
        exact_mod_cast (by nlinarith : i₀ * wdeg Xg < j * wdeg Xg)
    · intro h0
      exact absurd hi₀T.1 h0
  exact hR (by rw [himg]; exact hL)

theorem ContM_Kk {ϖ : O} (hϖ : Irreducible ϖ) {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg)
    (S : Finset ℕ) (y : ℕ) (hS : ∀ i ∈ S, i < y) (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ S, IsUnit (u i)) :
    ∀ (k : ℕ) (c : ℕ → O), (∑ i ∈ S, u i * C (c i) * Xg ^ i) ∈ Ideal.span {Xg ^ y, C ϖ ^ k} →
      ∀ i ∈ S, ϖ ^ k ∣ c i := by
  intro k
  induction k with
  | zero =>
    intro c _ i _
    simp
  | succ k ih =>
    intro c h i hi
    have hle : Ideal.span {Xg ^ y, C ϖ ^ (k + 1)} ≤ Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
      rw [Ideal.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · rw [pow_succ]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    have hdk := ih c (hle h)
    choose! c' hc' using hdk
    have hF : (∑ i ∈ S, u i * C (c i) * Xg ^ i) = C ϖ ^ k * ∑ i ∈ S, u i * C (c' i) * Xg ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc' j hj, map_mul, map_pow]
      ring
    rw [hF] at h
    have hXy : IsDist (Xg ^ y) := by
      show (Xg ^ y).map _ ≠ 0
      rw [map_pow]
      exact pow_ne_zero _ hX
    have h1 := ContM_mem_of_unif_mul hϖ hXy k h
    obtain ⟨e, he⟩ := dvd_coeffs_of_mem_span_distinguished hϖ hX hD S y hS u hu c' h1 i hi
    rw [hc' i hi, he]
    exact ⟨e, by ring⟩

theorem ContM_iSup_le (m : ℕ∞) : ⨆ (k : ℕ) (_ : (k : ℕ∞) ≤ m), (k : ℕ∞) = m := by
  apply le_antisymm
  · exact iSup₂_le fun k hk => hk
  · exact Cont.enat_le_of_forall fun k hk => le_iSup₂_of_le k hk le_rfl

end ContMAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem Mprime {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg) (I : Finset ℕ)
    (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ I, IsUnit (u i)) (c : ℕ → O) (hc : ∀ i ∈ I, c i ≠ 0) (y k : ℕ) :
    (∑ i ∈ I, u i * C (c i) * Xg ^ i) ∈ Ideal.span {Xg ^ y, C ϖ ^ k} ↔
      ∀ i ∈ I, i < y → (k : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (c i) := by
  classical
  have hdv : ∀ i, ((k : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (c i) ↔ ϖ ^ k ∣ c i) := by
    intro i
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  have hbig : ∀ i, y ≤ i → u i * C (c i) * Xg ^ i ∈ Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
    intro i hi
    have hpow : Xg ^ i = Xg ^ y * Xg ^ (i - y) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
  constructor
  · intro h i hi hiy
    rw [hdv]
    have hsplit : (∑ j ∈ I.filter (· < y), u j * C (c j) * Xg ^ j) ∈
        Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
      have heq := Finset.sum_filter_add_sum_filter_not I (· < y) (fun j => u j * C (c j) * Xg ^ j)
      have hnot : (∑ j ∈ I.filter (fun j => ¬ j < y), u j * C (c j) * Xg ^ j) ∈
          Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
        apply Ideal.sum_mem
        intro j hj
        rw [Finset.mem_filter] at hj
        exact hbig j (by omega)
      have h3 : (∑ j ∈ I.filter (· < y), u j * C (c j) * Xg ^ j) =
          (∑ j ∈ I, u j * C (c j) * Xg ^ j) - ∑ j ∈ I.filter (fun j => ¬ j < y), u j * C (c j) * Xg ^ j := by
        rw [← heq, add_sub_cancel_right]
      rw [h3]
      exact Ideal.sub_mem _ h hnot
    exact ContM_Kk hϖ hX hD (I.filter (· < y)) y (fun j hj => (Finset.mem_filter.1 hj).2) u
      (fun j hj => hu j (Finset.mem_filter.1 hj).1) k c hsplit i (Finset.mem_filter.2 ⟨hi, hiy⟩)
  · intro h
    apply Ideal.sum_mem
    intro i hi
    by_cases hiy : i < y
    · obtain ⟨e, he⟩ := (hdv i).1 (h i hi hiy)
      rw [he, map_mul, map_pow]
      have hmem : (C ϖ : O⟦X⟧) ^ k ∈ Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have h4 : u i * (C ϖ ^ k * C e) * Xg ^ i = C ϖ ^ k * (u i * C e * Xg ^ i) := by ring
      rw [h4]
      exact Ideal.mul_mem_right _ _ hmem
    · exact hbig i (by omega)

theorem Mprime_cont {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg) (I : Finset ℕ)
    (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ I, IsUnit (u i)) (c : ℕ → O) (hc : ∀ i ∈ I, c i ≠ 0) (y : ℕ) :
    cont ϖ (Xg ^ y) (∑ i ∈ I, u i * C (c i) * Xg ^ i) =
      ⨅ i ∈ I.filter (· < y), IsDiscreteValuationRing.addVal O (c i) := by
  unfold cont
  have hm : ∀ k : ℕ, (∑ i ∈ I, u i * C (c i) * Xg ^ i) ∈ Ideal.span {C ϖ ^ k, Xg ^ y} ↔
      (k : ℕ∞) ≤ ⨅ i ∈ I.filter (· < y), IsDiscreteValuationRing.addVal O (c i) := by
    intro k
    rw [Set.pair_comm, Mprime hϖ hX hD I u hu c hc y k, le_iInf₂_iff]
    simp only [Finset.mem_filter]
    constructor
    · intro h i hi
      exact h i hi.1 hi.2
    · intro h i hi hiy
      exact h i ⟨hi, hiy⟩
  simp_rw [hm]
  exact ContM_iSup_le _

end Formalism.MainNotions.N.FrobeniusPowerSeries
end

section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

namespace ContPA

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

private lemma isUnit_natCast_sp_complex_sections {l m : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hc : Nat.Coprime l m) : IsUnit (m : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  by_contra hm
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hm)
  have hne : (1 : O) ∉ IsLocalRing.maximalIdeal O :=
    (Ideal.ne_top_iff_one _).mp (inferInstance : (IsLocalRing.maximalIdeal O).IsMaximal).ne_top
  apply hne
  have h1 : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm')

theorem natCast_unit_mul {l : ℕ} [hp : Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (hn : n ≠ 0) : ∃ v : Oˣ, (n : O) = v * (l : O) ^ padicValNat l n := by
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := l) (n := n)
  have hnd : ¬ l ∣ m := by
    rintro ⟨c, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hn
    exact ⟨c, by rw [pow_succ, mul_assoc]; exact hm⟩
  have hu := isUnit_natCast_sp_complex_sections hl ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
  refine ⟨hu.unit, ?_⟩
  have hc : (n : O) = (l : O) ^ padicValNat l n * (m : O) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → O) hm
  rw [hc, IsUnit.unit_spec, mul_comm]

theorem natCast_ne_zero' {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) : (n : O) ≠ 0 := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv]
  exact mul_ne_zero v.ne_zero (pow_ne_zero _ hl0)

theorem addVal_l {l : ℕ} (hl0 : (l : O) ≠ 0) :
    IsDiscreteValuationRing.addVal O (l : O) = ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℕ∞) := by
  exact (ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm

theorem addVal_natCast {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal O (n : O) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * padicValNat l n : ℕ) : ℕ∞) := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv, AddValuation.map_mul, AddValuation.map_pow, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

theorem l_unit_mul {ϖ : O} (hϖ : Irreducible ϖ) {l : ℕ} (hl0 : (l : O) ≠ 0) :
    ∃ v : Oˣ, (l : O) = v * ϖ ^ (IsDiscreteValuationRing.addVal O (l : O)).toNat := by
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨v, ?_⟩
  rw [IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ENat.toNat_coe]
  exact hv


private lemma order_unit_mul_X_pow_lemma_3 {K : Type*} [Field K] {w : K⟦X⟧} (hw : IsUnit w) (n : ℕ) :
    (w * X ^ n).order = (n : ℕ∞) := by
  have hw0 : w.order = 0 := by
    obtain ⟨u, rfl⟩ := hw
    have h := congrArg PowerSeries.order u.mul_inv
    rw [PowerSeries.order_mul, PowerSeries.order_one] at h
    have h2 : PowerSeries.order (u : K⟦X⟧) ≤ 0 := by
      rw [← h]; exact le_self_add
    exact le_antisymm h2 (by simp)
  rw [PowerSeries.order_mul, hw0, PowerSeries.order_X_pow, zero_add]

theorem dist_of_map_eq {f : O⟦X⟧} {w : (IsLocalRing.ResidueField O)⟦X⟧} (hw : IsUnit w) (n : ℕ)
    (h : f.map (IsLocalRing.residue O) = w * X ^ n) : IsDist f ∧ wdeg f = n := by
  have hord : (f.map (IsLocalRing.residue O)).order = n := by
    rw [h]; exact order_unit_mul_X_pow_lemma_3 hw n
  refine ⟨?_, ?_⟩
  · unfold IsDist
    intro h0
    rw [h0, PowerSeries.order_zero] at hord
    exact ENat.top_ne_coe n hord
  · unfold wdeg
    rw [hord]
    rfl

theorem dist_X_pow (n : ℕ) : IsDist ((X : O⟦X⟧) ^ n) ∧ wdeg ((X : O⟦X⟧) ^ n) = n := dist_of_map_eq isUnit_one n (by simp)

section P1
variable {l : ℕ} [hlp : Fact l.Prime] {p1 e u : O⟦X⟧}

theorem residue_map_p1_eq (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hp : p1 = C (l : O) * e + u * X ^ l) :
    p1.map (IsLocalRing.residue O) = u.map (IsLocalRing.residue O) * X ^ l := by
  have h0 : IsLocalRing.residue O (l : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hl
  have h0' : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]; exact h0
  have h0'' : ((l : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0 := by
    rw [← map_natCast (C : IsLocalRing.ResidueField O →+* (IsLocalRing.ResidueField O)⟦X⟧) l, h0', map_zero]
  rw [hp]
  simp [h0, h0', h0'']




theorem p1_pow_eq_sum_choose_mul_X_pow_l_pow (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    p1 ^ y = ∑ i ∈ Finset.range (y + 1),
      (u ^ i * e ^ (y - i)) * C ((y.choose i : O) * (l : O) ^ (y - i)) * ((X : O⟦X⟧) ^ l) ^ i := by
  rw [hp, add_comm (C (l : O) * e), add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem addVal_coef (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    IsDiscreteValuationRing.addVal O ((a.choose i : O) * (l : O) ^ (a - i)) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  have hc : a.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  rw [AddValuation.map_mul, addVal_natCast hl hl0 hc, AddValuation.map_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

theorem coef_ne_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    (a.choose i : O) * (l : O) ^ (a - i) ≠ 0 := mul_ne_zero (natCast_ne_zero' hl hl0 (Nat.choose_pos hi).ne') (pow_ne_zero _ hl0)

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ


theorem content_p1_pow_X_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (y b : ℕ) (hlt : b < l * y) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : ((l * y : ℕ) : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + ((l * y : ℕ) : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : l * y ≤ b := by exact_mod_cast h2
    omega

theorem content_X_pow_p1_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (B y : ℕ) (hlt : l * y < B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : (B : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + (B : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : B ≤ l * y := by exact_mod_cast h2
    omega

omit hϖ in
theorem padicValNat_choose_le_logb (n i : ℕ) : (padicValNat l (n.choose i) : ℝ) ≤ Real.logb l n := by
  have h1 : padicValNat l (n.choose i) ≤ Nat.log l n := by
    rw [← Nat.factorization_def _ hlp.out]
    exact Nat.factorization_choose_le_log
  calc (padicValNat l (n.choose i) : ℝ) ≤ (Nat.log l n : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb l n := Real.natLog_le_logb n l


omit hϖ in
theorem p1_pow_eq_sum_image_choose_mul_X_pow (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    p1 ^ y = ∑ j ∈ (Finset.range (y + 1)).image (l * ·),
      (u ^ (j / l) * e ^ (y - j / l)) * C ((y.choose (j / l) : O) * (l : O) ^ (y - j / l)) * (X : O⟦X⟧) ^ j := by
  rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hlp.out.pos h), p1_pow_eq_sum_choose_mul_X_pow_l_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Nat.mul_div_cancel_left _ hlp.out.pos, ← pow_mul]


end P1

end ContPA

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
