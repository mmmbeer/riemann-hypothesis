import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp

section
open Polynomial

namespace GlobalTheory.NilpotentOfTracePowers

theorem trace_mul_aeval {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) (p : K[X]) :
    LinearMap.trace K V (f * aeval f p) = 0 := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, ← pow_succ', h (i + 1) (by omega), smul_zero]

theorem exists_pow_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ (m : ℕ) (g : K[X]), f ^ m = f ^ m * aeval f (X * g) := by
  have hp : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly hp 0
  set m := rootMultiplicity 0 f.charpoly
  have hc : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h0
  have h0 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
  have hpoly : (X : K[X]) ^ m = X ^ m * (X * (C (-(q.coeff 0)⁻¹) * q.divX))
      + C (q.coeff 0)⁻¹ * f.charpoly := by
    have h1 : X * q.divX + C (q.coeff 0) = q := X_mul_divX_add q
    have h2 : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X]) := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    rw [map_zero, sub_zero] at hq
    rw [map_neg]
    linear_combination (-C (q.coeff 0)⁻¹) * hq + (C (q.coeff 0)⁻¹ * X ^ m) * h1 - X ^ m * h2
  refine ⟨m, C (-(q.coeff 0)⁻¹) * q.divX, ?_⟩
  have := congrArg (aeval f) hpoly
  rw [map_add, map_mul (aeval f) _ f.charpoly, h0, mul_zero, add_zero, map_mul, map_pow,
    aeval_X] at this
  exact this

theorem isNilpotent_of_trace_pow {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  obtain ⟨m, g, hm⟩ := exists_pow_eq f
  have hiter : ∀ j : ℕ, f ^ m = f ^ m * aeval f ((X * g) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', map_mul, ← mul_assoc, ← hm, ← ih]
  set e : Module.End K V := aeval f ((X * g) ^ (m + 1)) with he
  have he1 : e = aeval f (X * g ^ (m + 1)) * f ^ m := by
    have : (X * g) ^ (m + 1) = (X * g ^ (m + 1)) * X ^ m := by ring
    rw [he, this, map_mul (aeval f) _ (X ^ m), map_pow, aeval_X]
  have hid : IsIdempotentElem e := by
    unfold IsIdempotentElem
    conv_lhs => enter [1]; rw [he1]
    rw [mul_assoc, ← hiter (m + 1), ← he1]
  have htr : LinearMap.trace K V e = 0 := by
    have : (X * g) ^ (m + 1) = X * (g ^ (m + 1) * X ^ m) := by ring
    rw [he, this, map_mul, aeval_X]
    exact trace_mul_aeval f h _
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    { map_mem := fun x => LinearMap.mem_range_self e x
      map_id := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun hid x }
  have hrk : Module.finrank K (LinearMap.range e) = 0 := by
    have := hproj.trace
    rw [htr] at this
    exact_mod_cast this.symm
  have he0 : e = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrk)
  exact ⟨m, by rw [hiter (m + 1), ← he, he0, mul_zero]⟩

end GlobalTheory.NilpotentOfTracePowers
end

section
open Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.AugmentationNilpotent

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem isNilpotent_of_trace_pow [CharZero K] [FiniteDimensional K V] (x : Module.End K V)
    (h : ∀ n : ℕ, LinearMap.trace K V (x ^ (n + 1)) = 0) : IsNilpotent x := by
  have hp : ∀ a : K[X], LinearMap.trace K V (aeval x (a * X)) = 0 := by
    intro a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_zero]
    | monomial n c =>
      rw [monomial_mul_X, aeval_monomial, ← Algebra.smul_def, map_smul, h, smul_zero]
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd x.charpoly
    x.charpoly_monic.ne_zero 0
  set k := rootMultiplicity 0 x.charpoly
  rw [C_0, sub_zero] at hq hnd
  have hc : IsCoprime ((X : K[X]) ^ (k + 1)) q :=
    ((irreducible_X.coprime_iff_not_dvd).2 hnd).pow_left
  obtain ⟨a, b, hab⟩ := hc
  have h0 : aeval x (X ^ k * q) = 0 := by rw [← hq]; exact x.aeval_self_charpoly
  have hidem : IsIdempotentElem (aeval x (a * X ^ (k + 1))) := by
    unfold IsIdempotentElem
    rw [← map_mul]
    have : a * X ^ (k + 1) * (a * X ^ (k + 1)) = a * X ^ (k + 1) - (a * b * X) * (X ^ k * q) := by
      linear_combination (a * X ^ (k + 1)) * hab
    rw [this, map_sub, map_mul _ (a * b * X), h0, mul_zero, sub_zero]
  have he : aeval x (a * X ^ (k + 1)) = 0 := by
    apply (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1
    rw [pow_succ, ← mul_assoc]
    exact hp _
  refine ⟨k, ?_⟩
  have : (X : K[X]) ^ k = X ^ k * (a * X ^ (k + 1)) + b * (X ^ k * q) := by
    linear_combination (-X ^ k) * hab
  have h2 := congrArg (aeval x) this
  rw [map_add, map_mul _ (X ^ k), he, map_mul _ b, h0, map_pow, aeval_X] at h2
  simpa using h2

variable {Γ : Type} [Group Γ] (ρ : Representation K Γ V) (H : Subgroup Γ)

def aug : Submodule K (Module.End K V) := Submodule.span K {x | ∃ s ∈ H, x = ρ s - 1}

theorem sub_one_mem {s : Γ} (hs : s ∈ H) : ρ s - 1 ∈ aug ρ H := Submodule.subset_span ⟨s, hs, rfl⟩

theorem aug_mul {x y : Module.End K V} (hx : x ∈ aug ρ H) (hy : y ∈ aug ρ H) :
    x * y ∈ aug ρ H := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have : (ρ s - 1) * (ρ t - 1) = (ρ (s * t) - 1) - (ρ s - 1) - (ρ t - 1) := by
      rw [map_mul]; noncomm_ring
    rw [this]
    exact sub_mem (sub_mem (sub_one_mem ρ H (mul_mem hs ht)) (sub_one_mem ρ H hs))
      (sub_one_mem ρ H ht)
  | zero_left => simp
  | zero_right => simp
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | smul_left r x y _ _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  | smul_right r x y _ _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

end GlobalTheory.AugmentationNilpotent
end

section
namespace GlobalTheory.UnipNormalTrace

open Module

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem isNilpotent_of_trace_pow_eq_zero {K : Type} [Field K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  first
  | exact @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | (apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow ..)

end GlobalTheory.UnipNormalTrace
end
