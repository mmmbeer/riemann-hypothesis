import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.SemilinearResidue

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WittLift

open WittVector Finset Matrix

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*}

local notation "𝕎" => WittVector p

section Perfect

variable [CommRing k] [CharP k p] [PerfectRing k p]

omit [CharP k p] [PerfectRing k p] in
theorem sMod_iff (x y : 𝕎 k) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {(p : 𝕎 k)}) ^ n • ⊤ : Submodule (𝕎 k) (𝕎 k))] ↔
      x - y ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]

theorem exists_limit (a : ℕ → 𝕎 k) (h : ∀ n, a (n + 1) - a n ∈ Ideal.span {(p : 𝕎 k) ^ n}) :
    ∃ L, ∀ n, L - a n ∈ Ideal.span {(p : 𝕎 k) ^ n} := by
  have hmono : ∀ m n, m ≤ n → a n - a m ∈ Ideal.span {(p : 𝕎 k) ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : a (n + 1) - a n ∈ Ideal.span {(p : 𝕎 k) ^ m} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hmn) (h n)
      have := Ideal.add_mem _ ih h1
      convert this using 1
      abel
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : 𝕎 k)}) a (fun {m n} hmn => by
    rw [sMod_iff, ← neg_sub]
    exact neg_mem (hmono m n hmn))
  refine ⟨L, fun n => ?_⟩
  have := (sMod_iff _ _ _).mp (hL n)
  rw [← neg_sub]
  exact neg_mem this

theorem eq_zero_of_forall_mem (x : 𝕎 k) (h : ∀ n, x ∈ Ideal.span {(p : 𝕎 k) ^ n}) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : 𝕎 k)}) x (fun n => by
    rw [sMod_iff, sub_zero]
    exact h n)

end Perfect

section Matrix

variable [CommRing k] [CharP k p] {ι : Type*} [Fintype ι]

noncomputable def matOp (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) :
    (ι → 𝕎 k) →+ (ι → 𝕎 k) where
  toFun x := A *ᵥ (fun i => τ (x i))
  map_zero' := by
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero A
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

omit [CharP k p] in
theorem matOp_apply (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) (x : ι → 𝕎 k) :
    matOp A τ x = A *ᵥ (fun i => τ (x i)) := rfl

omit [CharP k p] in
theorem matOp_p_smul (A : Matrix ι ι (𝕎 k)) (τ : 𝕎 k →+* 𝕎 k) (x : ι → 𝕎 k) :
    matOp A τ ((p : 𝕎 k) • x) = (p : 𝕎 k) • matOp A τ x := by
  rw [matOp_apply, matOp_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_natCast]

def red (x : ι → 𝕎 k) : ι → k := fun i => (x i).coeff 0

variable {e : ℕ}

noncomputable def resOp (A : Matrix ι ι (𝕎 k)) (e : ℕ) : (ι → k) →+ (ι → k) where
  toFun x := A.map (fun a => a.coeff 0) *ᵥ (fun i => x i ^ p ^ e)
  map_zero' := by
    rw [← Matrix.mulVec_zero (A.map (fun a => a.coeff 0))]
    congr 1
    funext i
    simp [hp.out.ne_zero]
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [add_pow_char_pow]

theorem resOp_apply (A : Matrix ι ι (𝕎 k)) (x : ι → k) :
    resOp A e x = A.map (fun a => a.coeff 0) *ᵥ (fun i => x i ^ p ^ e) := rfl

theorem red_matOp (A : Matrix ι ι (𝕎 k)) {τ : 𝕎 k →+* 𝕎 k}
    (hτ : ∀ y, (τ y).coeff 0 = y.coeff 0 ^ p ^ e) (x : ι → 𝕎 k) :
    red (matOp A τ x) = resOp A e (red x) := by
  funext i
  simp only [red, matOp_apply, resOp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [← WittVector.constantCoeff_apply, map_sum]
  simp [WittVector.mul_coeff_zero, hτ]

theorem red_iterate_matOp (A : Matrix ι ι (𝕎 k)) {τ : 𝕎 k →+* 𝕎 k}
    (hτ : ∀ y, (τ y).coeff 0 = y.coeff 0 ^ p ^ e) (x : ι → 𝕎 k) (N : ℕ) :
    red ((⇑(matOp A τ))^[N] x) = (⇑(resOp A e))^[N] (red x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', red_matOp A hτ, ih]

omit [CharP k p] [Fintype ι] in
theorem red_sub (x y : ι → 𝕎 k) : red (x - y) = red x - red y := by
  funext i
  simp [red, ← WittVector.constantCoeff_apply]

omit [Fintype ι] in
theorem red_p_smul (x : ι → 𝕎 k) : red ((p : 𝕎 k) • x) = 0 := by
  funext i
  simp [red, ← WittVector.constantCoeff_apply]

variable [PerfectRing k p]

omit [Fintype ι] in
theorem exists_eq_p_smul_of_red (x : ι → 𝕎 k) (h : red x = 0) : ∃ y, x = (p : 𝕎 k) • y := by
  have : ∀ i, ∃ y, x i = (p : 𝕎 k) * y := fun i => by
    have hi : (x i).coeff 0 = 0 := congrFun h i
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp
      ((mem_span_p_iff_coeff_zero_eq_zero (x i)).mpr hi)
    exact ⟨y, by rw [← hy, mul_comm]⟩
  choose y hy using this
  exact ⟨y, funext fun i => by simp [hy i]⟩

omit [CharP k p] [Fintype ι] [PerfectRing k p] in
theorem exists_lift (x : ι → k) : ∃ y : ι → 𝕎 k, red y = x :=
  ⟨fun i => teichmuller p (x i), funext fun _ => rfl⟩

end Matrix

section AlgClosed

variable [Field k] [IsAlgClosed k] [CharP k p] {ι : Type*} [Fintype ι] {e : ℕ}

end AlgClosed

end WittLift

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open IsLocalRing WittVector Ideal

section Integers

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem norm_coe_integer_le_one (x : normInteger K) : ‖(x : K)‖ ≤ 1 := mem_normInteger.1 x.2

theorem isUnit_integer_iff_norm_eq_one {x : normInteger K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  rw [(normInteger_integers (K := K)).isUnit_iff_valuation_eq_one]
  have hx : algebraMap (normInteger K) K x = (x : K) := rfl
  simp only [NormedField.valuation_apply, hx]
  constructor
  · intro h
    have := congrArg NNReal.toReal h
    simpa using this
  · intro h
    ext
    simpa using h

variable [IsDiscreteValuationRing (normInteger K)]

theorem residue_eq_zero_iff_norm_lt_one {x : normInteger K} :
    residue (normInteger K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (norm_coe_integer_le_one x) h, fun h => h.ne⟩

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)
include hϖ

theorem norm_unif_lt_one : ‖(ϖ : K)‖ < 1 :=
  lt_of_le_of_ne (norm_coe_integer_le_one ϖ) fun h =>
    hϖ.not_isUnit (isUnit_integer_iff_norm_eq_one.2 h)

theorem norm_unif_pos : 0 < ‖(ϖ : K)‖ := by
  have : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  exact norm_pos_iff.2 this

theorem norm_le_norm_unif_of_lt_one {x : normInteger K} (hx : ‖(x : K)‖ < 1) :
    ‖(x : K)‖ ≤ ‖(ϖ : K)‖ := by
  have hm : x ∈ maximalIdeal (normInteger K) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one]; exact hx.ne
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, mem_span_singleton'] at hm
  obtain ⟨y, rfl⟩ := hm
  simp only [Subring.coe_mul, norm_mul]
  calc ‖(y : K)‖ * ‖(ϖ : K)‖ ≤ 1 * ‖(ϖ : K)‖ := by
        gcongr; exact norm_coe_integer_le_one y
    _ = _ := one_mul _

theorem exists_norm_eq_pow {x : normInteger K} (hx : x ≠ 0) : ∃ n : ℕ, ‖(x : K)‖ = ‖(ϖ : K)‖ ^ n := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  refine ⟨n, ?_⟩
  have := congrArg (fun z : normInteger K => ‖(z : K)‖) hu
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow] at this
  rwa [isUnit_integer_iff_norm_eq_one.1 u.isUnit, mul_one] at this

end Integers

section PowCongr

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem norm_pow_sub_pow_le_of_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hx) (by positivity)
      (pow_le_one₀ (norm_nonneg _) hy)
  calc _ ≤ 1 * ‖x - y‖ := by gcongr
    _ = _ := one_mul _

theorem norm_pow_prime_sub_le {p : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hp : ‖(p : K)‖ ≤ c) {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {j : ℕ} (hj : 1 ≤ j) (h : ‖x - y‖ ≤ c ^ j) (hc1 : c ≤ 1) :
    ‖x ^ p - y ^ p‖ ≤ c ^ (j + 1) := by
  rw [← geom_sum₂_mul, norm_mul]
  have hxy : ‖x - y‖ ≤ c := h.trans (by simpa using pow_le_pow_of_le_one hc0 hc1 hj)
  have hs : ‖∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)‖ ≤ c := by
    have : ∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) =
        ∑ i ∈ Finset.range p, (x ^ i - y ^ i) * y ^ (p - 1 - i) + (p : K) * y ^ (p - 1) := by
      have h2 : ∀ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i) =
          (x ^ i - y ^ i) * y ^ (p - 1 - i) + y ^ (p - 1) := by
        intro i hi
        have hi' : i ≤ p - 1 := by rw [Finset.mem_range] at hi; omega
        rw [sub_mul, ← pow_add, Nat.add_sub_cancel' hi']; ring
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      simp [Finset.card_range, nsmul_eq_mul]
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc0 fun i _ => ?_
      rw [norm_mul, norm_pow]
      calc ‖x ^ i - y ^ i‖ * ‖y‖ ^ (p - 1 - i) ≤ c * 1 := by
            gcongr
            · exact (norm_pow_sub_pow_le_of_le_one hx hy i).trans hxy
            · exact pow_le_one₀ (norm_nonneg _) hy
        _ = c := mul_one c
    · rw [norm_mul, norm_pow]
      calc ‖(p : K)‖ * ‖y‖ ^ (p - 1) ≤ c * 1 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hy
        _ = c := mul_one c
  calc _ ≤ c * c ^ j := by gcongr
    _ = c ^ (j + 1) := by ring

end PowCongr

section Residue

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [IsDiscreteValuationRing (normInteger K)]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]

theorem residue_natCast_prime : residue (normInteger K) (p : normInteger K) = 0 := by
  rw [map_natCast]; exact CharP.cast_eq_zero _ p

theorem norm_natCast_prime_lt_one : ‖((p : normInteger K) : K)‖ < 1 :=
  residue_eq_zero_iff_norm_lt_one.1 (residue_natCast_prime p)

instance fact_not_isUnit_natCast_prime : Fact (¬ IsUnit (p : normInteger K)) :=
  ⟨fun h => (norm_natCast_prime_lt_one (K := K) p).ne (isUnit_integer_iff_norm_eq_one.1 h)⟩

instance isAdicComplete_natCast_prime [CompleteSpace K] :
    IsAdicComplete (span {(p : normInteger K)}) (normInteger K) :=
  isAdicComplete_span_singleton (norm_natCast_prime_lt_one p)

theorem norm_natCast_prime_le_unif {ϖ : normInteger K} (hϖ : Irreducible ϖ) :
    ‖((p : normInteger K) : K)‖ ≤ ‖(ϖ : K)‖ :=
  norm_le_norm_unif_of_lt_one hϖ (norm_natCast_prime_lt_one p)

theorem norm_pow_prime_pow_sub_le {ϖ : normInteger K} (hϖ : Irreducible ϖ) {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {j : ℕ} (hj : 1 ≤ j) (h : ‖x - y‖ ≤ ‖(ϖ : K)‖ ^ j) (m : ℕ) :
    ‖x ^ p ^ m - y ^ p ^ m‖ ≤ ‖(ϖ : K)‖ ^ (j + m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [pow_succ, pow_mul, pow_mul, ← add_assoc]
    have hc := norm_natCast_prime_le_unif (K := K) p hϖ
    have hpK : ‖(p : K)‖ ≤ ‖(ϖ : K)‖ := by simpa using hc
    exact norm_pow_prime_sub_le (norm_nonneg _) hpK (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy) (by omega) ih
      (norm_unif_lt_one hϖ).le

theorem norm_sub_le_unif_of_residue_eq {ϖ : normInteger K} (hϖ : Irreducible ϖ)
    {x y : normInteger K} (h : residue (normInteger K) x = residue (normInteger K) y) :
    ‖(x : K) - y‖ ≤ ‖(ϖ : K)‖ := by
  have : residue (normInteger K) (x - y) = 0 := by rw [map_sub, h, sub_self]
  have := norm_le_norm_unif_of_lt_one hϖ (residue_eq_zero_iff_norm_lt_one.1 this)
  simpa using this

theorem mem_span_natCast_prime_of_norm_le {x : normInteger K}
    (h : ‖(x : K)‖ ≤ ‖((p : normInteger K) : K)‖) : x ∈ span {(p : normInteger K)} := by
  have := (mem_span_singleton_pow_iff (a := (p : normInteger K)) (x := x) 1).2 (by simpa using h)
  simpa using this

variable [CharZero K]

theorem natCast_prime_ne_zero : (p : normInteger K) ≠ 0 := by
  intro h
  have h' : ((p : normInteger K) : K) = 0 := by rw [h]; rfl
  have : (p : K) = 0 := by simpa using h'
  exact hp.out.ne_zero (by exact_mod_cast this)

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)

def ramIdx : ℕ :=
  (IsDiscreteValuationRing.associated_pow_irreducible (natCast_prime_ne_zero (K := K) p) hϖ).choose

theorem associated_ramIdx : Associated (p : normInteger K) (ϖ ^ ramIdx p hϖ) :=
  (IsDiscreteValuationRing.associated_pow_irreducible (natCast_prime_ne_zero (K := K) p) hϖ).choose_spec

theorem exists_unit_natCast_prime_eq : ∃ u : (normInteger K)ˣ, (p : normInteger K) = ϖ ^ ramIdx p hϖ * u := by
  obtain ⟨u, hu⟩ := associated_ramIdx p hϖ
  exact ⟨u⁻¹, by rw [← hu, mul_assoc, Units.mul_inv, mul_one]⟩

theorem norm_natCast_prime_eq : ‖((p : normInteger K) : K)‖ = ‖(ϖ : K)‖ ^ ramIdx p hϖ := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  rw [hu]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
  rw [isUnit_integer_iff_norm_eq_one.1 u.isUnit, mul_one]

theorem ramIdx_pos : 0 < ramIdx p hϖ := by
  by_contra h
  have h0 : ramIdx p hϖ = 0 := by omega
  have := norm_natCast_prime_eq p hϖ
  rw [h0, pow_zero] at this
  exact (norm_natCast_prime_lt_one (K := K) p).ne this

end Residue

section Tilt

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [IsDiscreteValuationRing (normInteger K)]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]

variable (K) in

def tiltResidue : PreTilt (normInteger K) p →+* ResidueField (normInteger K) :=
  (Ideal.Quotient.lift (span {(p : normInteger K)}) (residue (normInteger K)) fun a ha => by
    obtain ⟨c, rfl⟩ := mem_span_singleton'.1 ha
    rw [map_mul, residue_natCast_prime, mul_zero]).comp (PreTilt.coeff 0)

theorem tiltResidue_of_mk (x : PreTilt (normInteger K) p) (y : normInteger K)
    (hy : Ideal.Quotient.mk _ y = PreTilt.coeff 0 x) :
    tiltResidue K p x = residue (normInteger K) y := by
  simp [tiltResidue, ← hy]

theorem preTilt_coeff_pow (x : PreTilt (normInteger K) p) (n m : ℕ) :
    PreTilt.coeff (n + m) x ^ p ^ m = PreTilt.coeff n x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_mul, ← add_assoc, PreTilt.coeff_pow_p, ih]

variable [CharZero K]

theorem tiltResidue_injective : Function.Injective (tiltResidue K p) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hsmall : ∀ n, ∀ y : normInteger K, Ideal.Quotient.mk _ y = PreTilt.coeff n x →
      ‖(y : K)‖ ≤ ‖(ϖ : K)‖ := by
    intro n y hy
    have h1 : tiltResidue K p x = residue _ (y ^ p ^ n) := by
      apply tiltResidue_of_mk
      rw [map_pow, hy, ← preTilt_coeff_pow p x 0 n, zero_add]
    rw [hx, map_pow, eq_comm, pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)] at h1
    exact norm_le_norm_unif_of_lt_one hϖ (residue_eq_zero_iff_norm_lt_one.1 h1)
  apply Perfection.ext
  intro n
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_zero]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff (n + ramIdx p hϖ) x)
  have hy1 := hsmall _ y hy
  rw [← preTilt_coeff_pow p x n (ramIdx p hϖ), ← hy, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply mem_span_natCast_prime_of_norm_le
  rw [norm_natCast_prime_eq p hϖ, SubmonoidClass.coe_pow, norm_pow]
  calc ‖(y : K)‖ ^ p ^ ramIdx p hϖ ≤ ‖(ϖ : K)‖ ^ p ^ ramIdx p hϖ := by gcongr
    _ ≤ ‖(ϖ : K)‖ ^ ramIdx p hϖ :=
        pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le
          (Nat.lt_pow_self hp.out.one_lt).le

variable [PerfectRing (ResidueField (normInteger K)) p]

theorem tiltResidue_surjective : Function.Surjective (tiltResidue K p) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  set e := ramIdx p hϖ
  intro a
  set r : ℕ → ResidueField (normInteger K) :=
    fun m => ((frobeniusEquiv (ResidueField (normInteger K)) p).symm^[m]) a with hr_def
  have hr : ∀ m, r (m + 1) ^ p = r m := by
    intro m
    simp only [hr_def, Function.iterate_succ_apply']
    exact frobenius_apply_frobeniusEquiv_symm _ p _
  have hr0 : ∀ m, r m ^ p ^ m = a := by
    intro m
    induction m with
    | zero => simp [hr_def]
    | succ m ih => rw [pow_succ', pow_mul, hr, ih]
  choose z hz using fun m => residue_surjective (R := normInteger K) (r m)
  let c : ℕ → ModP (normInteger K) p := fun n => Ideal.Quotient.mk _ (z (n + e) ^ p ^ e)
  have hc : ∀ n, c (n + 1) ^ p = c n := by
    intro n
    simp only [c, ← map_pow]
    rw [Ideal.Quotient.eq]
    apply mem_span_natCast_prime_of_norm_le
    rw [norm_natCast_prime_eq p hϖ]
    have hres : residue (normInteger K) (z (n + 1 + e) ^ p) = residue (normInteger K) (z (n + e)) := by
      rw [map_pow, hz, hz, show n + 1 + e = n + e + 1 by omega, hr]
    have h1 := norm_sub_le_unif_of_residue_eq hϖ hres
    have h2 := norm_pow_prime_pow_sub_le p hϖ (x := ((z (n + 1 + e) ^ p : normInteger K) : K))
      (y := ((z (n + e) : normInteger K) : K)) (norm_coe_integer_le_one _) (norm_coe_integer_le_one _)
      le_rfl (by simpa using h1) e
    have h3 : ‖(ϖ : K)‖ ^ (1 + e) ≤ ‖(ϖ : K)‖ ^ e :=
      pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le (by omega)
    rw [show ((z (n + 1 + e) ^ p ^ e) ^ p : normInteger K) = (z (n + 1 + e) ^ p) ^ p ^ e by
      rw [← pow_mul, ← pow_mul, mul_comm]]
    have h4 : (((z (n + 1 + e) ^ p) ^ p ^ e - z (n + e) ^ p ^ e : normInteger K) : K) =
        ((z (n + 1 + e) ^ p : normInteger K) : K) ^ p ^ e - ((z (n + e) : normInteger K) : K) ^ p ^ e := by
      push_cast; ring
    rw [h4]
    exact h2.trans h3
  let x : PreTilt (normInteger K) p := ⟨c, hc⟩
  refine ⟨x, ?_⟩
  rw [tiltResidue_of_mk p x (z (0 + e) ^ p ^ e) rfl, map_pow, hz, zero_add, hr0]

def tiltResidueEquiv : PreTilt (normInteger K) p ≃+* ResidueField (normInteger K) :=
  RingEquiv.ofBijective (tiltResidue K p) ⟨tiltResidue_injective p, tiltResidue_surjective p⟩

@[simp]
theorem tiltResidueEquiv_apply (x : PreTilt (normInteger K) p) :
    tiltResidueEquiv p x = tiltResidue K p x := rfl

end Tilt

section Cohen

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]

omit [CompleteSpace K] [IsDiscreteValuationRing (normInteger K)] [CharZero K] in

theorem frobeniusEquiv_symm_iterate_pow {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
    (a : R) (n : ℕ) : ((frobeniusEquiv R p).symm^[n] a) ^ p ^ n = a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    exact frobenius_apply_frobeniusEquiv_symm R p a

omit [CompleteSpace K] [CharZero K] [PerfectRing (ResidueField (normInteger K)) p] in

theorem eq_of_forall_sub_mem_span_pow {a : normInteger K} (ha : ‖(a : K)‖ < 1)
    {x y : normInteger K} (h : ∀ n : ℕ, x - y ∈ span {a ^ n}) : x = y := by
  have hn : ∀ n : ℕ, ‖((x - y : normInteger K) : K)‖ ≤ ‖(a : K)‖ ^ n := fun n =>
    (mem_span_singleton_pow_iff n).1 (by rw [span_singleton_pow]; exact h n)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
  have h0 : ‖((x - y : normInteger K) : K)‖ ≤ 0 := ge_of_tendsto' ht hn
  have : ((x - y : normInteger K) : K) = 0 := norm_le_zero_iff.1 h0
  exact sub_eq_zero.1 (Subtype.ext this)

variable (K) in

def cohenMap : WittVector p (ResidueField (normInteger K)) →+* normInteger K :=
  (fontaineTheta (normInteger K) p).comp
    (WittVector.map (tiltResidueEquiv (K := K) p).symm.toRingHom)

@[simp]
theorem residue_cohenMap (w : WittVector p (ResidueField (normInteger K))) :
    residue (normInteger K) (cohenMap K p w) = w.coeff 0 := by
  have h := mk_fontaineTheta (WittVector.map (tiltResidueEquiv (K := K) p).symm.toRingHom w)
  rw [WittVector.map_coeff] at h
  have h2 : tiltResidue K p ((tiltResidueEquiv (K := K) p).symm (w.coeff 0)) = w.coeff 0 := by
    rw [← tiltResidueEquiv_apply, RingEquiv.apply_symm_apply]
  rw [← h2]
  exact (tiltResidue_of_mk p _ _ h).symm

theorem ringHom_ext_of_residue (f g : WittVector p (ResidueField (normInteger K)) →+* normInteger K)
    (h : ∀ w, residue (normInteger K) (f w) = residue (normInteger K) (g w)) : f = g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  have hT : ∀ a, f (teichmuller p a) = g (teichmuller p a) := by
    intro a
    have hn : ∀ n : ℕ, ‖((f (teichmuller p a) : normInteger K) : K) - g (teichmuller p a)‖ ≤
        ‖(ϖ : K)‖ ^ n := by
      intro n
      set b := (frobeniusEquiv (ResidueField (normInteger K)) p).symm^[n] a
      have ht : teichmuller p a = teichmuller p b ^ p ^ n := by
        rw [← map_pow, frobeniusEquiv_symm_iterate_pow]
      rw [ht, map_pow, map_pow]
      push_cast
      have h1 := norm_sub_le_unif_of_residue_eq hϖ (h (teichmuller p b))
      refine (norm_pow_prime_pow_sub_le p hϖ (norm_coe_integer_le_one _) (norm_coe_integer_le_one _)
        le_rfl (by simpa using h1) n).trans ?_
      exact pow_le_pow_of_le_one (norm_nonneg _) (norm_unif_lt_one hϖ).le (by omega)
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_unif_lt_one hϖ)
    have h0 := ge_of_tendsto' ht hn
    exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 h0))
  have hmod : ∀ n : ℕ, (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})).comp f =
      (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})).comp g := by
    intro n
    apply WittVector.eq_of_apply_teichmuller_eq
    · refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : normInteger K) ^ n})), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_singleton_self _
    · intro x
      simp [hT x]
  ext w
  have := eq_of_forall_sub_mem_span_pow (K := K) (a := (p : normInteger K))
    (norm_natCast_prime_lt_one p) (x := f w) (y := g w) fun n => by
      have := congrArg (fun φ => φ w) (hmod n)
      simp only [RingHom.comp_apply] at this
      exact Ideal.Quotient.eq.1 this
  rw [this]

theorem comp_cohenMap_of_residue (σ : normInteger K →+* normInteger K) (a : ℕ)
    (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) :
    σ.comp (cohenMap K p) =
      (cohenMap K p).comp (WittVector.map (iterateFrobenius (ResidueField (normInteger K)) p a)) := by
  apply ringHom_ext_of_residue
  intro w
  simp [hσ, iterateFrobenius_def]

theorem norm_cohenMap_of_coeff_ne_zero {w : WittVector p (ResidueField (normInteger K))}
    (hw : w.coeff 0 ≠ 0) : ‖(cohenMap K p w : K)‖ = 1 := by
  refine le_antisymm (norm_coe_integer_le_one _) (not_lt.1 fun h => hw ?_)
  rw [← residue_cohenMap, residue_eq_zero_iff_norm_lt_one]
  exact h


instance cohenAlgebra : Algebra (WittVector p (ResidueField (normInteger K))) (normInteger K) :=
  (cohenMap K p).toAlgebra


theorem cohen_smul_def (w : WittVector p (ResidueField (normInteger K))) (x : normInteger K) :
    w • x = cohenMap K p w * x := Algebra.smul_def w x

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)

theorem exists_norm_cohenMap_eq {w : WittVector p (ResidueField (normInteger K))} (hw : w ≠ 0) :
    ∃ m : ℕ, ‖(cohenMap K p w : K)‖ = ‖(ϖ : K)‖ ^ (ramIdx p hϖ * m) := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w hw
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow, map_natCast]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
  rw [norm_natCast_prime_eq p hϖ, norm_cohenMap_of_coeff_ne_zero p hb, mul_one, ← pow_mul]

theorem linearIndependent_unif_pow :
    LinearIndependent (WittVector p (ResidueField (normInteger K)))
      (fun j : Fin (ramIdx p hϖ) => ϖ ^ (j : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  set S := Finset.univ.filter (fun i => g i ≠ 0) with hS_def
  have hS : S.Nonempty := ⟨i₀, by simp [hS_def, hi₀]⟩
  set f : Fin (ramIdx p hϖ) → K := fun i => (cohenMap K p (g i) : K) * (ϖ : K) ^ (i : ℕ) with hf
  have hsum : ∑ i ∈ S, f i = 0 := by
    have h1 := congrArg (fun z : normInteger K => (z : K)) hg
    simp only [cohen_smul_def] at h1
    push_cast at h1
    rw [← h1, hS_def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · simp [not_not.1 h]
  have hnorm : ∀ i ∈ S, ∃ m : ℕ, ‖f i‖ = ‖(ϖ : K)‖ ^ ((i : ℕ) + ramIdx p hϖ * m) := by
    intro i hi
    have hgi : g i ≠ 0 := by simpa [hS_def] using hi
    obtain ⟨m, hm⟩ := exists_norm_cohenMap_eq p hϖ hgi
    exact ⟨m, by rw [hf, norm_mul, norm_pow, hm, ← pow_add, add_comm]⟩
  have h0 := norm_unif_pos hϖ
  have h1 := norm_unif_lt_one hϖ
  have hpair : Set.Pairwise (S : Set (Fin (ramIdx p hϖ))) (fun i j => ‖f i‖ ≠ ‖f j‖) := by
    intro i hi j hj hij heq
    obtain ⟨m, hm⟩ := hnorm i hi
    obtain ⟨m', hm'⟩ := hnorm j hj
    rw [hm, hm'] at heq
    have := pow_right_injective₀ h0 h1.ne heq
    have hmod := congrArg (· % ramIdx p hϖ) this
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hmod
    exact hij (Fin.ext hmod)
  have := IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hS hpair
  rw [hsum, norm_zero] at this
  obtain ⟨m, hm⟩ := hnorm i₀ (by simp [hS_def, hi₀])
  have hpos : 0 < ‖f i₀‖ := by rw [hm]; positivity
  have hle : ‖f i₀‖ ≤ S.sup' hS (fun i => ‖f i‖) :=
    Finset.le_sup' (fun i => ‖f i‖) (by simp [hS_def, hi₀])
  linarith

theorem exists_digits (x : normInteger K) :
    ∃ (d : Fin (ramIdx p hϖ) → WittVector p (ResidueField (normInteger K))) (y : normInteger K),
      x = ∑ j, cohenMap K p (d j) * ϖ ^ (j : ℕ) + p * y := by
  have key : ∀ n : ℕ, ∃ (d : ℕ → WittVector p (ResidueField (normInteger K))) (y : normInteger K),
      x = ∑ j ∈ Finset.range n, cohenMap K p (d j) * ϖ ^ j + ϖ ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨0, x, by simp⟩
    | succ n ih =>
      obtain ⟨d, y, hy⟩ := ih
      set t := teichmuller p (residue (normInteger K) y)
      have hres : residue (normInteger K) (y - cohenMap K p t) = 0 := by
        rw [map_sub, residue_cohenMap, teichmuller_coeff_zero, sub_self]
      have hm : y - cohenMap K p t ∈ maximalIdeal (normInteger K) := (residue_eq_zero_iff _).1 hres
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, mem_span_singleton'] at hm
      obtain ⟨y', hy'⟩ := hm
      refine ⟨fun j => if j = n then t else d j, y', ?_⟩
      rw [Finset.sum_range_succ]
      simp only [if_true]
      have hs : ∑ j ∈ Finset.range n, cohenMap K p (if j = n then t else d j) * ϖ ^ j =
          ∑ j ∈ Finset.range n, cohenMap K p (d j) * ϖ ^ j :=
        Finset.sum_congr rfl fun j hj => by
          rw [if_neg (by rw [Finset.mem_range] at hj; omega)]
      rw [hs, hy]
      have : y = cohenMap K p t + y' * ϖ := by rw [hy']; ring
      rw [this]
      ring
  obtain ⟨d, y, hy⟩ := key (ramIdx p hϖ)
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  refine ⟨fun j => d j, ↑u⁻¹ * y, ?_⟩
  rw [hy, Fin.sum_univ_eq_sum_range (fun j => cohenMap K p (d j) * ϖ ^ j), hu]
  congr 1
  rw [mul_assoc, ← mul_assoc (u : normInteger K), Units.mul_inv, one_mul]

theorem span_unif_pow_eq_top :
    Submodule.span (WittVector p (ResidueField (normInteger K)))
      (Set.range fun j : Fin (ramIdx p hϖ) => ϖ ^ (j : ℕ)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  choose D Y hDY using exists_digits p hϖ
  set rem : ℕ → normInteger K := fun n => Y^[n] x with hrem
  set A : ℕ → Fin (ramIdx p hϖ) → WittVector p (ResidueField (normInteger K)) :=
    fun n j => ∑ i ∈ Finset.range n, (p : WittVector p (ResidueField (normInteger K))) ^ i * D (rem i) j
    with hA
  have hinv : ∀ n, x = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n := by
    intro n
    induction n with
    | zero => simp [hA, hrem]
    | succ n ih =>
      have hr : rem (n + 1) = Y (rem n) := by
        simp only [hrem]; rw [Function.iterate_succ_apply']
      have hA1 : ∀ j, A (n + 1) j = A n j + (p : WittVector p (ResidueField (normInteger K))) ^ n * D (rem n) j := by
        intro j; simp only [hA, Finset.sum_range_succ]
      calc x = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n := ih
        _ = ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n *
              (∑ j, cohenMap K p (D (rem n) j) * ϖ ^ (j : ℕ) + p * Y (rem n)) := by
            rw [← hDY (rem n)]
        _ = ∑ j, cohenMap K p (A (n + 1) j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ (n + 1) * rem (n + 1) := by
            rw [hr]
            simp only [hA1, map_add, map_mul, map_pow, map_natCast, add_mul, Finset.sum_add_distrib,
              mul_add, Finset.mul_sum, mul_assoc]
            ring
  have hlim : ∀ j, ∃ W : WittVector p (ResidueField (normInteger K)),
      ∀ n, W - A n j ∈ span {(p : WittVector p (ResidueField (normInteger K))) ^ n} := by
    intro j
    refine WittLift.exists_limit (fun n => A n j) fun n => ?_
    simp only [hA, Finset.sum_range_succ, add_sub_cancel_left]
    exact mem_span_singleton.2 (dvd_mul_right _ _)
  choose W hW using hlim
  have hx : x = ∑ j, cohenMap K p (W j) * ϖ ^ (j : ℕ) := by
    apply eq_of_forall_sub_mem_span_pow (K := K) (a := (p : normInteger K)) (norm_natCast_prime_lt_one p)
    intro n
    have hc : ∀ j, cohenMap K p (A n j) - cohenMap K p (W j) ∈ span {(p : normInteger K) ^ n} := by
      intro j
      obtain ⟨c, hc⟩ := mem_span_singleton.1 (hW j n)
      have : A n j - W j = -((p : WittVector p (ResidueField (normInteger K))) ^ n * c) := by
        rw [← hc]; ring
      rw [← map_sub, this, map_neg, map_mul, map_pow, map_natCast]
      exact neg_mem (mem_span_singleton.2 (dvd_mul_right _ _))
    nth_rewrite 1 [hinv n]
    have : ∑ j, cohenMap K p (A n j) * ϖ ^ (j : ℕ) + (p : normInteger K) ^ n * rem n -
        ∑ j, cohenMap K p (W j) * ϖ ^ (j : ℕ) =
        ∑ j, (cohenMap K p (A n j) - cohenMap K p (W j)) * ϖ ^ (j : ℕ) +
          (p : normInteger K) ^ n * rem n := by
      simp only [sub_mul, Finset.sum_sub_distrib]; ring
    rw [this]
    refine add_mem (Submodule.sum_mem _ fun j _ => ?_) (mem_span_singleton.2 (dvd_mul_right _ _))
    exact Ideal.mul_mem_right _ _ (hc j)
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← cohen_smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def cohenBasis : Module.Basis (Fin (ramIdx p hϖ)) (WittVector p (ResidueField (normInteger K)))
    (normInteger K) :=
  Module.Basis.mk (linearIndependent_unif_pow p hϖ) (span_unif_pow_eq_top p hϖ).ge

@[simp]
theorem cohenBasis_apply (j : Fin (ramIdx p hϖ)) : cohenBasis p hϖ j = ϖ ^ (j : ℕ) :=
  Module.Basis.mk_apply _ _ _

end Cohen

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace ExtRobba

open IsLocalRing WittVector Ideal TensorProduct

section WittInt

variable (p : ℕ) [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

def wittInt : Subring (WittVector p L) := (WittVector.map (normInteger L).subtype).range

theorem mem_wittInt_iff {w : WittVector p L} : w ∈ wittInt p ↔ ∀ n, ‖w.coeff n‖ ≤ 1 := by
  constructor
  · rintro ⟨v, rfl⟩ n
    rw [WittVector.map_coeff]
    exact mem_normInteger.1 (v.coeff n).2
  · intro h
    refine ⟨WittVector.mk p fun n => ⟨w.coeff n, mem_normInteger.2 (h n)⟩, ?_⟩
    ext n
    simp [WittVector.map_coeff]

theorem teichmuller_mem_wittInt {a : L} (ha : ‖a‖ ≤ 1) : teichmuller p a ∈ wittInt p := by
  rw [mem_wittInt_iff]
  intro n
  cases n with
  | zero => simpa using ha
  | succ n => simp [teichmuller_coeff_pos]

variable [CharP L p] [PerfectRing L p]


theorem coeff_eq_of_sub_mem {a b : WittVector p L} {m : ℕ}
    (h : a - b ∈ span {(p : WittVector p L) ^ m}) {i : ℕ} (hi : i < m) : a.coeff i = b.coeff i :=
  le_coeff_eq_iff_le_sub_coeff_eq_zero.2 ((mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 h) i hi

end WittInt

section Gamma

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]

set_option linter.unusedVariables false in

def WittOver (ι : ResidueField (normInteger K) →+* L) : Type _ := WittVector p L

variable (ι : ResidueField (normInteger K) →+* L)

instance : CommRing (WittOver p ι) := inferInstanceAs (CommRing (WittVector p L))

instance : Algebra (WittVector p (ResidueField (normInteger K))) (WittOver p ι) :=
  (WittVector.map ι).toAlgebra

def WittOver.equiv : WittOver p ι ≃+* WittVector p L := RingEquiv.refl _

theorem algebraMap_wittOver (w : WittVector p (ResidueField (normInteger K))) :
    WittOver.equiv p ι (algebraMap _ (WittOver p ι) w) = WittVector.map ι w := rfl

abbrev Gamma := WittOver p ι ⊗[WittVector p (ResidueField (normInteger K))] normInteger K

def gammaOfInt : normInteger K →+* Gamma p ι :=
  (Algebra.TensorProduct.includeRight :
    normInteger K →ₐ[WittVector p (ResidueField (normInteger K))] Gamma p ι).toRingHom

@[simp]
theorem gammaOfInt_apply (o : normInteger K) : gammaOfInt p ι o = 1 ⊗ₜ o := rfl

instance gammaAlgebraInt : Algebra (normInteger K) (Gamma p ι) := (gammaOfInt p ι).toAlgebra


def gammaPi (ϖ : normInteger K) : Gamma p ι := 1 ⊗ₜ ϖ

abbrev redAlgebra : Algebra (WittVector p (ResidueField (normInteger K))) L :=
  (ι.comp WittVector.constantCoeff).toAlgebra

def gammaRed : Gamma p ι →+* L :=
  letI := redAlgebra p ι
  (Algebra.TensorProduct.lift
    ({ toRingHom := WittVector.constantCoeff.comp (WittOver.equiv p ι).toRingHom
       commutes' := fun r => by
        change (WittVector.map ι r).coeff 0 = ι (r.coeff 0)
        rw [WittVector.map_coeff] } : WittOver p ι →ₐ[WittVector p (ResidueField (normInteger K))] L)
    ({ toRingHom := ι.comp (residue (normInteger K))
       commutes' := fun r => by
        change ι (residue _ (cohenMap K p r)) = ι (r.coeff 0)
        rw [residue_cohenMap] } : normInteger K →ₐ[WittVector p (ResidueField (normInteger K))] L)
    (fun _ _ => Commute.all _ _)).toRingHom

@[simp]
theorem gammaRed_tmul (w : WittOver p ι) (o : normInteger K) :
    gammaRed p ι (w ⊗ₜ o) = (WittOver.equiv p ι w).coeff 0 * ι (residue _ o) := by
  let _ := redAlgebra p ι
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem gammaRed_surjective : Function.Surjective (gammaRed p ι) := by
  intro a
  refine ⟨(WittOver.equiv p ι).symm (teichmuller p a) ⊗ₜ 1, ?_⟩
  rw [gammaRed_tmul, map_one, map_one, mul_one]
  exact teichmuller_coeff_zero p a

def wittOverInt : Subring (WittOver p ι) := (wittInt p).comap (WittOver.equiv p ι).toRingHom

theorem mem_wittOverInt_iff {w : WittOver p ι} :
    w ∈ wittOverInt p ι ↔ ∀ n, ‖(WittOver.equiv p ι w).coeff n‖ ≤ 1 := by
  rw [wittOverInt, Subring.mem_comap]; exact mem_wittInt_iff p

theorem algebraMap_mem_wittOverInt (hι : ∀ a, ‖ι a‖ ≤ 1)
    (c : WittVector p (ResidueField (normInteger K))) :
    algebraMap _ (WittOver p ι) c ∈ wittOverInt p ι := by
  rw [mem_wittOverInt_iff]
  intro n
  rw [algebraMap_wittOver, WittVector.map_coeff]
  exact hι _

def gammaInt : Subring (Gamma p ι) :=
  Subring.closure {x | ∃ w ∈ wittOverInt p ι, ∃ o : normInteger K, x = w ⊗ₜ o}

theorem tmul_mem_gammaInt {w : WittOver p ι} (hw : w ∈ wittOverInt p ι) (o : normInteger K) :
    w ⊗ₜ o ∈ gammaInt p ι :=
  Subring.subset_closure ⟨w, hw, o, rfl⟩

theorem gammaPi_eq (ϖ : normInteger K) : gammaPi p ι ϖ = 1 ⊗ₜ ϖ := rfl

theorem natCast_eq_tmul_left (n : ℕ) : (n : Gamma p ι) = (n : WittOver p ι) ⊗ₜ (1 : normInteger K) := by
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom
    (R := WittVector p (ResidueField (normInteger K))) (A := WittOver p ι) (B := normInteger K))]
  rfl

theorem natCast_eq_tmul_right (n : ℕ) : (n : Gamma p ι) = (1 : WittOver p ι) ⊗ₜ (n : normInteger K) := by
  rw [← map_natCast (gammaOfInt p ι)]
  rfl

theorem wittOver_equiv_natCast (n : ℕ) : WittOver.equiv p ι (n : WittOver p ι) = (n : WittVector p L) :=
  map_natCast _ n

theorem exists_mem_gammaInt_gammaRed_eq {a : L} (ha : ‖a‖ ≤ 1) :
    ∃ x ∈ gammaInt p ι, gammaRed p ι x = a := by
  refine ⟨(WittOver.equiv p ι).symm (teichmuller p a) ⊗ₜ 1, tmul_mem_gammaInt p ι ?_ 1, ?_⟩
  · rw [mem_wittOverInt_iff, RingEquiv.apply_symm_apply]
    exact (mem_wittInt_iff p).1 (teichmuller_mem_wittInt p ha)
  · rw [gammaRed_tmul, map_one, map_one, mul_one, RingEquiv.apply_symm_apply]
    exact teichmuller_coeff_zero p a

theorem mul_natCast_tmul (a : WittOver p ι) (o : normInteger K) (n : ℕ) :
    (a * (n : WittOver p ι)) ⊗ₜ o = a ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((n : normInteger K) * o) := by
  calc (a * (n : WittOver p ι)) ⊗ₜ o
      = (a ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] o) * ((n : WittOver p ι) ⊗ₜ (1 : normInteger K)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    _ = (a ⊗ₜ o) * (n : Gamma p ι) := by rw [natCast_eq_tmul_left]
    _ = (a ⊗ₜ o) * ((1 : WittOver p ι) ⊗ₜ (n : normInteger K)) := by rw [natCast_eq_tmul_right]
    _ = a ⊗ₜ ((n : normInteger K) * o) := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm]

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)
include hϖ
include hϖ

def gammaBasis : Module.Basis (Fin (ramIdx p hϖ)) (WittOver p ι) (Gamma p ι) :=
  Algebra.TensorProduct.basis (WittOver p ι) (cohenBasis p hϖ)

@[simp]
theorem gammaBasis_apply (j : Fin (ramIdx p hϖ)) : gammaBasis p ι hϖ j = 1 ⊗ₜ (ϖ ^ (j : ℕ)) := by
  simp [gammaBasis]

theorem gammaBasis_repr_tmul (w : WittOver p ι) (o : normInteger K) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr (w ⊗ₜ o) j =
      w * algebraMap _ (WittOver p ι) ((cohenBasis p hϖ).repr o j) := by
  simp [gammaBasis, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (x : Gamma p ι) :
    x = ∑ j, (gammaBasis p ι hϖ).repr x j ⊗ₜ (ϖ ^ (j : ℕ)) := by
  conv_lhs => rw [← (gammaBasis p ι hϖ).sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gammaBasis, Algebra.TensorProduct.basis_repr_symm_apply', cohenBasis_apply]

theorem gammaRed_tmul_unif_pow (w : WittOver p ι) {j : ℕ} (hj : j ≠ 0) :
    gammaRed p ι (w ⊗ₜ (ϖ ^ j)) = 0 := by
  rw [gammaRed_tmul, map_pow]
  have : residue (normInteger K) ϖ = 0 :=
    (residue_eq_zero_iff _).2 hϖ.not_isUnit
  rw [this, zero_pow hj, map_zero, mul_zero]

def fin0 : Fin (ramIdx p hϖ) := ⟨0, ramIdx_pos p hϖ⟩

theorem gammaRed_eq_coeff (x : Gamma p ι) :
    gammaRed p ι x = (WittOver.equiv p ι ((gammaBasis p ι hϖ).repr x (fin0 p hϖ))).coeff 0 := by
  conv_lhs => rw [eq_sum_tmul p ι hϖ x]
  rw [map_sum, Finset.sum_eq_single (fin0 p hϖ)]
  · simp [fin0]
  · intro j _ hj
    exact gammaRed_tmul_unif_pow p ι hϖ _ fun h => hj (Fin.ext h)
  · simp

theorem repr_mem_wittOverInt_of_tmul (hι : ∀ a, ‖ι a‖ ≤ 1) {w : WittOver p ι}
    (hw : w ∈ wittOverInt p ι) (o : normInteger K) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr (w ⊗ₜ o) j ∈ wittOverInt p ι := by
  rw [gammaBasis_repr_tmul]
  exact mul_mem hw (algebraMap_mem_wittOverInt p ι hι _)

theorem mem_gammaInt_iff (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι} :
    x ∈ gammaInt p ι ↔ ∀ j, (gammaBasis p ι hϖ).repr x j ∈ wittOverInt p ι := by
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, o, rfl⟩ := hx
      exact repr_mem_wittOverInt_of_tmul p ι hϖ hι hw o
    | zero => simp
    | one =>
      intro j
      rw [Algebra.TensorProduct.one_def]
      exact repr_mem_wittOverInt_of_tmul p ι hϖ hι (one_mem _) 1 j
    | add x y _ _ hx hy =>
      intro j; rw [map_add, Finsupp.add_apply]; exact add_mem (hx j) (hy j)
    | neg x _ hx =>
      intro j; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx j)
    | mul x y _ _ hx hy =>
      intro j
      rw [eq_sum_tmul p ι hϖ x, eq_sum_tmul p ι hϖ y, Finset.sum_mul_sum, map_sum,
        Finsupp.finsetSum_apply]
      refine Subring.sum_mem _ fun a _ => ?_
      rw [map_sum, Finsupp.finsetSum_apply]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact repr_mem_wittOverInt_of_tmul p ι hϖ hι (mul_mem (hx a) (hy b)) _ j
  · intro h
    rw [eq_sum_tmul p ι hϖ x]
    exact Subring.sum_mem _ fun j _ => tmul_mem_gammaInt p ι (h j) _

theorem norm_gammaRed_le_one (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι} (hx : x ∈ gammaInt p ι) :
    ‖gammaRed p ι x‖ ≤ 1 := by
  rw [gammaRed_eq_coeff p ι hϖ]
  exact (mem_wittOverInt_iff p ι).1 ((mem_gammaInt_iff p ι hϖ hι).1 hx _) 0

theorem repr_sum_tmul (a : Fin (ramIdx p hϖ) → WittOver p ι) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr (∑ i, a i ⊗ₜ (ϖ ^ (i : ℕ))) j = a j := by
  have : ∑ i, a i ⊗ₜ (ϖ ^ (i : ℕ)) = ∑ i, a i • gammaBasis p ι hϖ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gammaBasis, Algebra.TensorProduct.basis_repr_symm_apply', cohenBasis_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem exists_gammaPi_pow_ramIdx :
    ∃ v : (Gamma p ι)ˣ, gammaPi p ι ϖ ^ ramIdx p hϖ = (p : Gamma p ι) * v := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  refine ⟨Units.map (gammaOfInt p ι).toMonoidHom u⁻¹, ?_⟩
  rw [gammaPi_eq, Algebra.TensorProduct.tmul_pow, one_pow, natCast_eq_tmul_right,
    Units.coe_map]
  change _ = _ * (gammaOfInt p ι) _
  rw [gammaOfInt_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hu, mul_assoc, Units.mul_inv,
    mul_one]

theorem span_gammaPi_pow_eq (m : ℕ) :
    span {gammaPi p ι ϖ ^ (ramIdx p hϖ * m)} = span {(p : Gamma p ι) ^ m} := by
  obtain ⟨v, hv⟩ := exists_gammaPi_pow_ramIdx p ι hϖ
  rw [pow_mul, hv, mul_pow, ← Units.val_pow_eq_pow_val]
  exact span_singleton_mul_right_unit (v ^ m).isUnit _

theorem repr_natCast_pow_mul (m : ℕ) (z : Gamma p ι) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr ((p : Gamma p ι) ^ m * z) j =
      (p : WittOver p ι) ^ m * (gammaBasis p ι hϖ).repr z j := by
  have : (p : Gamma p ι) ^ m * z = ((p : WittOver p ι) ^ m) • z := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mem_span_of_mem_span {x : Gamma p ι} {m : ℕ}
    (hx : x ∈ span {(p : Gamma p ι) ^ m}) (j : Fin (ramIdx p hϖ)) :
    WittOver.equiv p ι ((gammaBasis p ι hϖ).repr x j) ∈ span {(p : WittVector p L) ^ m} := by
  obtain ⟨z, rfl⟩ := mem_span_singleton'.1 hx
  rw [mul_comm, repr_natCast_pow_mul p ι hϖ, map_mul, map_pow, wittOver_equiv_natCast]
  exact mem_span_singleton.2 ⟨_, rfl⟩

theorem mem_span_of_repr_mem_span {x : Gamma p ι} {m : ℕ}
    (h : ∀ j, WittOver.equiv p ι ((gammaBasis p ι hϖ).repr x j) ∈ span {(p : WittVector p L) ^ m}) :
    x ∈ span {(p : Gamma p ι) ^ m} := by
  choose c hc using fun j => mem_span_singleton.1 (h j)
  set z : Gamma p ι := ∑ j, (WittOver.equiv p ι).symm (c j) ⊗ₜ (ϖ ^ (j : ℕ))
  have hx : x = (p : Gamma p ι) ^ m * z := by
    apply (gammaBasis p ι hϖ).repr.injective
    ext j
    rw [repr_natCast_pow_mul p ι hϖ, repr_sum_tmul p ι hϖ]
    apply (WittOver.equiv p ι).injective
    rw [hc j, map_mul, map_pow, wittOver_equiv_natCast, RingEquiv.apply_symm_apply]
  exact mem_span_singleton'.2 ⟨z, by rw [hx, mul_comm]⟩

theorem exists_eq_gammaPi_mul {x : Gamma p ι} (hx : gammaRed p ι x = 0) :
    ∃ y, x = gammaPi p ι ϖ * y ∧
      ((∀ a, ‖ι a‖ ≤ 1) → x ∈ gammaInt p ι → y ∈ gammaInt p ι) := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  have he := ramIdx_pos p hϖ
  set c := (gammaBasis p ι hϖ).repr x with hc_def
  have hc0 : (WittOver.equiv p ι (c (fin0 p hϖ))).coeff 0 = 0 := by
    rw [← gammaRed_eq_coeff p ι hϖ]; exact hx

  obtain ⟨v, hv⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero _).2 hc0)
  have hvint : c (fin0 p hϖ) ∈ wittOverInt p ι → (WittOver.equiv p ι).symm v ∈ wittOverInt p ι := by
    intro hint
    rw [mem_wittOverInt_iff] at hint ⊢
    intro n
    have h1 := hint (n + 1)
    rw [← hv, mul_charP_coeff_succ, norm_pow] at h1
    rw [RingEquiv.apply_symm_apply]
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h1
  set y0 : Gamma p ι := (WittOver.equiv p ι).symm v ⊗ₜ (ϖ ^ (ramIdx p hϖ - 1) * u)
  set yj : Fin (ramIdx p hϖ) → Gamma p ι := fun j =>
    if (j : ℕ) = 0 then y0 else c j ⊗ₜ (ϖ ^ ((j : ℕ) - 1))
  have hterm : ∀ j, c j ⊗ₜ (ϖ ^ (j : ℕ)) = gammaPi p ι ϖ * yj j := by
    intro j
    by_cases hj : (j : ℕ) = 0
    · have hj' : j = fin0 p hϖ := Fin.ext hj
      have hcv : c j = (WittOver.equiv p ι).symm v * (p : WittOver p ι) := by
        rw [hj']
        apply (WittOver.equiv p ι).injective
        rw [map_mul, RingEquiv.apply_symm_apply, wittOver_equiv_natCast, ← hv]
      simp only [yj, if_pos hj, y0, gammaPi_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hcv, hj, pow_zero, mul_natCast_tmul, mul_one, hu]
      congr 1
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]
    · simp only [yj, if_neg hj, gammaPi_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj)]
  refine ⟨∑ j, yj j, ?_, ?_⟩
  · conv_lhs => rw [eq_sum_tmul p ι hϖ x]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hterm j
  · intro hι hxint
    have hci := (mem_gammaInt_iff p ι hϖ hι).1 hxint
    refine Subring.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) = 0
    · simp only [yj, if_pos hj, y0]
      exact tmul_mem_gammaInt p ι (hvint (hci _)) _
    · simp only [yj, if_neg hj]
      exact tmul_mem_gammaInt p ι (hci j) _

theorem gammaRed_gammaPi : gammaRed p ι (gammaPi p ι ϖ) = 0 := by
  rw [gammaPi_eq, ← pow_one ϖ]
  exact gammaRed_tmul_unif_pow p ι hϖ 1 one_ne_zero

theorem ker_gammaRed : RingHom.ker (gammaRed p ι) = span {gammaPi p ι ϖ} := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    obtain ⟨y, rfl, -⟩ := exists_eq_gammaPi_mul p ι hϖ hx
    exact mem_span_singleton'.2 ⟨y, mul_comm _ _⟩
  · intro hx
    obtain ⟨y, rfl⟩ := mem_span_singleton'.1 hx
    rw [map_mul, gammaRed_gammaPi p ι hϖ, mul_zero]

theorem exists_mem_gammaInt_eq_gammaPi_mul (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι}
    (hx : x ∈ gammaInt p ι) (h0 : gammaRed p ι x = 0) :
    ∃ y ∈ gammaInt p ι, x = gammaPi p ι ϖ * y := by
  obtain ⟨y, hy, hint⟩ := exists_eq_gammaPi_mul p ι hϖ h0
  exact ⟨y, hint hι hx, hy⟩

theorem eq_zero_of_natCast_mul_eq_zero {x : Gamma p ι} (hx : (p : Gamma p ι) * x = 0) : x = 0 := by
  apply (gammaBasis p ι hϖ).repr.injective
  ext j
  have h := congrArg (fun z => (gammaBasis p ι hϖ).repr z j) hx
  rw [← pow_one (p : Gamma p ι), repr_natCast_pow_mul p ι hϖ, pow_one, map_zero, Finsupp.zero_apply] at h
  rw [map_zero, Finsupp.zero_apply]
  apply (WittOver.equiv p ι).injective
  have h2 := congrArg (WittOver.equiv p ι) h
  rw [map_mul, wittOver_equiv_natCast, map_zero] at h2
  rw [map_zero]
  exact (mul_eq_zero.1 h2).resolve_left (WittVector.p_nonzero p L)

theorem gammaPi_mem_nonZeroDivisors : gammaPi p ι ϖ ∈ nonZeroDivisors (Gamma p ι) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨v, hv⟩ := exists_gammaPi_pow_ramIdx p ι hϖ
  have he := ramIdx_pos p hϖ
  have h1 : gammaPi p ι ϖ ^ ramIdx p hϖ * x = 0 := by
    rw [← Nat.sub_add_cancel he, pow_succ, mul_assoc, mul_comm (gammaPi p ι ϖ) x, hx, mul_zero]
  rw [hv, mul_assoc] at h1
  have h2 := eq_zero_of_natCast_mul_eq_zero p ι hϖ h1
  have := congrArg (fun z => (↑v⁻¹ : Gamma p ι) * z) h2
  simpa [← mul_assoc] using this

theorem isAdicComplete_gammaPi : IsAdicComplete (span {gammaPi p ι ϖ}) (Gamma p ι) := by
  have he := ramIdx_pos p hϖ
  have hmem : ∀ (n : ℕ) (x y : Gamma p ι),
      x ≡ y [SMOD (span {gammaPi p ι ϖ} ^ n • ⊤ : Submodule (Gamma p ι) (Gamma p ι))] ↔
        x - y ∈ span {gammaPi p ι ϖ ^ n} := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, span_singleton_pow]
  have hle : ∀ n m, n ≤ m → span {gammaPi p ι ϖ ^ m} ≤ span {gammaPi p ι ϖ ^ n} := fun n m h =>
    span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    simp only [hmem, sub_zero] at hx
    have hc : ∀ j, (gammaBasis p ι hϖ).repr x j = 0 := by
      intro j
      apply (WittOver.equiv p ι).injective
      rw [map_zero]
      apply WittLift.eq_zero_of_forall_mem
      intro m
      apply repr_mem_span_of_mem_span p ι hϖ _ j
      rw [← span_gammaPi_pow_eq p ι hϖ]
      exact hx _
    rw [eq_sum_tmul p ι hϖ x]
    simp [hc]
  · intro f hf
    simp only [hmem] at hf
    set a : Fin (ramIdx p hϖ) → ℕ → WittVector p L :=
      fun j n => WittOver.equiv p ι ((gammaBasis p ι hϖ).repr (f (ramIdx p hϖ * n)) j) with ha_def
    have ha : ∀ j n, a j (n + 1) - a j n ∈ span {(p : WittVector p L) ^ n} := by
      intro j n
      have h1 : f (ramIdx p hϖ * n) - f (ramIdx p hϖ * (n + 1)) ∈ span {(p : Gamma p ι) ^ n} := by
        rw [← span_gammaPi_pow_eq p ι hϖ]
        exact hf (Nat.mul_le_mul_left _ (Nat.le_succ n))
      have h2 := repr_mem_span_of_mem_span p ι hϖ h1 j
      rw [map_sub, Finsupp.sub_apply, map_sub] at h2
      rw [← neg_sub]
      exact neg_mem h2
    choose W hW using fun j => WittLift.exists_limit (a j) (ha j)
    refine ⟨∑ j, (WittOver.equiv p ι).symm (W j) ⊗ₜ (ϖ ^ (j : ℕ)), fun n => ?_⟩
    rw [hmem]
    have h1 : f n - f (ramIdx p hϖ * n) ∈ span {gammaPi p ι ϖ ^ n} :=
      hf (Nat.le_mul_of_pos_left n he)
    have h2 : f (ramIdx p hϖ * n) - ∑ j, (WittOver.equiv p ι).symm (W j) ⊗ₜ (ϖ ^ (j : ℕ)) ∈
        span {gammaPi p ι ϖ ^ n} := by
      apply hle n (ramIdx p hϖ * n) (Nat.le_mul_of_pos_left n he)
      rw [span_gammaPi_pow_eq p ι hϖ]
      apply mem_span_of_repr_mem_span p ι hϖ
      intro j
      rw [map_sub, Finsupp.sub_apply, repr_sum_tmul p ι hϖ, map_sub, RingEquiv.apply_symm_apply]
      rw [← neg_sub]
      exact neg_mem (hW j n)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

theorem mem_gammaInt_of_forall (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι}
    (h : ∀ N : ℕ, ∃ y ∈ gammaInt p ι, x - y ∈ span {gammaPi p ι ϖ ^ N}) : x ∈ gammaInt p ι := by
  rw [mem_gammaInt_iff p ι hϖ hι]
  intro j
  rw [mem_wittOverInt_iff]
  intro n
  obtain ⟨y, hy, hxy⟩ := h (ramIdx p hϖ * (n + 1))
  rw [span_gammaPi_pow_eq p ι hϖ] at hxy
  have h1 := repr_mem_span_of_mem_span p ι hϖ hxy j
  rw [map_sub, Finsupp.sub_apply, map_sub] at h1
  rw [coeff_eq_of_sub_mem p h1 (Nat.lt_succ_self n)]
  exact (mem_wittOverInt_iff p ι).1 ((mem_gammaInt_iff p ι hϖ hι).1 hy j) n

end Gamma

section Frobenius

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : ResidueField (normInteger K) →+* L)

def wittOverFrob (a : ℕ) : WittOver p ι →+* WittOver p ι :=
  (WittOver.equiv p ι).symm.toRingHom.comp
    ((WittVector.map (iterateFrobenius L p a)).comp (WittOver.equiv p ι).toRingHom)

theorem wittOverFrob_coeff (a : ℕ) (w : WittOver p ι) (n : ℕ) :
    (WittOver.equiv p ι (wittOverFrob p ι a w)).coeff n = (WittOver.equiv p ι w).coeff n ^ p ^ a := by
  change (WittVector.map (iterateFrobenius L p a) (WittOver.equiv p ι w)).coeff n = _
  rw [WittVector.map_coeff, iterateFrobenius_def]

theorem wittOverFrob_bijective (a : ℕ) : Function.Bijective (wittOverFrob p ι a) := by
  have hb : Function.Bijective (iterateFrobenius L p a) := by
    rw [← coe_iterateFrobeniusEquiv]; exact (iterateFrobeniusEquiv L p a).bijective
  have hm : Function.Bijective (WittVector.map (iterateFrobenius L p a) : WittVector p L → WittVector p L) :=
    ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩
  exact (WittOver.equiv p ι).symm.bijective.comp (hm.comp (WittOver.equiv p ι).bijective)

theorem wittOverFrob_mem_wittOverInt (a : ℕ) {w : WittOver p ι} (hw : w ∈ wittOverInt p ι) :
    wittOverFrob p ι a w ∈ wittOverInt p ι := by
  rw [mem_wittOverInt_iff] at hw ⊢
  intro n
  rw [wittOverFrob_coeff, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hw n)

set_option linter.unusedVariables false in

def TwistedGamma (a : ℕ) : Type _ := Gamma p ι

instance (a : ℕ) : CommRing (TwistedGamma p ι a) := inferInstanceAs (CommRing (Gamma p ι))

instance (a : ℕ) : Algebra (WittVector p (ResidueField (normInteger K))) (TwistedGamma p ι a) :=
  @RingHom.toAlgebra _ (TwistedGamma p ι a) _ _
    ((algebraMap (WittVector p (ResidueField (normInteger K))) (Gamma p ι)).comp
      (WittVector.map (iterateFrobenius (ResidueField (normInteger K)) p a)))

variable (a : ℕ) (σ : normInteger K →+* normInteger K)

def gammaPhiLeft : WittOver p ι →ₐ[WittVector p (ResidueField (normInteger K))] TwistedGamma p ι a where
  toRingHom := (Algebra.TensorProduct.includeLeftRingHom (R := WittVector p (ResidueField (normInteger K)))
    (A := WittOver p ι) (B := normInteger K)).comp (wittOverFrob p ι a)
  commutes' := fun c => by
    change wittOverFrob p ι a (algebraMap _ (WittOver p ι) c) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] (1 : normInteger K) =
      algebraMap _ (Gamma p ι) (WittVector.map (iterateFrobenius _ p a) c)
    rw [Algebra.TensorProduct.algebraMap_apply]
    congr 1
    apply (WittOver.equiv p ι).injective
    ext n
    rw [wittOverFrob_coeff, algebraMap_wittOver, algebraMap_wittOver, WittVector.map_coeff,
      WittVector.map_coeff, WittVector.map_coeff, iterateFrobenius_def, map_pow]

def gammaPhiRight (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) :
    normInteger K →ₐ[WittVector p (ResidueField (normInteger K))] TwistedGamma p ι a where
  toRingHom := (gammaOfInt p ι).comp σ
  commutes' := fun c => by
    change (1 : WittOver p ι) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] σ (cohenMap K p c) =
      algebraMap _ (Gamma p ι) (WittVector.map (iterateFrobenius _ p a) c)
    have := congrArg (fun f => f c) (comp_cohenMap_of_residue p σ a hσ)
    simp only [RingHom.comp_apply] at this
    rw [this, Algebra.TensorProduct.algebraMap_apply']
    rfl

def gammaPhi (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) : Gamma p ι →+* Gamma p ι :=
  (Algebra.TensorProduct.lift (gammaPhiLeft p ι a) (gammaPhiRight p ι a σ hσ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem gammaPhi_tmul (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (w : WittOver p ι) (o : normInteger K) :
    gammaPhi p ι a σ hσ (w ⊗ₜ o) = wittOverFrob p ι a w ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] σ o := by
  have h := Algebra.TensorProduct.lift_tmul (gammaPhiLeft p ι a) (gammaPhiRight p ι a σ hσ)
    (fun _ _ => Commute.all _ _) w o
  refine h.trans ?_
  change ((wittOverFrob p ι a w ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] (1 : normInteger K) : Gamma p ι) *
    ((1 : WittOver p ι) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] σ o : Gamma p ι)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gammaRed_gammaPhi (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (x : Gamma p ι) :
    gammaRed p ι (gammaPhi p ι a σ hσ x) = gammaRed p ι x ^ p ^ a := by
  induction x using TensorProduct.induction_on with
  | zero => simp [zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  | tmul w o =>
    rw [gammaPhi_tmul p ι a σ hσ, gammaRed_tmul, gammaRed_tmul, wittOverFrob_coeff, hσ, map_pow, mul_pow]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    exact (add_pow_expChar_pow _ _ p a).symm

theorem gammaPhi_mem_gammaInt (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) {x : Gamma p ι} (hx : x ∈ gammaInt p ι) :
    gammaPhi p ι a σ hσ x ∈ gammaInt p ι := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, o, rfl⟩ := hx
    rw [gammaPhi_tmul]
    exact tmul_mem_gammaInt p ι (wittOverFrob_mem_wittOverInt p ι a hw) _
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem gammaPhi_gammaPi (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (ϖ : normInteger K) : gammaPhi p ι a σ hσ (gammaPi p ι ϖ) = gammaPi p ι (σ ϖ) := by
  rw [gammaPi_eq, gammaPhi_tmul, map_one, gammaPi_eq]

theorem gammaPhi_bijective (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (hbij : Function.Bijective σ) {ϖ : normInteger K} (hϖ : Irreducible ϖ) :
    Function.Bijective (gammaPhi p ι a σ hσ) := by
  set e := RingEquiv.ofBijective σ hbij
  have hϖ' : Irreducible (σ ϖ) := by
    have : Irreducible (e ϖ) := (MulEquiv.irreducible_iff (f := e.toMulEquiv)).2 hϖ
    simpa [e] using this
  have hram : ramIdx p hϖ' = ramIdx p hϖ := by
    have h1 := norm_natCast_prime_eq (K := K) p hϖ
    have h2 := norm_natCast_prime_eq (K := K) p hϖ'
    have hn : ‖((σ ϖ : normInteger K) : K)‖ = ‖(ϖ : K)‖ := by
      obtain ⟨n, hn⟩ := exists_norm_eq_pow hϖ (x := σ ϖ) hϖ'.ne_zero
      obtain ⟨m, hm⟩ := exists_norm_eq_pow hϖ' (x := ϖ) hϖ.ne_zero
      have h0 := norm_unif_pos hϖ
      have h1' := norm_unif_lt_one hϖ
      rw [hn] at hm
      rw [← pow_mul] at hm
      have : 1 = n * m := by
        have := pow_right_injective₀ h0 h1'.ne (show ‖(ϖ : K)‖ ^ 1 = ‖(ϖ : K)‖ ^ (n * m) by rw [pow_one]; exact hm)
        exact this
      have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_right this.symm
      rw [hn, hn1, pow_one]
    rw [hn] at h2
    rw [h1] at h2
    exact (pow_right_injective₀ (norm_unif_pos hϖ) (norm_unif_lt_one hϖ).ne h2).symm

  have hphi : ∀ x : Gamma p ι, gammaPhi p ι a σ hσ x =
      ∑ j : Fin (ramIdx p hϖ), wittOverFrob p ι a ((gammaBasis p ι hϖ).repr x j) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (j : ℕ)) := by
    intro x
    conv_lhs => rw [eq_sum_tmul p ι hϖ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gammaPhi_tmul p ι a σ hσ, map_pow]
  obtain ⟨finv, hfl, hfr⟩ : ∃ g : WittOver p ι → WittOver p ι,
      Function.LeftInverse g (wittOverFrob p ι a) ∧ Function.RightInverse g (wittOverFrob p ι a) :=
    ⟨Function.surjInv (wittOverFrob_bijective p ι a).2,
      Function.leftInverse_surjInv (wittOverFrob_bijective p ι a),
      Function.rightInverse_surjInv (wittOverFrob_bijective p ι a).2⟩
  have hsum : ∀ c : Fin (ramIdx p hϖ) → WittOver p ι, ∀ j : Fin (ramIdx p hϖ'),
      (gammaBasis p ι hϖ').repr (∑ i : Fin (ramIdx p hϖ), c i ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (i : ℕ))) j =
        c (Fin.cast hram j) := by
    intro c j
    have : ∑ i : Fin (ramIdx p hϖ), c i ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (i : ℕ)) =
        ∑ i : Fin (ramIdx p hϖ'), c (Fin.cast hram i) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (i : ℕ)) := by
      rw [← (finCongr hram.symm).sum_comp]
      rfl
    rw [this, repr_sum_tmul p ι hϖ']
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · apply (gammaBasis p ι hϖ).repr.injective
    ext j
    have h := congrArg (fun z => (gammaBasis p ι hϖ').repr z (Fin.cast hram.symm j)) hxy
    simp only [hphi, hsum] at h
    exact (wittOverFrob_bijective p ι a).1 (by simpa using h)
  · refine ⟨∑ j : Fin (ramIdx p hϖ), finv ((gammaBasis p ι hϖ').repr y (Fin.cast hram.symm j)) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] (ϖ ^ (j : ℕ)), ?_⟩
    apply (gammaBasis p ι hϖ').repr.injective
    ext j
    rw [hphi, hsum, repr_sum_tmul p ι hϖ, hfr]
    simp

end Frobenius

end ExtRobba

end GroundTheory.PAdicHodge
end
end
