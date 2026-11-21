import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Mathlib
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd

section
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))

def IntC (x : C) : Prop := 0 ≤ v x

def IntS {σ : Type*} (f : MvPowerSeries σ C) : Prop := ∀ μ, IntC v (coeff μ f)

variable {v}

theorem intC_zero : IntC v 0 := by
  unfold IntC
  simp
theorem intC_one : IntC v 1 := by
  unfold IntC
  simp
theorem intC_add {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)
theorem intC_neg {x : C} (hx : IntC v x) : IntC v (-x) := by
  unfold IntC at *
  rwa [AddValuation.map_neg]
theorem intC_mul {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x * y) := by
  unfold IntC at *
  rw [AddValuation.map_mul]
  exact add_nonneg hx hy
theorem intC_sub {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x - y) := by
  rw [sub_eq_add_neg]
  exact intC_add hx (intC_neg hy)
theorem intC_natCast (n : ℕ) : IntC v (n : C) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact intC_zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact intC_add ih intC_one
theorem intC_intCast (n : ℤ) : IntC v (n : C) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact intC_natCast n
  | negSucc n =>
    rw [Int.cast_negSucc]
    exact intC_neg (intC_natCast _)
theorem intC_sum {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (IntC v) (fun _ _ => intC_add) intC_zero h
theorem intC_prod {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntC v) (fun _ _ => intC_mul) intC_one h
theorem intC_finsum {ι : Type*} {f : ι → C} (h : ∀ i, IntC v (f i)) : IntC v (∑ᶠ i, f i) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact intC_sum _ fun i _ => h i
  · rw [finsum_of_infinite_support hs]
    exact intC_zero

variable {σ τ : Type*}

theorem intS_mul {f g : MvPowerSeries σ C} (hf : IntS v f) (hg : IntS v g) : IntS v (f * g) := by
  intro μ
  rw [coeff_mul]
  exact intC_sum _ fun p _ => intC_mul (hf _) (hg _)

theorem intS_one : IntS v (1 : MvPowerSeries σ C) := by
  intro μ
  rw [coeff_one]
  split_ifs
  · exact intC_one
  · exact intC_zero

theorem intS_pow {f : MvPowerSeries σ C} (hf : IntS v f) (n : ℕ) : IntS v (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact intS_one
  | succ n ih =>
    rw [pow_succ]
    exact intS_mul ih hf

theorem intS_prod {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS v (f i)) :
    IntS v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntS v) (fun _ _ => intS_mul) intS_one h

private theorem hasSubst_lemma [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

theorem intS_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS v (a s)) {γ : MvPowerSeries σ C} (hγ : IntS v γ) : IntS v (subst a γ) := by
  have hsub : HasSubst a := hasSubst_lemma ha0
  intro μ
  rw [coeff_subst hsub]
  refine intC_finsum fun d => ?_
  rw [smul_eq_mul]
  exact intC_mul (hγ d) (intS_prod _ (fun s _ => intS_pow (ha s) _) μ)

def LowLt {σ : Type*} (K : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < K → IntC v (coeff μ f)

def OrdV {σ : Type*} (D : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < D → coeff μ f = 0

private theorem degree_add_lemma_2 (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add _ a b
  | exact Finsupp.sum_add_index' (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

theorem low_mul {E D D' : ℕ} {f g : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f)
    (hg : OrdV D' g) (hg' : LowLt (v := v) (E + D') g) :
    OrdV (D + D') (f * g) ∧ LowLt (v := v) (E + (D + D')) (f * g) := by
  constructor
  · intro μ hμ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
    · rw [hg p.2 (by omega), mul_zero]
  · intro μ hμ
    rw [coeff_mul]
    refine intC_sum _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
      exact intC_zero
    · by_cases h2 : p.2.degree < D'
      · rw [hg p.2 h2, mul_zero]
        exact intC_zero
      · exact intC_mul (hf' p.1 (by omega)) (hg' p.2 (by omega))

theorem low_one (E : ℕ) : OrdV 0 (1 : MvPowerSeries σ C) ∧ LowLt (v := v) E (1 : MvPowerSeries σ C) :=
  ⟨fun _ hμ => absurd hμ (Nat.not_lt_zero _), fun μ _ => intS_one μ⟩

theorem low_pow {E D : ℕ} {f : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f) (n : ℕ) :
    OrdV (n * D) (f ^ n) ∧ LowLt (v := v) (E + n * D) (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.add_zero]
    exact low_one E
  | succ n ih =>
    rw [pow_succ, Nat.add_mul, Nat.one_mul]
    exact low_mul ih.1 ih.2 hf hf'

theorem low_prod {E : ℕ} {t : σ → MvPowerSeries σ C} (ht : ∀ s, OrdV 1 (t s))
    (ht' : ∀ s, LowLt (v := v) (E + 1) (t s)) (S : Finset σ) (d : σ → ℕ) :
    OrdV (∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) ∧ LowLt (v := v) (E + ∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, Nat.add_zero]
    exact low_one E
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp := low_pow (ht a) (ht' a) (d a)
    rw [Nat.mul_one] at hp
    exact low_mul hp.1 hp.2 ih.1 ih.2

theorem deg_one_single (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ y, d = Finsupp.single y 1 := by
  have hdeg : ∑ i ∈ d.support, d i = 1 := h
  have h1 : ∀ x ∈ d.support, d x = 1 := by
    intro x hx
    have hle := Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) hx
    have h0 : d x ≠ 0 := Finsupp.mem_support_iff.1 hx
    omega
  have hcard : d.support.card = 1 := by
    rw [← hdeg, Finset.sum_congr rfl h1]
    simp
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcard
  refine ⟨y, Finsupp.ext fun x => ?_⟩
  by_cases hx : x = y
  · subst hx
    rw [Finsupp.single_eq_same]
    exact h1 x (by rw [hy]; exact Finset.mem_singleton_self x)
  · have hxs : x ∉ d.support := by
      rw [hy]
      simpa using hx
    have hdx : d x = 0 := by
      by_contra h'
      exact hxs (Finsupp.mem_support_iff.2 h')
    rw [hdx, Finsupp.single_apply, if_neg (Ne.symm hx)]

theorem intC_det {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n C) (hA : ∀ i j, IntC v (A i j)) :
    IntC v A.det := by
  rw [Matrix.det_apply]
  refine intC_sum _ fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact intC_mul (intC_intCast _) (intC_prod _ fun i _ => hA _ _)




end Formalism.L2.FormalSeriesBounds.AltInv
end
end

section
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem intS_invG {σ : Type*} [Fintype σ] (Φ t G : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (hG : ∀ x, IntS v (G x)) (heq : ∀ x, subst t (Φ x) = G x) :
    ∀ y, IntS v (t y) := by
  set L : Matrix σ σ C := Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) with hLdef
  have hdet0 : L.det ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hL; exact WithTop.top_ne_coe hL
  have hord : ∀ s, OrdV 1 (t s) := fun s μ hμ => by
    have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 (by omega)
    subst this; simpa using ht0 s
  have hs : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  suffices key : ∀ E : ℕ, ∀ y, LowLt (v := v) E (t y) by
    intro y μ; exact key (μ.degree + 1) y μ (Nat.lt_succ_self _)
  intro E
  induction E with
  | zero => intro y μ h; exact absurd h (Nat.not_lt_zero _)
  | succ E ih =>
    intro y μ hμ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hμ with hlt | heqd
    · exact ih y μ hlt

    cases E with
    | zero =>
      have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 heqd
      subst this; simp [ht0 y, intC_zero]
    | succ E' =>

      have hlow : ∀ s, LowLt (v := v) (E' + 1) (t s) := ih
      have hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree → IntC v (coeff μ (d.prod fun s n => t s ^ n)) := by
        intro d hd
        have hp := low_prod (v := v) hord hlow d.support d
        have : (d.prod fun s n => t s ^ n) = ∏ s ∈ d.support, t s ^ d s := rfl
        rw [this]
        have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
        exact hp.2 μ (by omega)

      have heqx : ∀ x, ∑ y', L x y' * coeff μ (t y') = coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) := by
        intro x
        have h1 := congrArg (coeff μ) (heq x)
        rw [coeff_subst hs] at h1
        have hfin := coeff_subst_finite hs (Φ x) μ
        set T : (σ →₀ ℕ) → C := fun d => coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n) with hT
        have hsplit : ∀ d, T d = (if d.degree = 1 then T d else 0) + (if d.degree = 1 then 0 else T d) := by
          intro d; split_ifs <;> simp
        have hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact hd; exact absurd rfl hd)
        have hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact absurd rfl hd; exact hd)
        have h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) +
            ∑ᶠ d, (if d.degree = 1 then 0 else T d) := by
          rw [← finsum_add_distrib hfg hfh]; exact finsum_congr hsplit
        have h3 : (∑ᶠ d, if d.degree = 1 then T d else 0) = ∑ y', L x y' * coeff μ (t y') := by
          rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y' => Finsupp.single y' 1)
            (fun d hd => by
              simp only [Function.mem_support] at hd
              split_ifs at hd with hd1
              · obtain ⟨y', rfl⟩ := deg_one_single d hd1
                simp
              · exact absurd rfl hd)]
          rw [Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [if_pos (by simp), hT]
          simp only [smul_eq_mul]
          rw [Finsupp.prod_single_index (by simp), pow_one]
          rfl
        rw [h2, h3] at h1
        exact eq_sub_of_add_eq h1

      have hc : ∀ x, IntC v (coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n))) := by
        intro x
        refine intC_sub ?_ (intC_finsum fun d => ?_)
        · exact hG x μ
        · split_ifs with hd1
          · exact intC_zero
          · by_cases hd0 : d = 0
            · subst hd0; rw [coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul]; exact intC_zero
            · have : 2 ≤ d.degree := by
                have : d.degree ≠ 0 := fun h0 => hd0 ((Finsupp.degree_eq_zero_iff d).1 h0)
                omega
              rw [smul_eq_mul]; exact intC_mul (hΦ x d) (hbig d this)

      set w : σ → C := fun y' => coeff μ (t y') with hw
      set c : σ → C := fun x => coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) with hcdef
      have hLw : L.mulVec w = c := by
        funext x; simp only [Matrix.mulVec, dotProduct]; exact heqx x
      have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet0
      have hwsol : w = L⁻¹.mulVec c := by
        rw [← hLw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hunit, Matrix.one_mulVec]
      have hinv : ∀ i j, IntC v (L⁻¹ i j) := by
        intro i j
        rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        refine intC_mul ?_ ?_
        · unfold IntC; rw [AddValuation.map_inv, hL]; simp
        · rw [Matrix.adjugate_apply]
          refine intC_det _ fun a b => ?_
          rw [Matrix.updateRow_apply]
          split_ifs
          · rw [Pi.single_apply]; split_ifs; exact intC_one; exact intC_zero
          · exact hΦ a _
      have : w y = (L⁻¹.mulVec c) y := by rw [← hwsol]
      show IntC v (w y)
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      exact intC_sum _ fun x _ => intC_mul (hinv y x) (hc x)

end Formalism.L2.FormalSeriesBounds.AltInv
end
end

section
noncomputable section
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace AbstractGermZero

open Formalism.IncomingBounds

variable {C : Type} [Field C] (V : VF C)

def AbstractGermZeroCondition : Prop :=
  ∀ (I : Fin 2 → Type) [∀ g, Fintype (I g)] (t t₂ φ φ₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) → (∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0) →
    (∀ g k, MvPowerSeries.constantCoeff (φ g k) = 0) → (∀ g k, IntS V (φ g k)) →
    (∀ g, V.v (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ g k)).det = 0) →
    (∀ g k, MvPowerSeries.constantCoeff (φ₂ g k) = 0) → (∀ g k, IntS V (φ₂ g k)) →
    (∀ g, V.v (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ₂ g k)).det = 0) →
    (∀ g k, MvPowerSeries.subst (t g) (φ g k) = MvPowerSeries.subst (t₂ g) (φ₂ g k)) →
    IntGerm V t = IntGerm V t₂

theorem intS_iff_alt {σ : Type} (F : MvPowerSeries σ C) : IntS V F ↔ AltInv.IntS V.v F := by
  simp only [IntS, AltInv.IntS, AltInv.IntC]
  exact Iff.rfl

theorem one_group {σ : Type} [Fintype σ] (t t₂ φ φ₂ : σ → MvPowerSeries σ C)
    (ht0₂ : ∀ c, MvPowerSeries.constantCoeff (t₂ c) = 0) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hφ0 : ∀ k, MvPowerSeries.constantCoeff (φ k) = 0) (hφ : ∀ k, IntS V (φ k))
    (hL : V.v (Matrix.of fun k c : σ => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)).det = 0)
    (hφ0₂ : ∀ k, MvPowerSeries.constantCoeff (φ₂ k) = 0) (hφ₂ : ∀ k, IntS V (φ₂ k))
    (heq : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t₂ (φ₂ k)) :
    ∃ h : σ → MvPowerSeries σ C, (∀ c, MvPowerSeries.constantCoeff (h c) = 0) ∧ (∀ c, IntS V (h c)) ∧
      ∀ c, t c = MvPowerSeries.subst t₂ (h c) := by
  classical

  set L : Matrix σ σ C := Matrix.of fun k c : σ => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)
    with hLdef
  have hdet : IsUnit L.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at hL
    simp at hL
  set N : Matrix σ σ C := L⁻¹ with hNdef
  have hLN : L * N = 1 := Matrix.mul_nonsing_inv L hdet
  have hNL : N * L = 1 := Matrix.nonsing_inv_mul L hdet

  have comb : ∀ {M : Type} [AddCommGroup M] [Module C M] (A B : Matrix σ σ C), A * B = 1 →
      ∀ (X : σ → M) (i : σ), ∑ j, A i j • ∑ k, B j k • X k = X i := by
    intro M _ _ A B hAB X i
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hrow : ∀ k, ∑ j, A i j * B j k = (1 : Matrix σ σ C) i k := fun k => by
      rw [← hAB, Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hcoeff : ∀ (ψ : σ → MvPowerSeries σ C) j μ,
      MvPowerSeries.coeff μ (∑ k, N j k • ψ k) = ∑ k, N j k * MvPowerSeries.coeff μ (ψ k) := by
    intro ψ j μ
    simp only [map_sum, MvPowerSeries.coeff_smul]
  have hcc : ∀ (ψ : σ → MvPowerSeries σ C), (∀ k, MvPowerSeries.constantCoeff (ψ k) = 0) →
      ∀ j, MvPowerSeries.constantCoeff (∑ k, N j k • ψ k) = 0 := by
    intro ψ hψ j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ]

  have hid : Formalism.FG.IsIdMod2 (fun j => ∑ k, N j k • φ k) := by
    refine ⟨hcc φ hφ0, fun j i => ?_⟩
    show MvPowerSeries.coeff (Finsupp.single i 1) (∑ k, N j k • φ k) = _
    rw [hcoeff]
    have hNLji : ∑ k, N j k * MvPowerSeries.coeff (Finsupp.single i 1) (φ k) = (N * L) j i := by
      rw [Matrix.mul_apply]
      rfl
    rw [hNLji, hNL, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij]
  obtain ⟨h, hh0, hhs⟩ := Formalism.FG.solve_exists_vector C σ σ (fun j => ∑ k, N j k • φ k)
    (fun j => ∑ k, N j k • φ₂ k) hid (hcc φ₂ hφ0₂)
  have hsub_h : MvPowerSeries.HasSubst h := MvPowerSeries.hasSubst_of_constantCoeff_zero hh0
  have hlin : ∀ (a : σ → MvPowerSeries σ C), MvPowerSeries.HasSubst a → ∀ j,
      MvPowerSeries.subst a (∑ k, N j k • φ k) = ∑ k, N j k • MvPowerSeries.subst a (φ k) := by
    intro a ha j
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum, MvPowerSeries.coe_substAlgHom ha]
    exact Finset.sum_congr rfl fun k _ => MvPowerSeries.subst_smul ha _ _

  have hφh : ∀ k, MvPowerSeries.subst h (φ k) = φ₂ k := by
    have h1 : ∀ j, ∑ k, N j k • MvPowerSeries.subst h (φ k) = ∑ k, N j k • φ₂ k := by
      intro j
      rw [← hlin h hsub_h]
      exact hhs j
    intro i
    have e1 := comb L N hLN (fun k => MvPowerSeries.subst h (φ k)) i
    have e2 := comb L N hLN φ₂ i
    simp only [h1] at e1
    exact e1.symm.trans e2
  have hhI : ∀ c, IntS V (h c) := by
    have hint := AltInv.intS_invG φ h φ₂ hφ0 (fun k => (intS_iff_alt V _).mp (hφ k)) hL hh0
      (fun k => (intS_iff_alt V _).mp (hφ₂ k)) hφh
    exact fun c => (intS_iff_alt V _).mpr (hint c)

  have hsub_t : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have hsub_t₂ : MvPowerSeries.HasSubst t₂ := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0₂
  set t' : σ → MvPowerSeries σ C := fun c => MvPowerSeries.subst t₂ (h c) with ht'
  have hL1t : ∀ i, Formalism.FG.SolveVAux.Low 1 (t i) :=
    fun i => (Formalism.FG.SolveVAux.low_one_iff _).mpr (ht0 i)
  have hL1t' : ∀ i, Formalism.FG.SolveVAux.Low 1 (t' i) := fun i =>
    Formalism.FG.SolveVAux.low_subst (fun j => (Formalism.FG.SolveVAux.low_one_iff _).mpr (ht0₂ j))
      ((Formalism.FG.SolveVAux.low_one_iff _).mpr (hh0 i))
  have hsub_t' : MvPowerSeries.HasSubst t' :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (Formalism.FG.SolveVAux.low_one_iff _).mp (hL1t' i)
  have hφt : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t' (φ k) := by
    intro k
    rw [heq k, ← hφh k]
    exact MvPowerSeries.subst_comp_subst_apply hsub_h hsub_t₂ (φ k)
  have hg2 : ∀ j, Formalism.FG.SolveVAux.Low 2 ((∑ k, N j k • φ k) - MvPowerSeries.X j) := by
    intro j
    unfold Formalism.FG.SolveVAux.Low
    intro d hd
    rw [map_sub]
    rcases (by omega : d.degree = 0 ∨ d.degree = 1) with hd0 | hd1
    · have hd00 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst hd00
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0]
    · obtain ⟨i, rfl⟩ := Formalism.FG.SolveVAux.degree_eq_one d hd1
      rw [show MvPowerSeries.coeff (Finsupp.single i 1) (∑ k, N j k • φ k) =
        if i = j then 1 else 0 from hid.2 j i, MvPowerSeries.coeff_X]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg]
        · simp
        · intro h'
          exact hij (Finsupp.single_left_injective one_ne_zero h')
  have hlow : ∀ (M : ℕ) (i : σ), Formalism.FG.SolveVAux.Low M (t i - t' i) := by
    intro M
    induction M with
    | zero => exact fun i => Formalism.FG.SolveVAux.low_zero _
    | succ M ih =>
      intro i
      have hsplit : ∀ a : σ → MvPowerSeries σ C, MvPowerSeries.HasSubst a →
          MvPowerSeries.subst a (∑ k, N i k • φ k) =
            a i + MvPowerSeries.subst a ((∑ k, N i k • φ k) - MvPowerSeries.X i) := by
        intro a ha
        rw [MvPowerSeries.subst_sub ha, MvPowerSeries.subst_X ha]
        abel
      have hfeq : MvPowerSeries.subst t (∑ k, N i k • φ k) =
          MvPowerSeries.subst t' (∑ k, N i k • φ k) := by
        rw [hlin t hsub_t, hlin t' hsub_t']
        simp only [hφt]
      have h1 := hsplit t hsub_t
      have h2 := hsplit t' hsub_t'
      rw [hfeq] at h1
      have hdiff : t i - t' i =
          -(MvPowerSeries.subst t ((∑ k, N i k • φ k) - MvPowerSeries.X i) -
            MvPowerSeries.subst t' ((∑ k, N i k • φ k) - MvPowerSeries.X i)) := by
        linear_combination h2 - h1
      rw [hdiff]
      exact Formalism.FG.SolveVAux.low_neg (Formalism.FG.SolveVAux.low_subst_sub hL1t hL1t' ih (hg2 i))
  have htt : t = t' := by
    funext i
    ext d
    have hd := hlow (d.degree + 1) i d (Nat.lt_succ_self _)
    rw [map_sub] at hd
    exact sub_eq_zero.mp hd
  exact ⟨h, hh0, hhI, fun c => congrFun htt c⟩

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem upG_subst {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) (g : Fin 2) (γ : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) (upG g γ) = upG g (MvPowerSeries.subst (t g) γ) := by
  have hX : MvPowerSeries.HasSubst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  have hT : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by
      unfold upG
      rw [cc_subst_lemma _ (fun x => by simp)]
      exact ht0 w.1 w.2)
  have ht : MvPowerSeries.HasSubst (t g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (ht0 g)
  have e1 : upG g γ = MvPowerSeries.subst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) γ := rfl
  have e2 : upG g (MvPowerSeries.subst (t g) γ) = MvPowerSeries.subst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) (MvPowerSeries.subst (t g) γ) := rfl
  rw [e1, e2, MvPowerSeries.subst_comp_subst_apply hX hT, MvPowerSeries.subst_comp_subst_apply ht hX]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hT]
  try rfl

theorem germ_sub {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t t₂ h : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0₂ : ∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0)
    (hh0 : ∀ g c, MvPowerSeries.constantCoeff (h g c) = 0) (hhI : ∀ g c, IntS V (h g c))
    (hth : ∀ g c, t g c = MvPowerSeries.subst (t₂ g) (h g c)) :
    IntGerm V t ⊆ IntGerm V t₂ := by
  rintro F ⟨γ, hγ, rfl⟩
  have hX : ∀ (g : Fin 2) (x : I g),
      AltInv.IntS V.v (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C) := fun g x => by
    intro μ
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact AltInv.intC_one (v := V.v)
    · exact AltInv.intC_zero (v := V.v)
  have hH0 : ∀ w : WV I, MvPowerSeries.constantCoeff (upG w.1 (h w.1 w.2)) = 0 := fun w => by
    unfold upG
    rw [cc_subst_lemma _ (fun x => by simp)]
    exact hh0 w.1 w.2
  have hHI : ∀ w : WV I, IntS V (upG w.1 (h w.1 w.2)) := fun w => by
    rw [intS_iff_alt]
    exact AltInv.intS_subst (v := V.v) (fun x => by simp) (fun x => hX w.1 x)
      ((intS_iff_alt V _).mp (hhI w.1 w.2))
  have hH : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (h w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hH0
  have hT₂ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t₂ w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by
      unfold upG
      rw [cc_subst_lemma _ (fun x => by simp)]
      exact ht0₂ w.1 w.2)
  refine ⟨MvPowerSeries.subst (fun w : WV I => upG w.1 (h w.1 w.2)) γ, ?_, ?_⟩
  · exact AltInv.intS_subst (v := V.v) hH0 (fun w => (intS_iff_alt V _).mp (hHI w)) ((intS_iff_alt V γ).mp hγ)
  · rw [MvPowerSeries.subst_comp_subst_apply hH hT₂]
    congr 1
    funext w
    rw [upG_subst t₂ ht0₂, ← hth]

theorem abstract_germ_zero : AbstractGermZeroCondition V := by
  intro I _ t t₂ φ φ₂ ht0 ht0₂ hφ0 hφ hL hφ0₂ hφ₂ hL₂ heq
  choose h hh0 hhI hth using fun g => one_group V (t g) (t₂ g) (φ g) (φ₂ g) (ht0₂ g) (ht0 g) (hφ0 g) (hφ g)
    (hL g) (hφ0₂ g) (hφ₂ g) (heq g)
  choose h' hh0' hhI' hth' using fun g => one_group V (t₂ g) (t g) (φ₂ g) (φ g) (ht0 g) (ht0₂ g) (hφ0₂ g)
    (hφ₂ g) (hL₂ g) (hφ0 g) (hφ g) (fun k => (heq g k).symm)
  exact Set.Subset.antisymm (germ_sub V t t₂ h ht0₂ hh0 hhI hth) (germ_sub V t₂ t h' ht0 hh0' hhI' hth')

end AbstractGermZero
end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace FormalGermZero

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

private theorem deg_single_lemma_0 {τ : Type} (c : τ) (n : ℕ) : Finsupp.degree (Finsupp.single c n) = n := by
  first
  | exact Finsupp.degree_single c n
  | simp [Finsupp.degree_single]
  | simp [Finsupp.degree]
  | (classical
     unfold Finsupp.degree
     by_cases h : n = 0 <;> simp [h])

private theorem deg_zero_lemma_0 {τ : Type} (d : τ →₀ ℕ) (h : Finsupp.degree d = 0) : d = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff d).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h
  | simpa using h

private theorem cs_mul_lemma {τ : Type} (A B : MvPowerSeries τ C) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (A * B) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add, deg_single_lemma_0] at hdeg
  rcases Nat.eq_zero_or_pos p.1.degree with h0 | h0
  · rw [deg_zero_lemma_0 p.1 h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
  · have h1 : p.2.degree = 0 := by omega
    rw [deg_zero_lemma_0 p.2 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]

private theorem cs_prod_lemma_2 {σ τ : Type} (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : σ →₀ ℕ) (he : e ≠ 0) :
    MvPowerSeries.constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (Finsupp.ext h)
  rw [map_finsuppProd]
  simp only [map_pow, ha0, Finsupp.prod]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)

private theorem cs_prod_lemma_3 {σ τ : Type} (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : σ →₀ ℕ) (he : 2 ≤ e.degree) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (e.prod fun s n => a s ^ n) = 0 := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finsupp.ext h)
  have hle : Finsupp.single s 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    omega
  have hsplit : e = Finsupp.single s 1 + (e - Finsupp.single s 1) := (add_tsub_cancel_of_le hle).symm
  have hdeg : 1 ≤ (e - Finsupp.single s 1).degree := by
    have h2 := congrArg Finsupp.degree hsplit
    rw [map_add, deg_single_lemma_0] at h2
    omega
  have hne' : e - Finsupp.single s 1 ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  rw [hsplit, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _), pow_one]
  exact cs_mul_lemma _ _ (ha0 s) (cs_prod_lemma_2 a ha0 _ hne') c

theorem coeff_single_subst_of_low_degree {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (r : MvPowerSeries σ C)
    (hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e r = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a r) = 0 := by
  classical
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < 2
  · rw [hr e he, zero_smul]
  · rw [cs_prod_lemma_3 a ha0 e (by omega) c, smul_zero]

theorem coeff_single_subst_lin {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : σ)
    (hf : ∀ μ : σ →₀ ℕ, μ.degree ≤ 1 → MvPowerSeries.coeff μ f = MvPowerSeries.coeff μ (MvPowerSeries.X i))
    (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a f) =
      MvPowerSeries.coeff (Finsupp.single c 1) (a i) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e (f - MvPowerSeries.X i) = 0 := by
    intro e he
    rw [map_sub, hf e (by omega), sub_self]
  have hsplit : f = MvPowerSeries.X i + (f - MvPowerSeries.X i) := by ring
  rw [hsplit, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, map_add,
    coeff_single_subst_of_low_degree a ha0 _ hr c, add_zero]

theorem subst_zero_of_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (0 : σ → MvPowerSeries τ C) f = 0 := by
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)), map_zero]
  rw [finsum_eq_single _ 0]
  · simp [hf]
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    simp only [Pi.zero_apply, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)]
    simp

theorem intS_X {V : VF C} {τ : Type} (c : τ) : IntS V (MvPowerSeries.X c : MvPowerSeries τ C) := by
  rw [AbstractGermZero.intS_iff_alt]
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact AltInv.intC_one (v := V.v)
  · exact AltInv.intC_zero (v := V.v)

private theorem prod_X_lemma_8 {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]

theorem coeff_single_substX_tyS {τ : Type} {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (c c'' : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1)
        (PowerSeries.subst (MvPowerSeries.X c'' : MvPowerSeries τ C) (tyS l a)) =
      if c'' = c then a 0 else 0 := by
  classical
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hcoef : MvPowerSeries.coeff (Finsupp.single () 1) (tyS l a) = a 0 := by
    have hl1 : l ≠ 1 := by omega
    unfold tyS
    first
    | (rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff (R := C) 1 from rfl,
        PowerSeries.coeff_mk]
       simp [Finset.sum_range_succ, hl1])
    | (rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff C 1 from rfl,
        PowerSeries.coeff_mk]
       simp [Finset.sum_range_succ, hl1])
    | (show (∑ s ∈ Finset.range (1 + 1), if l ^ s = 1 then a s else 0) = a 0
       simp [Finset.sum_range_succ, hl1])
  show MvPowerSeries.coeff (Finsupp.single c 1)
      (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) (tyS l a)) = _
  rw [MvPowerSeries.coeff_subst ha]
  simp only [prod_X_lemma_8 (fun _ : Unit => c''), MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [finsum_eq_single _ (Finsupp.single () 1)]
  · rw [Finsupp.mapDomain_single]
    by_cases h : c'' = c
    · subst h
      rw [if_pos rfl, if_pos rfl, hcoef]
    · rw [if_neg (fun h' => h ((Finsupp.single_left_injective one_ne_zero h').symm)), if_neg h]
  · intro d hd
    rw [if_neg]
    intro h'
    apply hd
    rw [Finsupp.unique_single d, Finsupp.mapDomain_single] at h'
    rw [Finsupp.unique_single d]
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h' with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [← h2]
    · exact absurd h1 one_ne_zero

theorem isT_sum {V : VF C} {d : ℕ} {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {X₁ : Cart V d I₁ J₁} (S : Sys X₁)
    {t : I₁ → MvPowerSeries I₁ C} (ht : S.IsT t) (x : I₁) :
    ∑ c, PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x)) = MvPowerSeries.X x := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  ext μ
  have key : ∀ c, MvPowerSeries.coeff μ (PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x))) =
      ∑ s ∈ Finset.range (μ.degree + 1), S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s)) := by
    intro c
    have hS : PowerSeries.HasSubst (t c) := PowerSeries.HasSubst.of_constantCoeff_zero (ht.1 c)
    have hlow : ∀ n, μ.degree < n → MvPowerSeries.coeff μ (t c ^ n) = 0 := fun n hn =>
      Formalism.FG.SolveVAux.low_pow ((Formalism.FG.SolveVAux.low_one_iff _).2 (ht.1 c)) n μ hn
    rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
    · have e1 : ∀ n ∈ Finset.range (μ.degree + 1),
          PowerSeries.coeff n (tyS V.l fun s => S.al c s x) • MvPowerSeries.coeff μ (t c ^ n) =
            ∑ s ∈ Finset.range (μ.degree + 1),
              if V.l ^ s = n then S.al c s x * MvPowerSeries.coeff μ (t c ^ n) else 0 := by
        intro n hn
        rw [Finset.mem_range] at hn
        unfold tyS
        rw [PowerSeries.coeff_mk, smul_eq_mul, Finset.sum_mul]
        simp only [ite_mul, zero_mul]
        apply Finset.sum_subset
        · intro s hs
          rw [Finset.mem_range] at hs ⊢
          omega
        · intro s _ hs
          rw [Finset.mem_range] at hs
          have : s < V.l ^ s := Nat.lt_pow_self (by omega)
          rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [Finset.mem_range] at h
        rw [hlow _ (by omega), mul_zero]
    · intro n hn
      rw [Function.mem_support] at hn
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact hn (by rw [hlow n (by omega), smul_zero])
  rw [map_sum]
  simp only [key]
  rw [Finset.sum_comm, MvPowerSeries.coeff_X]
  exact ht.2 x μ

section Law

variable {dd : ℕ}

def addS {σ : Type} (F : Fin dd → PS C 2 dd) (a b : Fin dd → MvPowerSeries σ C) : Fin dd → MvPowerSeries σ C :=
  fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2) (F j)

def gsum {σ ι : Type} (F : Fin dd → PS C 2 dd) (Γ : ι → Fin dd → MvPowerSeries σ C) :
    List ι → Fin dd → MvPowerSeries σ C
  | [] => 0
  | c :: l => addS F (Γ c) (gsum F Γ l)

theorem pair_const {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

theorem pair_int {V : VF C} {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × Fin dd, IntS V (![a, b] q.1 q.2) := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

private theorem prod_X_lemma {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]

private theorem un1_lift_lemma_2 (f : MvPowerSeries (Fin 1 × Fin dd) C) :
    MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      (un1 f) = f := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  have hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ := by
    rw [← Finsupp.mapDomain_comp]
    have hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id := by
      funext p
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hc, Finsupp.mapDomain_id]
  rw [finsum_eq_single _ (μ.mapDomain Prod.snd)]
  · rw [if_pos hμ.symm, smul_eq_mul, mul_one]
    show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _
    rw [show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h
    apply hd
    rw [h, ← Finsupp.mapDomain_comp,
      show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]

private theorem ev1_lemma_3 {n : ℕ} (Q : Pt C n dd) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : PS C 1 dd) : ev ![Q] f = MvPowerSeries.subst Q (un1 f) := by
  have hA : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨a, i⟩
      fin_cases a
      exact hQ i)
  unfold ev
  conv_lhs => rw [← un1_lift_lemma_2 f]
  rw [MvPowerSeries.subst_comp_subst_apply hA hB]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hB]
  rfl

theorem lg_addS {σ : Type} (Y : FBChart C V O dd) (a b : Fin dd → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (addS Y.B.G.F a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by
  have hpt : ∀ k : Fin 2, ∀ i, MvPowerSeries.constantCoeff (pt C dd k i) = 0 := fun k i => by simp [pt]
  have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C dd 0) (pt C dd 1) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i)) = 0
    unfold ev
    rw [cc_subst_lemma _ (fun p => by
      rcases p with ⟨a, k⟩
      fin_cases a <;> simp [pt])]
    exact Y.B.G.const i
  have hF' : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext i
    show ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i) = Y.B.G.F i
    have hX : (fun p : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) p.1 p.2) =
        MvPowerSeries.X := by
      funext p
      rcases p with ⟨a, k⟩
      fin_cases a <;> rfl
    unfold ev
    rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
    simp
  have hfb := Y.lg_add i
  rw [ev1_lemma_3 _ hadd, ev1_lemma_3 _ (hpt 0), ev1_lemma_3 _ (hpt 1), hF'] at hfb
  have hP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (pair_const ha hb)
  have hF : MvPowerSeries.HasSubst Y.B.G.F := MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const
  have hX0 : MvPowerSeries.HasSubst (pt C dd (0 : Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 0)
  have hX1 : MvPowerSeries.HasSubst (pt C dd (1 : Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 1)
  have e := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2)) hfb
  rw [MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP,
    MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP] at e
  simp only [pt, MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
  exact e

theorem gsum_const {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsum Y.B.G.F Γ l j) = 0
  | [], j => by
    show MvPowerSeries.constantCoeff ((0 : Fin dd → MvPowerSeries σ C) j) = 0
    simp
  | c :: l, j => constantCoeff_subst_zero (pair_const (hΓ c) (gsum_const Y Γ hΓ l)) (Y.B.G.const j)

theorem gsum_int {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsum Y.B.G.F Γ l j)
  | [], j => by
    intro μ
    show V.Ge 0 (MvPowerSeries.coeff μ ((0 : Fin dd → MvPowerSeries σ C) j))
    rw [Pi.zero_apply, map_zero]
    exact VF.Ge.zero 0
  | c :: l, j => IntS.subst (pair_const (hΓ0 c) (gsum_const Y Γ hΓ0 l))
      (pair_int (hΓ c) (gsum_int Y Γ hΓ0 hΓ l)) (Y.intF j)

theorem gsum_lg {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : Fin dd) :
    ∀ l : List ι, MvPowerSeries.subst (gsum Y.B.G.F Γ l) (un1 (Y.lg i)) =
      (l.map fun c => MvPowerSeries.subst (Γ c) (un1 (Y.lg i))).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    exact subst_zero_of_const _ (by rw [constantCoeff_uncurry, Y.lg_const])
  | c :: l => by
    rw [List.map_cons, List.sum_cons, ← gsum_lg Y Γ hΓ i l]
    exact lg_addS Y (Γ c) (gsum Y.B.G.F Γ l) (hΓ c) (gsum_const Y Γ hΓ l) i

end Law

section Sys1

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]

theorem sys_curve (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) (c : I g) :
    ∃ γ : Fin dd → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (un1 (Y.lg i)) =
      ∑ c' : I g, p.u g c' i • tyS V.l (fun s => S.al c s c') := by
  have hm : S.cur c ∈ (Y.raw p).TySet V g := (S.curve c).1
  obtain ⟨γ, lam, hγ, -, hlog, -⟩ := hm
  exact ⟨γ, hγ, hlog⟩

theorem sys_P (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) :
    ∃ P : Fin dd → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', p.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C))
            ((Y.raw p).ex j) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  choose γ hγ hlog using fun c => sys_curve Y p hg S c
  have hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0 := fun c j => (hγ c j).1
  have hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) :=
    fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c
  set Γ : I g → Fin dd → MvPowerSeries (I g) C :=
    fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef
  have hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0 := fun c j =>
    constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)
  have hΓI : ∀ c j, IntS V (Γ c j) := fun c j =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)

  have hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) =
      ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c')) := by
    intro c i
    have e1 : MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) =
        PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (un1 (Y.lg i))) := by
      show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _
      rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]
      rfl
    rw [e1, hlog c i, ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]
    simp only [map_smul]
  set P : Fin dd → MvPowerSeries (I g) C := gsum Y.B.G.F Γ Finset.univ.toList with hPdef
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := gsum_const Y Γ hΓ0 _
  have hPlg : ∀ i, MvPowerSeries.subst P (un1 (Y.lg i)) =
      ∑ c, ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C)
        (tyS V.l (fun s => S.al c s c')) := by
    intro i
    rw [gsum_lg Y Γ hΓ0 i, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun c _ => hΓlg c i
  refine ⟨P, hP0, gsum_int Y Γ hΓ0 hΓI _, ?_, ?_⟩
  ·
    intro j c
    have hlin := coeff_single_subst_lin P hP0 (un1 (Y.lg j)) j (Y.raw_lin p j) c
    rw [← hlin, hPlg j, map_sum]
    simp only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    exact congrFun (S.curve c).2.1 (Sum.inl c')
  ·
    intro t ht j
    have ht0 := ht.1
    have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
    set Q : Fin dd → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ
    have hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := fun j => constantCoeff_subst_zero ht0 (hP0 j)
    have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    have hQlg : ∀ i, MvPowerSeries.subst Q (un1 (Y.lg i)) =
        ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
      intro i
      have e1 : MvPowerSeries.subst Q (un1 (Y.lg i)) = MvPowerSeries.subst t (MvPowerSeries.subst P (un1 (Y.lg i))) := by
        rw [MvPowerSeries.subst_comp_subst_apply hPS hts]
      have e2 : ∀ c (A : PowerSeries C), MvPowerSeries.subst t
          (PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) A) = PowerSeries.subst (t c) A := by
        intro c A
        show MvPowerSeries.subst t (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) A) =
          MvPowerSeries.subst (fun _ : Unit => t c) A
        rw [MvPowerSeries.subst_comp_subst_apply (hXc c) hts]
        congr 1
        funext u
        rw [MvPowerSeries.subst_X hts]
      rw [e1, hPlg i, ← MvPowerSeries.coe_substAlgHom hts, map_sum]
      simp only [map_sum, map_smul, MvPowerSeries.coe_substAlgHom hts, e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.smul_sum, isT_sum S ht c']
    have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero (Y.chart_log_constantCoeff p)
    have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    have h := congrArg (MvPowerSeries.subst Q) (Y.raw_exlg p j)
    rw [MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS] at h
    show Q j = _
    rw [← h]
    congr 1
    funext i
    exact hQlg i

end Sys1


end FormalGermZero

end Formalism.L2.FormalSeriesBounds
end
end
