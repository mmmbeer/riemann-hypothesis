import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq

section
namespace GlobalTheory.PowerSeriesCoeffSum

open MvPowerSeries Finsupp

variable {O : Type} [CommRing O] {a : ℕ}

noncomputable def part (f : MvPowerSeries (Fin a) O) (i : Fin a) : MvPowerSeries (Fin a) O :=
  fun e => if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0

lemma coeff_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := rfl

lemma coeff_X_mul_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if (1 ≤ m i ∧ ∀ j < i, m j = 0) then coeff m f else 0 := by
  rw [X, coeff_monomial_mul, one_mul]
  by_cases h1 : 1 ≤ m i
  · have hle : single i 1 ≤ m := by
      intro k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simp [single_apply, Ne.symm hk]
    rw [if_pos hle, coeff_part, tsub_add_cancel_of_le hle]
    have : (∀ j < i, (m - single i 1 : Fin a →₀ ℕ) j = 0) ↔ (∀ j < i, m j = 0) := by
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      have : j ≠ i := ne_of_lt hj
      simp [single_apply, Ne.symm this]
    simp only [this, h1, true_and]
  · have hle : ¬ single i 1 ≤ m := by
      intro h; exact h1 (by simpa using h i)
    simp [hle, h1]

lemma eq_sum (f : MvPowerSeries (Fin a) O) (h0 : coeff 0 f = 0) :
    f = ∑ i, X i * part f i := by
  ext m
  rw [map_sum]
  simp only [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm; simp [h0]
  · have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
    set i0 := m.support.min' hne with hi0
    have hi0mem : i0 ∈ m.support := Finset.min'_mem _ _
    have key : ∀ i, (1 ≤ m i ∧ ∀ j < i, m j = 0) ↔ i = i0 := by
      intro i
      constructor
      · rintro ⟨h1, h2⟩
        apply le_antisymm
        · by_contra hlt
          push_neg at hlt
          exact (Finsupp.mem_support_iff.mp hi0mem) (h2 _ hlt)
        · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr (by omega))
      · rintro rfl
        refine ⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0mem), fun j hj => ?_⟩
        by_contra hj0
        exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
    simp only [key]
    simp

theorem main : ∀ (O : Type) [inst : CommRing O] (a n : ℕ) (f : MvPowerSeries (Fin a) O),
    (∀ (m : Fin a →₀ ℕ), (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m < n →
      (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f = (0 : O)) →
    f ∈ Ideal.span (Set.range MvPowerSeries.X) ^ n := by
  intro O _ a n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have h0 : coeff 0 f = 0 := hf 0 (by simp)
    rw [eq_sum f h0, pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ ?_)
    intro e he
    rw [coeff_part]
    split_ifs
    · apply hf
      rw [map_add, degree_single]; omega
    · rfl

end GlobalTheory.PowerSeriesCoeffSum
end

section
namespace GlobalTheory.PowerSeriesMaximalBound
open MvPowerSeries

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

lemma C_mem_max {r : O} (hr : r ∈ IsLocalRing.maximalIdeal O) :
    (C r : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_C]
  exact hr

lemma X_mem_max (i : Fin a) :
    (X i : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

lemma map_le_max :
    Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  exact C_mem_max hr

lemma monomial_one_mem (v : Fin a →₀ ℕ) :
    (monomial v (1 : O)) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ (Finsupp.degree v) := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add i k w hi hk ih =>
    rw [← one_mul (1 : O), ← monomial_mul_monomial, map_add, Finsupp.degree_single, pow_add, ← X_pow_eq]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (X_mem_max i) k) ih

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a N : ℕ} (v : Fin a →₀ ℕ) {c : O}, c ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) v) → (MvPowerSeries.monomial v : O → MvPowerSeries (Fin a) O) c ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by
  intro O _ _ a N v c hc
  have h1 : (C c : MvPowerSeries (Fin a) O) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ (N - Finsupp.degree v) := by
    have : (C c : MvPowerSeries (Fin a) O) ∈
        Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O ^ (N - Finsupp.degree v)) :=
      Ideal.mem_map_of_mem _ hc
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono map_le_max _ this
  have h2 : monomial v c = C c * monomial v (1 : O) := by
    rw [← monomial_zero_eq_C, monomial_mul_monomial, zero_add, mul_one]
  rw [h2]
  refine Ideal.pow_le_pow_right (by omega : N ≤ (N - Finsupp.degree v) + Finsupp.degree v) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul h1 (monomial_one_mem v)

end GlobalTheory.PowerSeriesMaximalBound
end

section
namespace GlobalTheory.MaximalIdealFiltration

open MvPowerSeries

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

def filt (N : ℕ) : Ideal (MvPowerSeries (Fin a) O) where
  carrier := {f | ∀ m : Fin a →₀ ℕ, coeff m f ∈ IsLocalRing.maximalIdeal O ^ (N - m.degree)}
  add_mem' := by
    intro f g hf hg m
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' := by
    intro m
    simp
  smul_mem' := by
    intro c f hf m
    simp only [Set.mem_setOf_eq, smul_eq_mul, coeff_mul] at *
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine Ideal.mul_mem_left _ _ ?_
    refine Ideal.pow_le_pow_right ?_ (hf p.2)
    have : p.2.degree ≤ m.degree := by
      rw [← hp, map_add]; omega
    omega

theorem mul_mem_filt {k l : ℕ} {f g : MvPowerSeries (Fin a) O}
    (hf : f ∈ filt (O := O) k) (hg : g ∈ filt (O := O) l) : f * g ∈ filt (O := O) (k + l) := by
  intro m
  simp only [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 := hf p.1
  have h2 := hg p.2
  have hm := Ideal.mul_mem_mul h1 h2
  rw [← pow_add] at hm
  refine Ideal.pow_le_pow_right ?_ hm
  have : m.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
  omega

theorem maximalIdeal_le_filt_one :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ≤ filt (O := O) 1 := by
  intro f hf m
  by_cases h0 : m = 0
  · subst h0
    simp only [map_zero, Nat.sub_zero, pow_one]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf ⊢
    intro hu
    apply hf
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hu
  · have : 1 ≤ m.degree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h
      exact h0 ((Finsupp.degree_eq_zero_iff m).1 h)
    have : 1 - m.degree = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem maximalIdeal_pow_le_filt (N : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ≤ filt (O := O) N := by
  induction N with
  | zero =>
    intro f _ m
    simp
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs
    exact mul_mem_filt (ih hr) (maximalIdeal_le_filt_one hs)

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ), ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N, ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by
  intro O _ _ a N f hf m
  exact maximalIdeal_pow_le_filt N hf m

end GlobalTheory.MaximalIdealFiltration
end

section
open MvPowerSeries

namespace GlobalTheory.FiltrationMultiplicative

section

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ↔
      coeff 0 f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff, coeff_zero_eq_constantCoeff_apply]

variable (O) in

def Filt (σ : Type) (N : ℕ) : Set (MvPowerSeries σ O) :=
  {f | ∀ m : σ →₀ ℕ, coeff m f ∈ IsLocalRing.maximalIdeal O ^ (N - Finsupp.degree m)}

theorem filt_mul {σ : Type} {a b : ℕ} {f g : MvPowerSeries σ O}
    (hf : f ∈ Filt O σ a) (hg : g ∈ Filt O σ b) : f * g ∈ Filt O σ (a + b) := by
  classical
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree m := by
    rw [← map_add, hpm]
  have := Ideal.mul_mem_mul (hf p.1) (hg p.2)
  rw [← pow_add] at this
  exact Ideal.pow_le_pow_right (by omega) this

theorem filt_zero {σ : Type} (f : MvPowerSeries σ O) : f ∈ Filt O σ 0 := by
  intro m
  simp

variable (O) in

def FiltIdeal (σ : Type) (N : ℕ) : Ideal (MvPowerSeries σ O) where
  carrier := Filt O σ N
  add_mem' := by
    intro f g hf hg m
    rw [map_add]
    exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' := by
    intro m
    simp
  smul_mem' := by
    intro c f hf
    have := filt_mul (filt_zero c) hf
    simpa using this

theorem max_le_filt_one {σ : Type} :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ≤ FiltIdeal O σ 1 := by
  intro f hf m
  by_cases h : Finsupp.degree m = 0
  · have hm : m = 0 := (Finsupp.degree_eq_zero_iff m).mp h
    subst hm
    simpa using (mem_max_iff f).mp hf
  · have : 1 - Finsupp.degree m = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem pow_le_filt {σ : Type} (N : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ N ≤ FiltIdeal O σ N := by
  induction N with
  | zero => intro f _; exact filt_zero f
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs
    exact filt_mul (ih hr) (max_le_filt_one hs)

def IsFirst {a : ℕ} (m : Fin a →₀ ℕ) (i : Fin a) : Prop := m i ≠ 0 ∧ ∀ j, j < i → m j = 0

theorem isFirst_unique {a : ℕ} {m : Fin a →₀ ℕ} {i j : Fin a} (hi : IsFirst m i)
    (hj : IsFirst m j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (hj.2 i h) hi.1
  · exact h
  · exact absurd (hi.2 j h) hj.1

theorem isFirst_exists {a : ℕ} {m : Fin a →₀ ℕ} (hm : m ≠ 0) : ∃ i, IsFirst m i := by
  have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
  refine ⟨m.support.min' hne, Finsupp.mem_support_iff.mp (Finset.min'_mem _ _), fun j hj => ?_⟩
  by_contra h
  exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hj)

open Classical in

noncomputable def part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) :
    MvPowerSeries (Fin a) O :=
  fun q => if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0

open Classical in
theorem coeff_part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (q : Fin a →₀ ℕ) :
    coeff q (part f i) =
      if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0 :=
  rfl

open Classical in
theorem coeff_X_mul_part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if IsFirst m i then coeff m f else 0 := by
  rw [X_def, coeff_monomial_mul, one_mul]
  by_cases h : Finsupp.single i 1 ≤ m
  · rw [if_pos h, coeff_part, tsub_add_cancel_of_le h]
  · rw [if_neg h, if_neg]
    intro hf
    apply h
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hf.1

theorem decomp {a : ℕ} (f : MvPowerSeries (Fin a) O) :
    f = C (coeff 0 f) + ∑ i, X i * part f i := by
  classical
  ext m
  rw [map_add, map_sum]
  simp_rw [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm
    simp [IsFirst]
  · obtain ⟨i, hi⟩ := isFirst_exists hm
    rw [Finset.sum_eq_single i, if_pos hi, coeff_C, if_neg hm, zero_add]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (isFirst_unique h hi)
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem part_mem {a N : ℕ} {f : MvPowerSeries (Fin a) O} (hf : f ∈ Filt O (Fin a) (N + 1))
    (i : Fin a) : part f i ∈ Filt O (Fin a) N := by
  classical
  intro q
  rw [coeff_part]
  split_ifs
  · have := hf (q + Finsupp.single i 1)
    rwa [map_add, Finsupp.degree_single,
      show N + 1 - (Finsupp.degree q + 1) = N - Finsupp.degree q by omega] at this
  · exact Ideal.zero_mem _

theorem C_mem_pow {σ : Type} (n : ℕ) {c : O} (hc : c ∈ IsLocalRing.maximalIdeal O ^ n) :
    (C c : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ n := by
  have h1 : Ideal.map (C : O →+* MvPowerSeries σ O) (IsLocalRing.maximalIdeal O) ≤
      IsLocalRing.maximalIdeal (MvPowerSeries σ O) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff, coeff_zero_C]
    exact hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* MvPowerSeries σ O) hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem filt_le_pow {a : ℕ} (N : ℕ) : ∀ f : MvPowerSeries (Fin a) O, f ∈ Filt O (Fin a) N →
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by
  induction N with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    rw [decomp f]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)
    · apply C_mem_pow
      simpa using hf 0
    · rw [pow_succ']
      exact Ideal.mul_mem_mul ((mem_max_iff _).mpr (by simp)) (ih _ (part_mem hf i))

end

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ)
    (f : MvPowerSeries (Fin a) O),
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ↔
      ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈
        IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by
  intro O _ _ a N f
  exact ⟨fun h => pow_le_filt N h, filt_le_pow N f⟩

end GlobalTheory.FiltrationMultiplicative
end

section
namespace GlobalTheory.NoetherianLocalHausdorff

theorem noeth_local_hausdorff : ∀ (B : Type) [inst : CommRing B] [inst_1 : IsLocalRing B] [IsNoetherianRing B],
    IsHausdorff (IsLocalRing.maximalIdeal B) B := by
  intro B _ _ _
  refine ⟨fun x hx => ?_⟩
  have h : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal B) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have := hx n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
    exact this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top] at h
  exact (Submodule.mem_bot B).1 h

end GlobalTheory.NoetherianLocalHausdorff
end

section
namespace GlobalTheory.MaximalIdealMembership

theorem mem_maximalIdeal_iff {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (f : MvPowerSeries (Fin a) O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ↔
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

end GlobalTheory.MaximalIdealMembership
end

section
namespace GlobalTheory.LocalRingBasicFacts

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ}, Ideal.span (Set.range MvPowerSeries.X) ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  intro O _ _ a
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have := h.map (MvPowerSeries.constantCoeff (R := O) (σ := Fin a))
  simp at this

end GlobalTheory.LocalRingBasicFacts
end

section
namespace GlobalTheory.PowerSeriesShift

noncomputable def shift {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => MvPowerSeries.coeff (Finsupp.single i 1 + m) f

noncomputable def free {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => if m i = 0 then MvPowerSeries.coeff m f else (0 : O)

theorem eq_X_mul_shift_add {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) :
    f = MvPowerSeries.X i * shift i f + free i f := by
  classical
  ext m
  rw [map_add, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases h : m i = 0
  · have h1 : ¬ Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_neg h1, zero_add]
    change _ = if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_pos h]
  · have h1 : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_pos h1, one_mul]
    change _ = MvPowerSeries.coeff (Finsupp.single i 1 + (m - Finsupp.single i 1)) f +
      if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_neg h, add_zero, add_tsub_cancel_of_le h1]

theorem main : (let d1 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ (MvPowerSeries.coeff ((fun₀ | i => (1 : ℕ)) + m) : MvPowerSeries σ O → O) f); let d2 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ if (m : σ → ℕ) i = (0 : ℕ) then (MvPowerSeries.coeff m : MvPowerSeries σ O → O) f else (0 : O)); ∀ {σ O : Type} [inst : CommRing O] (i : σ) (f : MvPowerSeries σ O), f = MvPowerSeries.X i * d1 i f + d2 i f) := by
  intro d1 d2 σ O _ i f
  exact eq_X_mul_shift_add i f

end GlobalTheory.PowerSeriesShift
end

section
namespace GlobalTheory.PowerSeriesIdealPowers

open MvPowerSeries IsLocalRing

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

theorem mem_smul_top_iff {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem coeff_mem_of_mem_pow {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by
  classical
  induction n with
  | zero => intro f _ d; simp
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy d
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 := ih x hx p.1
      have h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree) := by
        by_cases h0 : p.2.degree = 0
        · rw [Finsupp.degree_eq_zero_iff] at h0
          rw [h0, coeff_zero_eq_constantCoeff_apply]
          simpa using (mem_max_iff y).1 hy
        · rw [show 1 - p.2.degree = 0 by omega]; simp
      have hdeg : d.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
      have hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree) := by omega
      exact Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)
    · intro x y hx hy d
      rw [map_add]; exact add_mem (hx d) (hy d)

theorem coeff_X_mul_add {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by
  rw [X, coeff_monomial_mul]
  simp

theorem C_mem_pow {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by
  have h1 : C c ∈ Ideal.map (C (σ := σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ n h1
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_max_iff, constantCoeff_C]
  exact hx

theorem X_mem_max {σ : Type} (i : σ) : (X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := by
  rw [mem_max_iff, constantCoeff_X]; exact zero_mem _

theorem mem_pow_of_coeff_mem (a n : ℕ) :
    ∀ f : MvPowerSeries (Fin a) O, (∀ d : Fin a →₀ ℕ, coeff d f ∈ (maximalIdeal O) ^ (n - d.degree)) →
      f ∈ (maximalIdeal (MvPowerSeries (Fin a) O)) ^ n := by
  classical
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    let P : Fin a → (Fin a →₀ ℕ) → Prop := fun i d => d i ≠ 0 ∧ ∀ j < i, d j = 0
    let fi : Fin a → MvPowerSeries (Fin a) O := fun i d => if P i d then coeff d f else 0
    have hfi : ∀ i d, coeff d (fi i) = if P i d then coeff d f else 0 := fun i d => rfl
    have huniq : ∀ i j d, P i d → P j d → i = j := by
      intro i j d hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (hj.2 i h) hi.1
      · exact h
      · exact absurd (hi.2 j h) hj.1
    have hexists : ∀ d : Fin a →₀ ℕ, d ≠ 0 → ∃ i, P i d := by
      intro d hd
      have hs : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hd
      refine ⟨d.support.min' hs, Finsupp.mem_support_iff.1 (Finset.min'_mem _ hs), fun j hj => ?_⟩
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.2 hne)) (not_le.2 hj)
    have hdecomp : f = C (constantCoeff f) + ∑ i, fi i := by
      ext d
      rw [map_add, map_sum, coeff_C]
      simp only [hfi]
      by_cases hd : d = 0
      · subst hd
        have : ∀ i, ¬ P i 0 := fun i h => h.1 rfl
        simp [this, coeff_zero_eq_constantCoeff_apply]
      · obtain ⟨i, hi⟩ := hexists d hd
        rw [if_neg hd, zero_add, Finset.sum_eq_single i (fun j _ hj => by
          rw [if_neg (fun h => hj (huniq _ _ _ h hi))]) (fun h => absurd (Finset.mem_univ i) h),
          if_pos hi]
    rw [hdecomp]
    refine add_mem (C_mem_pow _ _ ?_) (Ideal.sum_mem _ fun i _ => ?_)
    · simpa [coeff_zero_eq_constantCoeff_apply] using hf 0
    · have hdvd : (X i : MvPowerSeries (Fin a) O) ∣ fi i := by
        rw [X_dvd_iff]
        intro m hm
        rw [hfi, if_neg (fun h => h.1 hm)]
      obtain ⟨g, hg⟩ := hdvd
      rw [hg, pow_succ']
      refine Ideal.mul_mem_mul (X_mem_max i) (ih g fun d => ?_)
      rw [← coeff_X_mul_add i g d, ← hg, hfi]
      split_ifs
      · have := hf (d + Finsupp.single i 1)
        rwa [map_add, Finsupp.degree_single, show n + 1 - (d.degree + 1) = n - d.degree by omega] at this
      · exact zero_mem _

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by
  intro O _ _ hO a
  constructor
  intro f hf
  simp only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢
  let s : (Fin a →₀ ℕ) → ℕ → O := fun d k => coeff d (f (k + d.degree))
  have hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro d
    refine IsPrecomplete.prec hO ?_
    intro k l hkl
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have h := coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d
    rwa [map_sub, Nat.add_sub_cancel] at h
  choose L hL using hs
  let Lim : MvPowerSeries (Fin a) O := fun d => L d
  have hLim : ∀ d, coeff d Lim = L d := fun d => rfl
  refine ⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩
  rw [map_sub, hLim]
  by_cases hd : d.degree ≤ n
  · have h := hL d (n - d.degree)
    rw [SModEq.sub_mem, mem_smul_top_iff] at h
    simp only [s, Nat.sub_add_cancel hd] at h
    exact h
  · rw [show n - d.degree = 0 by omega]; simp
end GlobalTheory.PowerSeriesIdealPowers
end

section
namespace GlobalTheory.LocalRingFurtherFacts

theorem main {O : Type} [CommRing O] [IsLocalRing O] {a k : ℕ} {c : O}
    (hc : c ∈ IsLocalRing.maximalIdeal O ^ k) :
    (MvPowerSeries.C : O → MvPowerSeries (Fin a) O) c ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ k := by
  have h1 : Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal x).mp hx
    have := hu.map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O →+* O)
    simpa using this
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

end GlobalTheory.LocalRingFurtherFacts
end

section
noncomputable section

open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1

namespace GlobalTheory.PsCNL

section Division

variable {σ : Type} {O : Type} [CommRing O]

def divX (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O := fun m => coeff (Finsupp.single i 1 + m) f

end Division

section

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f

theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a

end

theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B

theorem psCNL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ),
    ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧
      ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔
        MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := by
  intro O _ _ A n
  refine ⟨inferInstance, ?_, fun x => mem_max_iff x⟩
  exact
    { noeth := inferInstance
      complete :=
        { toIsHausdorff := haus_of_noeth _
          toIsPrecomplete := ps_isPrecomplete n }
      localHom := ⟨fun a ha => by
        rw [MvPowerSeries.algebraMap_apply, isUnit_iff_constantCoeff, constantCoeff_C] at ha
        exact isUnit_of_map_unit _ _ ha⟩
      resSurj := by
        intro y
        obtain ⟨f, rfl⟩ := residue_surjective y
        obtain ⟨a, ha⟩ := IsCNL.resSurj (O := O) (A := A.C) (residue A.C (constantCoeff f))
        have ha' : residue A.C (algebraMap O A.C a) = residue A.C (constantCoeff f) := ha
        refine ⟨a, ?_⟩
        show residue _ (algebraMap O (MvPowerSeries (Fin n) A.C) a) = residue _ f
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
          isUnit_iff_constantCoeff, map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]
        show algebraMap O A.C a - constantCoeff f ∈ maximalIdeal A.C
        rw [← residue_eq_zero_iff, map_sub, ha', sub_self] }

end GlobalTheory.PsCNL

open Formalism.BasicNotions.V1 IsLocalRing in
example : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ), ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧ ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔ MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := GlobalTheory.PsCNL.psCNL
end
end
