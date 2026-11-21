import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormOneOfPair
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho

section
open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem algebraMap_conjO (r : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl

theorem conjO_conjO (r : 𝓞 K) : conjO K (conjO K r) = r :=
  _root_.Formalism.HermitianLattices.Ext.L3.conjO_conjO r

theorem mem_conjIdeal_iff (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ↔ conjO K r ∈ p := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]

theorem conjIdeal_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).IsPrime := by
  rw [conjIdeal_eq_comap]
  exact Ideal.comap_isPrime (conjO K) p

theorem hcompl_eq_closure (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) p = Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  congr 1
  ext s
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 _ (algebraMap_conjO s)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have : t = conjO K s := RingOfIntegers.ext ht
    rwa [this]

theorem mem_hcompl_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (s : 𝓞 K) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ↔ s ∉ p ∧ s ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  rw [hcompl_eq_closure, mem_conjIdeal_iff]
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      have h1 : (1 : 𝓞 K) ∉ p := (Ideal.ne_top_iff_one p).mp hp.ne_top
      exact ⟨h1, by rwa [map_one]⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact (hp.mem_or_mem h).elim ihx.1 ihy.1
      · rw [map_mul] at h
        exact (hp.mem_or_mem h).elim ihx.2 ihy.2
  · intro hs
    exact Submonoid.subset_closure hs

theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  rw [hcompl_eq_closure] at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    apply Submonoid.subset_closure
    exact ⟨hx.2, by rw [conjO_conjO]; exact hx.1⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_mem ihx ihy

theorem algebraMap_ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  have hs0 : s = 0 := RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm)
  exact ((mem_hcompl_iff hp s).mp hs).1 (hs0 ▸ p.zero_mem)

theorem mem_locR_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) :
    a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ↔
      ∃ r : 𝓞 K, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
        a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  constructor
  · rintro ⟨s, hs, h1⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp h1
    refine ⟨r, s, hs, ?_⟩
    rw [eq_div_iff (algebraMap_ne_zero_of_mem_hcompl hp hs), hr, mul_comm]
  · rintro ⟨r, s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [mul_div_cancel₀ _ (algebraMap_ne_zero_of_mem_hcompl hp hs)]
    exact Formalism.HermitianLatticesTheory.locDual_alg_mem r

def locRing (p : Ideal (𝓞 K)) : Subring K where
  carrier := {a | a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p}
  mul_mem' := by
    intro a b ha hb
    change a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at ha
    change b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at hb
    change a * b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha hb ⊢
    obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have e : algebraMap (𝓞 K) K (s * t) * (a * b) =
        (algebraMap (𝓞 K) K s * a) * (algebraMap (𝓞 K) K t * b) := by
      rw [map_mul]; ring
    rw [e]
    exact Formalism.HermitianLatticesTheory.locDual_one_mul h1 h2
  one_mem' := by
    change (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, mul_one]; exact Submodule.one_le.mp le_rfl⟩
  add_mem' := fun ha hb => (Formalism.HermitianLatticesTheory.locR (K := K) p).add_mem ha hb
  zero_mem' := (Formalism.HermitianLatticesTheory.locR (K := K) p).zero_mem
  neg_mem' := fun ha => (Formalism.HermitianLatticesTheory.locR (K := K) p).neg_mem ha

theorem mem_locRing (p : Ideal (𝓞 K)) (a : K) :
    a ∈ locRing p ↔ a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := Iff.rfl

theorem algebraMap_mem_locRing (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    algebraMap (𝓞 K) K r ∈ locRing p := by
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR]
  exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Formalism.HermitianLatticesTheory.locDual_alg_mem r⟩

theorem frac_locRing (p : Ideal (𝓞 K)) (a : K) : ∃ t ∈ locRing p, t ≠ 0 ∧ t * a ∈ locRing p := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
  refine ⟨algebraMap (𝓞 K) K s, algebraMap_mem_locRing p _, ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  · rw [mul_comm]
    change a * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r at hrs
    rw [hrs]
    exact algebraMap_mem_locRing p r

theorem star_mem_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) :
    star a ∈ locRing p := by
  rw [mem_locRing, mem_locR_iff hp] at ha ⊢
  obtain ⟨r, s, hs, rfl⟩ := ha
  refine ⟨conjO K r, conjO K s, conjO_mem_hcompl hs, ?_⟩
  rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

theorem isUnitIn_div_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := fun h => h0 (by rw [h, zero_div])
    rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv
    obtain ⟨u, hu, h1⟩ := hinv
    obtain ⟨v, hv⟩ := Submodule.mem_one.mp h1
    have e : u * s = v * r := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (u * s) = algebraMap (𝓞 K) K (v * r)
      rw [map_mul, map_mul, hv, inv_div]
      field_simp
    have hus := (mem_hcompl_iff hp _).mp (mul_mem hu hs)
    rw [e] at hus
    rw [mem_hcompl_iff hp]
    exact ⟨fun h => hus.1 (p.mul_mem_left v h), fun h => hus.2 (Ideal.mul_mem_left _ v h)⟩
  · intro hr
    have hr0 := algebraMap_ne_zero_of_mem_hcompl hp hr
    refine ⟨div_ne_zero hr0 hs0, ?_, ?_⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨r, s, hs, rfl⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨s, r, hr, inv_div _ _⟩

theorem unram_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ θ ∈ locRing p, IsUnitIn (locRing p) (θ - star θ) := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  refine ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_locRing p θ, ?_⟩
  have hmem : θ - conjO K θ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hp.isPrime, mem_conjIdeal_iff]
    refine ⟨hθ, fun h => hθ ?_⟩
    rw [map_sub, conjO_conjO] at h
    have := p.neg_mem h
    rwa [neg_sub] at this
  have h := (isUnitIn_div_iff hp.isPrime (θ - conjO K θ)
    (one_mem (Formalism.HermitianLatticesTheory.hcompl (K := K) p))).mpr hmem
  rwa [map_one, div_one, map_sub, algebraMap_conjO] at h

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section
open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace BE

theorem exists_gen {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have hIP : ∀ {P' : Ideal R}, P'.IsPrime → ¬ (I ≤ I * P') := by
    intro P' hP' hle
    have e : I * P' = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) hle
    exact hP'.ne_top (mul_left_cancel₀ (by rwa [Ideal.zero_eq_bot]) e)
  have hnot : ¬ ((I : Set R) ⊆ ((I * P : Ideal R) : Set R) ∪ ((I * Q : Ideal R) : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hIP hP h
    · exact hIP hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr.1 (Submodule.zero_mem _)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {r} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrI))
  have hJP : ∀ {P' : Ideal R}, r ∉ I * P' → ¬ (J ≤ P') := by
    intro P' hr' hJ'
    apply hr'
    have hrr : r ∈ Ideal.span {r} := Ideal.mem_span_singleton_self r
    rw [hJ] at hrr
    exact Ideal.mul_mono_right hJ' hrr
  have hnot2 : ¬ ((J : Set R) ⊆ (P : Set R) ∪ (Q : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hJP hr.1 h
    · exact hJP hr.2 h
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.mp hnot2
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hs
  refine ⟨r, hrI, hr0, s, hs.1, hs.2, fun x hx => ?_⟩
  have hmem : s * x ∈ Ideal.span {r} := by
    rw [hJ, mul_comm s x]
    exact Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨y, by rw [← hy, mul_comm]⟩

theorem avoid_two {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := fun c hc => hsP (by
    have := P.add_mem hc (P.mul_mem_left c ha)
    simpa using this)
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have hma : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem hma with h | h
    · exact hm h
    · exact hsQ (by
        have := Q.add_mem h1 (Q.mul_mem_left k h)
        simpa using this)
  · left
    exact ⟨hP _, h1⟩

end BE

theorem principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by
  obtain ⟨t, ht0, ht⟩ := ht
  have hpp := hp.isPrime
  let I : Ideal (𝓞 K) :=
    { carrier := {r | algebraMap (𝓞 K) K r * t⁻¹ ∈ A}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_add, add_mul] at *
        exact A.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_assoc] at *
        exact hA _ (algebraMap_mem_locRing p c) _ hx }
  have hmemI : ∀ r : 𝓞 K, r ∈ I ↔ algebraMap (𝓞 K) K r * t⁻¹ ∈ A := fun r => Iff.rfl

  have hrep : ∀ a ∈ A, ∃ x ∈ I, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K x / (algebraMap (𝓞 K) K s * t) := by
    intro a ha
    obtain ⟨x, s, hs, hx⟩ := (mem_locR_iff hpp _).1 ((mem_locRing p _).1 (ht a ha))
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
    have e : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s * (t * a) := by
      rw [hx]; field_simp
    refine ⟨x, ?_, s, hs, ?_⟩
    · rw [hmemI, e]
      have : algebraMap (𝓞 K) K s * (t * a) * t⁻¹ = algebraMap (𝓞 K) K s * a := by field_simp
      rw [this]
      exact hA _ (algebraMap_mem_locRing p s) _ ha
    · rw [e]; field_simp
  have hI : I ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := h0
    obtain ⟨x, hx, s, hs, e⟩ := hrep a ha
    intro hbot
    rw [hbot, Ideal.mem_bot] at hx
    apply ha0
    rw [e, hx]; simp
  obtain ⟨r, hrI, hr0, s, hsP, hsQ, hgen⟩ := BE.exists_gen hI hpp (conjIdeal_isPrime hpp)
  have hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (mem_hcompl_iff hpp s).2 ⟨hsP, hsQ⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
  have hr0' : algebraMap (𝓞 K) K r ≠ 0 := by
    intro h
    exact hr0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h)
  refine ⟨algebraMap (𝓞 K) K r * t⁻¹, (hmemI r).1 hrI, mul_ne_zero hr0' (inv_ne_zero ht0), ?_⟩
  intro a ha
  obtain ⟨x, hx, s', hs', e⟩ := hrep a ha
  have hs0' := algebraMap_ne_zero_of_mem_hcompl hpp hs'
  obtain ⟨y, hy⟩ := hgen x hx
  have hy' : algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K x
      = algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K y := by
    rw [← map_mul, ← map_mul, hy]
  rw [mem_locRing, mem_locR_iff hpp]
  refine ⟨y, s * s', mul_mem hs hs', ?_⟩
  rw [e, map_mul]
  field_simp
  linear_combination hy'

theorem unit_or_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) (ha : a ∈ locRing p)
    (κ : K) (hκ : κ ∈ locRing p) (μ : K) (hna : a⁻¹ ∉ locRing p) (hμ : IsUnitIn (locRing p) μ) :
    IsUnitIn (locRing p) (1 - κ * a) ∨ IsUnitIn (locRing p) (1 - (κ + μ) * a) := by
  obtain ⟨a₁, s₁, hs₁, ea⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 ha)
  obtain ⟨k₁, s₂, hs₂, ek⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hκ)
  obtain ⟨m₁, s₃, hs₃, em⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hμ.2.1)
  have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
  have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
  have h3 := algebraMap_ne_zero_of_mem_hcompl hp hs₃
  have hm₁ : m₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (isUnitIn_div_iff hp m₁ hs₃).1 (em ▸ hμ)
  have ha₁ : a₁ ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    intro h
    have := (isUnitIn_div_iff hp a₁ hs₁).2 h
    rw [← ea] at this
    exact hna this.2.2
  have hQ := conjIdeal_isPrime hp
  set S : 𝓞 K := s₁ * s₂ * s₃ with hS
  have hSm : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem (mul_mem hs₁ hs₂) hs₃
  have hS' := (mem_hcompl_iff hp S).1 hSm
  have hM : m₁ * s₂ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hm₁ hs₂
  have hM' := (mem_hcompl_iff hp _).1 hM
  have e1 : (1 - κ * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, hS]; simp only [map_sub, map_mul]; field_simp
  have e2 : (1 - (κ + μ) * a)
      = algebraMap (𝓞 K) K (S - (k₁ * s₃ + m₁ * s₂) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, em, hS]; simp only [map_sub, map_mul, map_add]; field_simp
  rw [e1, e2, isUnitIn_div_iff hp _ hSm, isUnitIn_div_iff hp _ hSm, mem_hcompl_iff hp,
    mem_hcompl_iff hp]
  have hor : a₁ ∈ p ∨ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
    by_contra h
    push Not at h
    exact ha₁ ((mem_hcompl_iff hp a₁).2 h)
  rcases hor with h | h
  · exact BE.avoid_two hQ (k₁ * s₃) h hS'.1 hS'.2 hM'.2
  · rcases BE.avoid_two hp (k₁ * s₃) h hS'.2 hS'.1 hM'.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) where
  star_mem := fun _ ha => star_mem_locRing hp.isPrime ha
  frac := frac_locRing p
  unram := unram_locRing hK hp
  principal := principal_locRing hK hp
  unit_or := fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem loc_gmap (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsm : ∀ (s : 𝓞 K) (v : V), g (s • v) = s • g v := fun s v => by
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s (g v), map_smul]
  unfold Formalism.HermitianLatticesTheory.loc Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.locS
  ext x
  simp only [Submodule.mem_map, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    refine ⟨g.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have e : s • g.symm x = y := g.injective (by rw [hsm, g.apply_symm_apply]; exact hyx.symm)
    rw [e]; exact hy
  · rintro ⟨z, ⟨s, hs, hz⟩, rfl⟩
    exact ⟨s, hs, s • z, hz, hsm s z⟩

theorem gmap_injective (g : V ≃ₗ[K] V) :
    Function.Injective (Formalism.HermitianLatticesTheory.gmap g : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by
  intro L M hLM
  unfold Formalism.HermitianLatticesTheory.gmap at hLM
  exact Submodule.map_injective_of_injective (f := (g : V →ₗ[K] V).restrictScalars (𝓞 K))
    (fun a b h => g.injective h) hLM

theorem isUnimodularAt_of_loc_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (p : Ideal (𝓞 K))
    {L M : Submodule (𝓞 K) V} (he : Formalism.HermitianLatticesTheory.loc (K := K) p L = Formalism.HermitianLatticesTheory.loc (K := K) p M) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p L ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p M := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [he]

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).mp ha
  obtain ⟨t, ht, htm⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hm
  refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, mul_mem hs ht, ?_⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have : (s * t) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t), ← algebraMap_smul K r, ← algebraMap_smul K t, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp
  rw [this]
  exact L.smul_mem r htm

theorem isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by
  have hu' : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L ↔
      ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hp ha hm
  · intro x hx y hy
    exact (hu' y).mp hy x hx
  · intro x hx
    exact (hu' x).mpr hx
  · intro x
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

end Formalism.HermitianLattices.Ext.L3.WA
end
end
