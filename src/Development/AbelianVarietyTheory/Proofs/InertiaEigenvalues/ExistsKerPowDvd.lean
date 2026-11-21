import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup

section
namespace GlobalTheory.LTLog

open MvPowerSeries GroundTheory.LocalField.FormalGroup

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}
  (K : Type*) [Field K] [Algebra A K] [FaithfulSMul A K]

theorem existsUnique_eigen (hπ : Irreducible π) {f : PowerSeries A} (hf : IsLubinTateSeries π f)
    {σ : Type*} [Finite σ] {ℓ : MvPowerSeries σ K} (hℓ : constantCoeff ℓ = 0) :
    ∃! φ : MvPowerSeries σ K, (2 : ℕ∞) ≤ order (φ - ℓ) ∧
      PowerSeries.subst φ (PowerSeries.C (algebraMap A K π) * PowerSeries.X) =
        subst (substEach (PowerSeries.map (algebraMap A K) f)) φ := by
  have h0 : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  refine existsUnique_of_dvd_defect (π := algebraMap A K π) (by simp) (by simp) ?_ ?_
    (fun x hx => (mul_eq_zero.1 hx).resolve_left h0) (fun n hn => ?_)
    (fun _ _ => (IsUnit.mk0 _ h0).dvd) hℓ
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf.constantCoeff_eq_zero, map_zero]
  · rw [PowerSeries.coeff_map, hf.coeff_one]
  · simpa using (isUnit_one_sub_pow hπ hn).map (algebraMap A K)

noncomputable def log (hπ : Irreducible π) {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries K :=
  (existsUnique_eigen K hπ hf (σ := Unit) (ℓ := (PowerSeries.X : PowerSeries K))
    PowerSeries.constantCoeff_X).exists.choose

theorem coeff_eq_of_order {R σ : Type*} [CommRing R] {φ ψ : MvPowerSeries σ R}
    (h : (2 : ℕ∞) ≤ order (φ - ψ)) {e : σ →₀ ℕ} (he : e.degree ≤ 1) : coeff e φ = coeff e ψ := by
  have he2 : (e.degree : ℕ∞) < 2 := by
    have : e.degree < 2 := by omega
    exact_mod_cast this
  have := coeff_of_lt_order (lt_of_lt_of_le he2 h)
  rwa [map_sub, sub_eq_zero] at this

variable (hπ : Irreducible π) {f g : PowerSeries A} (hf : IsLubinTateSeries π f)
  (hg : IsLubinTateSeries π g)

theorem log_spec : (2 : ℕ∞) ≤ order ((log K hπ hf - PowerSeries.X : PowerSeries K) :
      MvPowerSeries Unit K) ∧
    PowerSeries.subst (log K hπ hf) (PowerSeries.C (algebraMap A K π) * PowerSeries.X) =
      subst (substEach (PowerSeries.map (algebraMap A K) f)) (log K hπ hf) :=
  (existsUnique_eigen K hπ hf (σ := Unit) (ℓ := (PowerSeries.X : PowerSeries K))
    PowerSeries.constantCoeff_X).exists.choose_spec

theorem constantCoeff_log : PowerSeries.constantCoeff (log K hπ hf) = 0 := by
  have := coeff_eq_of_order (log_spec K hπ hf).1 (e := 0) (by simp)
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply] at this
  exact this.trans PowerSeries.constantCoeff_X

theorem coeff_one_log : PowerSeries.coeff 1 (log K hπ hf) = 1 := by
  have := coeff_eq_of_order (log_spec K hπ hf).1 (e := Finsupp.single () 1) (by simp)
  exact this.trans PowerSeries.coeff_one_X

theorem isLift_log : IsLubinTateLift (PowerSeries.C (algebraMap A K π) * PowerSeries.X)
    (PowerSeries.map (algebraMap A K) f) (PowerSeries.X : PowerSeries K) (log K hπ hf) :=
  ⟨constantCoeff_log K hπ hf, (log_spec K hπ hf).1, (log_spec K hπ hf).2⟩

theorem log_subst_self :
    PowerSeries.subst (PowerSeries.map (algebraMap A K) f) (log K hπ hf) =
      PowerSeries.C (algebraMap A K π) * log K hπ hf := by
  have h := (log_spec K hπ hf).2
  rw [subst_substEach_unit, powerSeries_subst_C_mul_X
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_log K hπ hf))] at h
  exact h.symm

omit [IsDomain A] [IsDiscreteValuationRing A] [FaithfulSMul A K] in
theorem constantCoeff_map_eq_zero {u : PowerSeries A} (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap A K) u) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, map_zero]

omit [IsDomain A] [IsDiscreteValuationRing A] [FaithfulSMul A K] in

theorem isLift_map {σ : Type*} [Finite σ] {u v : PowerSeries A}
    (hv : PowerSeries.constantCoeff v = 0) {ℓ φ : MvPowerSeries σ A}
    (h : IsLubinTateLift u v ℓ φ) :
    IsLubinTateLift (PowerSeries.map (algebraMap A K) u) (PowerSeries.map (algebraMap A K) v)
      (map (algebraMap A K) ℓ) (map (algebraMap A K) φ) := by
  obtain ⟨h0, h2, he⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · rw [← map_sub]
    have h3 : ((2 : ℕ) : ℕ∞) ≤ order (map (algebraMap A K) (φ - ℓ)) :=
      nat_le_order fun d hd => by
        rw [coeff_map, coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h2), map_zero]
    exact_mod_cast h3
  · have := congrArg (map (algebraMap A K)) he
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
      map_subst (hasSubst_substEach hv)] at this
    rw [this]
    congr 1
    funext i
    rw [substEach_apply, substEach_apply, PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_X]

section
variable [Finite (IsLocalRing.ResidueField A)]

theorem log_subst_lubinTateHom (a : A) :
    PowerSeries.subst (PowerSeries.map (algebraMap A K) (lubinTateHom hπ hf hg a).toPowerSeries)
        (log K hπ hf) = PowerSeries.C (algebraMap A K a) * log K hπ hg := by
  have hf0 := constantCoeff_map_eq_zero K hf.constantCoeff_eq_zero
  have hg0 := constantCoeff_map_eq_zero K hg.constantCoeff_eq_zero
  have h1 := (isLift_log K hπ hf).comp hf0 hg0 (fun _ =>
    isLift_map K hg.constantCoeff_eq_zero (isLubinTateLift_lubinTateHom hπ hf hg a))
  have hℓ : constantCoeff (σ := Unit)
      (PowerSeries.C (algebraMap A K a) * PowerSeries.X : PowerSeries K) = 0 := by
    change PowerSeries.constantCoeff _ = 0
    simp
  refine (existsUnique_eigen K hπ hg (σ := Unit) hℓ).unique ⟨?_, h1.2.2⟩ ⟨?_, ?_⟩
  · have h2 := h1.2.1
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def, PowerSeries.subst_X] at h2
    · have e : map (algebraMap A K) (PowerSeries.C a * PowerSeries.X : PowerSeries A) =
          (PowerSeries.C (algebraMap A K a) * PowerSeries.X : PowerSeries K) := by
        change PowerSeries.map _ _ = _
        simp
      rw [e] at h2
      exact h2
    · refine PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_map_eq_zero K ?_)
      simp
  · refine two_le_order_sub_C_mul_X ?_ ?_
    · simp [constantCoeff_log]
    · simp [coeff_one_log]
  · have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
    rw [subst_substEach_unit, powerSeries_subst_C_mul_X, PowerSeries.subst_mul hs,
      log_subst_self, PowerSeries.subst_C]
    · change PowerSeries.C _ * _ = PowerSeries.C _ * _
      exact mul_left_comm _ _ _
    · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
      simp [constantCoeff_log]

theorem log_subst_formalGroup :
    PowerSeries.subst (map (algebraMap A K) (lubinTateFormalGroup hπ hf).toPowerSeries)
        (log K hπ hf) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) (log K hπ hf) +
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) (log K hπ hf) := by
  have hf0 := constantCoeff_map_eq_zero K hf.constantCoeff_eq_zero
  have h1 := (isLift_log K hπ hf).comp hf0 hf0 (fun _ =>
    isLift_map K hf.constantCoeff_eq_zero
      (isLubinTateLift_lubinTateLift hπ hf hf (![1, 1] : Fin 2 → A)))
  have hX : ∀ i : Fin 2, IsLubinTateLift (PowerSeries.C (algebraMap A K π) * PowerSeries.X)
      (PowerSeries.map (algebraMap A K) f) (X i)
      (PowerSeries.subst (X i : MvPowerSeries (Fin 2) K) (log K hπ hf)) := by
    intro i
    have := (isLift_log K hπ hf).comp hf0 hf0 (fun _ => isLubinTateLift_X hf0 i)
    rwa [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)] at this
  have hℓ : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  refine (existsUnique_eigen K hπ hf hℓ).unique ⟨?_, h1.2.2⟩ ⟨?_, ?_⟩
  · have h2 := h1.2.1
    have e : map (algebraMap A K) (sum₂ (![1, 1] : Fin 2 → A)) =
        (X 0 + X 1 : MvPowerSeries (Fin 2) K) := by
      rw [linearForm_fin_two]
      simp
    rw [e, ← PowerSeries.subst_def, ← PowerSeries.subst_def,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hℓ)] at h2
    exact h2
  · rw [add_sub_add_comm]
    exact le_trans (le_min (hX 0).2.1 (hX 1).2.1) min_order_le_add
  · have e := fun i => (hX i).2.2
    have e0 := e 0
    have e1 := e 1
    rw [powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (hX _).1)] at e0 e1
    rw [subst_add (hasSubst_substEach hf0), ← e0, ← e1, powerSeries_subst_C_mul_X
      (PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_add, (hX 0).1, (hX 1).1, add_zero])),
      mul_add]

include hf in
omit [Finite (IsLocalRing.ResidueField A)] in

theorem dvd_coeff_pow (m k : ℕ) (hk : k ≠ Nat.card (IsLocalRing.ResidueField A) * m) :
    π ∣ PowerSeries.coeff k (f ^ m) := by
  have h1 : PowerSeries.C π ∣ f - PowerSeries.X ^ Nat.card (IsLocalRing.ResidueField A) := by
    choose c hc using hf.dvd_coeff_sub
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [hc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  obtain ⟨u, hu⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ m)
  have := congrArg (PowerSeries.coeff k) hu
  rw [map_sub, ← pow_mul, PowerSeries.coeff_X_pow, if_neg hk, sub_zero,
    PowerSeries.coeff_C_mul] at this
  exact ⟨_, this⟩

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
theorem coeff_pow_of_lt {u : PowerSeries A} (hu : PowerSeries.constantCoeff u = 0) {m k : ℕ}
    (h : k < m) : PowerSeries.coeff k (u ^ m) = 0 := by
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.2 hu
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
theorem coeff_pow_self {u : PowerSeries A} (hu : PowerSeries.constantCoeff u = 0) (m : ℕ) :
    PowerSeries.coeff m (u ^ m) = PowerSeries.coeff 1 u ^ m := by
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.2 hu
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_succ_X_mul]
  simp

omit [Finite (IsLocalRing.ResidueField A)] in

theorem coeff_log_rec (k : ℕ) :
    (algebraMap A K π - algebraMap A K π ^ k) * PowerSeries.coeff k (log K hπ hf) =
      ∑ m ∈ Finset.range k, PowerSeries.coeff m (log K hπ hf) *
        algebraMap A K (PowerSeries.coeff k (f ^ m)) := by
  have hf0 := constantCoeff_map_eq_zero K hf.constantCoeff_eq_zero
  have h := congrArg (PowerSeries.coeff k) (log_subst_self K hπ hf)
  rw [PowerSeries.coeff_C_mul,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hf0),
    finsum_eq_sum_of_support_subset (s := Finset.range (k + 1)), Finset.sum_range_succ,
    coeff_pow_self hf0, PowerSeries.coeff_map, hf.coeff_one] at h
  · simp only [smul_eq_mul, ← map_pow, PowerSeries.coeff_map] at h
    rw [← map_pow]
    linear_combination -h
  · intro m hm
    rw [Function.mem_support] at hm
    by_contra hc
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    exact hm (by rw [coeff_pow_of_lt hf0 (by omega), smul_zero])

theorem pow_log_mul_coeff_mem (k : ℕ) :
    ∃ b : A, algebraMap A K π ^ Nat.log (Nat.card (IsLocalRing.ResidueField A)) k *
      PowerSeries.coeff k (log K hπ hf) = algebraMap A K b := by
  set q := Nat.card (IsLocalRing.ResidueField A) with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have h0 : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact ⟨0, by simp [constantCoeff_log]⟩
    · exact ⟨1, by simp [coeff_one_log]⟩
  have hterm : ∀ m ∈ Finset.range k, ∃ b : A,
      algebraMap A K π ^ Nat.log q k * (PowerSeries.coeff m (log K hπ hf) *
        algebraMap A K (PowerSeries.coeff k (f ^ m))) = algebraMap A K π * algebraMap A K b := by
    intro m hm
    have hm' := Finset.mem_range.1 hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact ⟨0, by simp [constantCoeff_log]⟩
    obtain ⟨b, hb⟩ := ih m hm'
    rcases (Nat.log_mono_right (b := q) hm'.le).eq_or_lt with he | hl
    · obtain ⟨c, hc⟩ := dvd_coeff_pow hf m k (by
        rintro rfl
        rw [← hq, mul_comm, Nat.log_mul_base hq1 hm0.ne'] at he
        omega)
      refine ⟨b * c, ?_⟩
      rw [← he, hc, ← mul_assoc, hb, map_mul, map_mul]
      ring
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hl
      refine ⟨π ^ d * b * PowerSeries.coeff k (f ^ m), ?_⟩
      rw [hd, map_mul, map_mul, map_pow (algebraMap A K) π d, ← hb]
      ring
  choose! c hc using hterm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, hu⟩ := (isUnit_one_sub_pow hπ (n := j) (by omega)).exists_left_inv
  have hu' := congrArg (algebraMap A K) hu
  simp only [map_mul, map_sub, map_one, map_pow] at hu'
  have hr := congrArg (algebraMap A K π ^ Nat.log q (j + 1) * ·) (coeff_log_rec K hπ hf (j + 1))
  simp only [Finset.mul_sum] at hr
  rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, ← map_sum] at hr
  refine ⟨u * ∑ m ∈ Finset.range (j + 1), c m, mul_left_cancel₀ h0 ?_⟩
  rw [map_mul]
  linear_combination algebraMap A K u * hr - (algebraMap A K π *
    algebraMap A K π ^ Nat.log q (j + 1) * PowerSeries.coeff (j + 1) (log K hπ hf)) * hu'

theorem main :
    PowerSeries.constantCoeff (log K hπ hf) = 0 ∧ PowerSeries.coeff 1 (log K hπ hf) = 1 ∧
    PowerSeries.subst (map (algebraMap A K) (lubinTateFormalGroup hπ hf).toPowerSeries)
        (log K hπ hf) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) (log K hπ hf) +
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) (log K hπ hf) ∧
    (∀ a : A, PowerSeries.subst
        (PowerSeries.map (algebraMap A K) (lubinTateHom hπ hf hf a).toPowerSeries) (log K hπ hf) =
      PowerSeries.C (algebraMap A K a) * log K hπ hf) ∧
    PowerSeries.subst (PowerSeries.map (algebraMap A K) f) (log K hπ hf) =
      PowerSeries.C (algebraMap A K π) * log K hπ hf ∧
    ∀ k : ℕ, ∃ b : A, algebraMap A K π ^ Nat.log (Nat.card (IsLocalRing.ResidueField A)) k *
      PowerSeries.coeff k (log K hπ hf) = algebraMap A K b :=
  ⟨constantCoeff_log K hπ hf, coeff_one_log K hπ hf, log_subst_formalGroup K hπ hf,
    log_subst_lubinTateHom K hπ hf hf, log_subst_self K hπ hf, pow_log_mul_coeff_mem K hπ hf⟩

end

end GlobalTheory.LTLog
end

section
namespace GlobalTheory.DiscEval

open PowerSeries Finset

variable (p : ℕ) {A K C B C' B' : Type*} [CommRing A] [CommRing K] [CommRing C] [CommRing B] [CommRing C']
  [CommRing B']

def Tends (i : C →+* B) (s : ℕ → B) (y : B) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ z : C, s n - y = i ((p : C) ^ r * z)

def OnDisc (a : A →+* K) (L : PowerSeries K) : Prop :=
  ∀ M : ℕ, 0 < M → ∃ D : ℕ, ∀ k : ℕ, ∃ b : A, (p : K) ^ (D + k / M) * coeff k L = a b

noncomputable def psum (κ : K →+* B) (L : PowerSeries K) (x : B) (n : ℕ) : B :=
  ∑ k ∈ range n, κ (coeff k L) * x ^ k

def IsEval (i : C →+* B) (κ : K →+* B) (L : PowerSeries K) (x y : B) : Prop := Tends p i (psum κ L x) y

variable {p} {i : C →+* B} {i' : C' →+* B'} {κ : K →+* B} {a : A →+* K} {o : A →+* C}

theorem eq_zero_of_dvd [h : IsHausdorff (Ideal.span {(p : C)}) C] {z : C} (hz : ∀ r : ℕ, (p : C) ^ r ∣ z) :
    z = 0 :=
  h.haus' z fun r => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hz r

theorem Tends.unique [IsHausdorff (Ideal.span {(p : C)}) C] (hi : Function.Injective i) {s : ℕ → B} {y y' : B}
    (h : Tends p i s y) (h' : Tends p i s y') : y = y' := by
  have key : ∀ r : ℕ, ∃ z : C, y - y' = i ((p : C) ^ r * z) := fun r => by
    obtain ⟨N, hN⟩ := h r
    obtain ⟨N', hN'⟩ := h' r
    obtain ⟨z, hz⟩ := hN (max N N') (le_max_left _ _)
    obtain ⟨z', hz'⟩ := hN' (max N N') (le_max_right _ _)
    exact ⟨z' - z, by rw [mul_sub, map_sub, ← hz, ← hz']; ring⟩
  obtain ⟨z, hz⟩ := key 0
  rw [pow_zero, one_mul] at hz
  have : z = 0 := eq_zero_of_dvd (p := p) fun r => (key r).imp fun w hw => hi (hz.symm.trans hw)
  rwa [this, map_zero, sub_eq_zero] at hz

theorem Tends.map (ψ : B →+* B') (hψ : ∀ z, ∃ z', ψ (i z) = i' z') {s : ℕ → B} {y : B}
    (h : Tends p i s y) : Tends p i' (fun n => ψ (s n)) (ψ y) := fun r =>
  (h r).imp fun N hN n hn => by
    obtain ⟨z, hz⟩ := hN n hn
    obtain ⟨z', hz'⟩ := hψ z
    exact ⟨z', by simp only [← map_sub, hz, map_mul, map_pow, map_natCast, hz']⟩

theorem Tends.const (y : B) : Tends p i (fun _ => y) y := fun _ => ⟨0, fun _ _ => ⟨0, by simp⟩⟩

theorem Tends.add {s t : ℕ → B} {y w : B} (h : Tends p i s y) (h' : Tends p i t w) :
    Tends p i (fun n => s n + t n) (y + w) := fun r => by
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  refine ⟨max N N', fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n (le_of_max_le_left hn)
  obtain ⟨z', hz'⟩ := hN' n (le_of_max_le_right hn)
  exact ⟨z + z', by rw [mul_add, map_add, ← hz, ← hz']; ring⟩

theorem Tends.mul_left (hp : IsUnit (p : B)) {c : B} (hc : ∃ (D : ℕ) (z : C), (p : B) ^ D * c = i z)
    {s : ℕ → B} {y : B} (h : Tends p i s y) : Tends p i (fun n => c * s n) (c * y) := fun r => by
  obtain ⟨D, w, hw⟩ := hc
  refine (h (D + r)).imp fun N hN n hn => ?_
  obtain ⟨z, hz⟩ := hN n hn
  refine ⟨w * z, ?_⟩
  simp only [← mul_sub, hz, map_mul, map_pow, map_natCast, ← hw]
  ring

theorem exists_sum [h : IsPrecomplete (Ideal.span {(p : C)}) C] {N : ℕ} (hN : 0 < N) (t : ℕ → C)
    (ht : ∀ k, (p : C) ^ (k / N) ∣ t k) : ∃ S : C, ∀ n, (p : C) ^ (n / N) ∣ ∑ k ∈ range n, t k - S := by
  have h1 : ∀ m n, m ≤ n → (p : C) ^ (m / N) ∣ ∑ k ∈ range m, t k - ∑ k ∈ range n, t k := fun m n hmn => by
    rw [← neg_sub, dvd_neg, ← sum_Ico_eq_sub _ hmn]
    exact dvd_sum fun k hk => (pow_dvd_pow _ (Nat.div_le_div_right (mem_Ico.1 hk).1)).trans (ht k)
  obtain ⟨S, hS⟩ := h.prec' (fun n => ∑ k ∈ range (n * N), t k) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have := h1 _ _ (Nat.mul_le_mul_right N hmn)
    rwa [Nat.mul_div_cancel _ hN] at this
  refine ⟨S, fun n => ?_⟩
  have h2 := hS (n / N)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  have h3 := h1 _ _ (Nat.div_mul_le_self n N)
  rw [Nat.mul_div_cancel _ hN] at h3
  have := dvd_sub h2 h3
  rwa [show ∀ u v w : C, u - v - (u - w) = w - v from fun u v w => by ring] at this

theorem pow_div_dvd {x : C} {M : ℕ} (hx : (p : C) ∣ x ^ M) (k : ℕ) : (p : C) ^ (k / M) ∣ x ^ k := by
  refine (pow_dvd_pow_of_dvd hx _).trans ?_
  rw [← pow_mul]
  exact pow_dvd_pow _ (Nat.mul_div_le k M)

theorem two_mul_div_le (k M : ℕ) : k / (M * 2) + k / (M * 2) ≤ k / M := by
  rw [← Nat.div_div_eq_div_mul]
  omega

theorem exists_pos_pow {x : C} (hx : ∃ M : ℕ, (p : C) ∣ x ^ M) : ∃ M : ℕ, 0 < M ∧ (p : C) ∣ x ^ M :=
  hx.elim fun M hM => ⟨M + 1, M.succ_pos, hM.trans (pow_dvd_pow _ M.le_succ)⟩

theorem term_bound (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} {M D : ℕ}
    (hD : ∀ k : ℕ, ∃ b : A, (p : K) ^ (D + k / (M * 2)) * coeff k L = a b) {k n : ℕ} (hk : k ≤ n) {z : C}
    (hz : (p : C) ^ (n / M) ∣ z) :
    ∃ w : C, (p : B) ^ D * (κ (coeff k L) * i z) = i ((p : C) ^ (n / (M * 2)) * w) := by
  obtain ⟨b, hb⟩ := hD k
  obtain ⟨w, rfl⟩ := hz
  have h1 : k / (M * 2) + n / (M * 2) ≤ n / M :=
    (Nat.add_le_add_right (Nat.div_le_div_right hk) _).trans (two_mul_div_le n M)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  have h2 := congrArg κ hb
  refine ⟨(p : C) ^ d * o b * w, ?_⟩
  simp only [map_mul, map_pow, map_natCast, h, hd, ← h2]
  ring

theorem exists_isEval_rate [IsPrecomplete (Ideal.span {(p : C)}) C] (hp : IsUnit (p : B))
    (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L) {x : C}
    (hx : ∃ M : ℕ, (p : C) ∣ x ^ M) : ∃ y : B, IsEval p i κ L (i x) y ∧ ∃ D N : ℕ, 0 < N ∧
      (∀ k, ∃ w : C, (p : B) ^ D * (κ (coeff k L) * i x ^ k) = i ((p : C) ^ (k / N) * w)) ∧
      ∀ n, ∃ w : C, (p : B) ^ D * (psum κ L (i x) n - y) = i ((p : C) ^ (n / N) * w) := by
  obtain ⟨M, hM, hx⟩ := exists_pos_pow hx
  have hN : 0 < M * 2 := by omega
  obtain ⟨D, hD⟩ := hL (M * 2) hN
  have ht := fun k => term_bound h hD (le_refl k) (pow_div_dvd hx k)
  simp only [map_pow i x] at ht
  choose w hw using id ht
  obtain ⟨S, hS⟩ := exists_sum hN (fun k => (p : C) ^ (k / (M * 2)) * w k) fun k => dvd_mul_right _ _
  obtain ⟨u, hu⟩ := (hp.pow D).exists_right_inv
  have hr : ∀ n, ∃ w : C, (p : B) ^ D * (psum κ L (i x) n - u * i S) = i ((p : C) ^ (n / (M * 2)) * w) :=
    fun n => (hS n).imp fun z hz => by
      rw [← hz, map_sub, map_sum, mul_sub, ← mul_assoc, hu, one_mul, psum, mul_sum]
      simp only [hw]
  refine ⟨u * i S, fun r => ⟨(D + r) * (M * 2), fun n hn => ?_⟩, D, M * 2, hN, ht, hr⟩
  obtain ⟨z, hz⟩ := hr n
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ((Nat.le_div_iff_mul_le hN).2 hn)
  refine ⟨(p : C) ^ d * z, (hp.pow D).mul_left_cancel ?_⟩
  simp only [hz, hd, map_mul, map_pow, map_natCast]
  ring

theorem existsUnique_isEval [IsAdicComplete (Ideal.span {(p : C)}) C] (hi : Function.Injective i)
    (hp : IsUnit (p : B)) (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L) {x : C}
    (hx : ∃ M : ℕ, (p : C) ∣ x ^ M) : ∃! y : B, IsEval p i κ L (i x) y :=
  (exists_isEval_rate hp h hL hx).elim fun y hy => ⟨y, hy.1, fun _ h' => Tends.unique hi h' hy.1⟩

theorem IsEval.map {K' : Type*} [CommRing K'] {κ' : K' →+* B'} (ψ : B →+* B') (τ : K →+* K')
    (hψ : ∀ z, ∃ z', ψ (i z) = i' z') (hκ : ∀ c, ψ (κ c) = κ' (τ c)) {L : PowerSeries K} {x y : B}
    (h : IsEval p i κ L x y) : IsEval p i' κ' (PowerSeries.map τ L) (ψ x) (ψ y) := by
  have := Tends.map ψ hψ h
  intro r
  simpa only [psum, map_sum, map_mul, map_pow, hκ, coeff_map] using this r

theorem IsEval.C_mul (hp : IsUnit (p : B)) {c : K} (hc : ∃ (D : ℕ) (z : C), (p : B) ^ D * κ c = i z)
    {L : PowerSeries K} {x y : B} (h : IsEval p i κ L x y) : IsEval p i κ (PowerSeries.C c * L) x (κ c * y) := by
  have := Tends.mul_left hp hc h
  intro r
  simpa only [psum, coeff_C_mul, map_mul, mul_sum, mul_assoc] using this r

theorem IsEval.add {L L' : PowerSeries K} {x y y' : B} (h : IsEval p i κ L x y) (h' : IsEval p i κ L' x y') :
    IsEval p i κ (L + L') x (y + y') := by
  have := Tends.add h h'
  intro r
  simpa only [psum, map_add, add_mul, sum_add_distrib] using this r

theorem pow_sub_dvd (u : PowerSeries A) {x y d : C} {n : ℕ} (hx : d ∣ x ^ n)
    (hy : d ∣ y - ∑ j ∈ range n, o (coeff j u) * x ^ j) (k : ℕ) :
    d ∣ y ^ k - ∑ j ∈ range n, o (coeff j (u ^ k)) * x ^ j := by
  have e : ∀ v : PowerSeries A, ∑ j ∈ range n, o (coeff j v) * x ^ j = Polynomial.eval₂RingHom o x (trunc n v) :=
    fun v => (eval₂_trunc_eq_sum_range x o n v).symm
  rw [e] at hy ⊢
  have h1 : Polynomial.X ^ n ∣ trunc n u ^ k - trunc n (u ^ k) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro j hj
    rw [Polynomial.coeff_sub, ← trunc_trunc_pow, coeff_trunc, if_pos hj, ← Polynomial.coe_pow,
      Polynomial.coeff_coe, sub_self]
  have h2 := map_dvd (Polynomial.eval₂RingHom o x) h1
  rw [map_pow, map_sub, map_pow, show Polynomial.eval₂RingHom o x Polynomial.X = x from
    Polynomial.eval₂_X o x] at h2
  have := dvd_add (hy.trans (sub_dvd_pow_sub_pow _ _ k)) (hx.trans h2)
  rwa [sub_add_sub_cancel] at this

theorem coeff_pow_of_lt {u : PowerSeries K} (hu : constantCoeff u = 0) {m k : ℕ} (h : k < m) :
    coeff k (u ^ m) = 0 := by
  obtain ⟨v, rfl⟩ := X_dvd_iff.2 hu
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem IsEval.subst (hp : IsUnit (p : B)) (h : ∀ c, i (o c) = κ (a c)) {L : PowerSeries K} (hL : OnDisc p a L)
    {u : PowerSeries A} (hu : constantCoeff u = 0) {x y : C} {M : ℕ} (hM : 0 < M) (hx : (p : C) ∣ x ^ M)
    (hy : ∀ n, (p : C) ^ (n / M) ∣ y - ∑ j ∈ range n, o (coeff j u) * x ^ j) {w : B}
    (hw : IsEval p i κ L (i y) w) : IsEval p i κ (L.subst (PowerSeries.map a u)) (i x) w := by
  have hN : 0 < M * 2 := by omega
  obtain ⟨D, hD⟩ := hL (M * 2) hN
  have hu' : constantCoeff (PowerSeries.map a u) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have hc : ∀ n j, j < n → coeff j (L.subst (PowerSeries.map a u)) =
      ∑ k ∈ range n, coeff k L * a (coeff j (u ^ k)) := fun n j hj => by
    rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hu'), finsum_eq_sum_of_support_subset (s := range n)]
    · simp only [smul_eq_mul, ← map_pow, coeff_map]
    · intro m hm
      rw [Function.mem_support] at hm
      by_contra hc
      simp only [coe_range, Set.mem_Iio, not_lt] at hc
      exact hm (by rw [coeff_pow_of_lt hu' (by omega), smul_zero])
  have hs : ∀ n, psum κ L (i y) n - psum κ (L.subst (PowerSeries.map a u)) (i x) n =
      ∑ k ∈ range n, κ (coeff k L) * i (y ^ k - ∑ j ∈ range n, o (coeff j (u ^ k)) * x ^ j) := fun n => by
    have e : psum κ (L.subst (PowerSeries.map a u)) (i x) n =
        ∑ j ∈ range n, ∑ k ∈ range n, κ (coeff k L * a (coeff j (u ^ k))) * i x ^ j :=
      sum_congr rfl fun j hj => by rw [hc n j (mem_range.1 hj), map_sum, sum_mul]
    rw [e, psum, sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [map_sub, map_sum, map_mul, map_pow i, h, mul_sub, mul_sum, mul_assoc]
  intro r
  obtain ⟨N, hN'⟩ := hw r
  refine ⟨max N ((D + r) * (M * 2)), fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN' n (le_of_max_le_left hn)
  choose! v hv using fun k (hk : k ∈ range n) =>
    term_bound h hD (mem_range.1 hk).le (pow_sub_dvd u (pow_div_dvd hx n) (hy n) k)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ((Nat.le_div_iff_mul_le hN).2 (le_of_max_le_right hn))
  have h2 : psum κ L (i y) n - psum κ (L.subst (PowerSeries.map a u)) (i x) n =
      i ((p : C) ^ r * ((p : C) ^ d * ∑ k ∈ range n, v k)) := by
    refine (hp.pow D).mul_left_cancel ?_
    rw [hs, mul_sum, sum_congr rfl hv, ← map_sum, ← mul_sum]
    simp only [hd, map_mul, map_pow, map_natCast]
    ring
  exact ⟨z - (p : C) ^ d * ∑ k ∈ range n, v k, by rw [mul_sub, map_sub, ← hz, ← h2]; ring⟩

theorem onDisc_of_log {π : A} (hπ : π ∣ (p : A)) {q : ℕ} (hq : 1 < q) {L : PowerSeries K}
    (hL : ∀ k, ∃ b : A, a π ^ Nat.log q k * coeff k L = a b) : OnDisc p a L := fun M hM => by
  refine ⟨M, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hL k
  obtain ⟨c, hc⟩ := hπ
  have h1 : Nat.log q k ≤ M + k / M := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    refine (Nat.log_lt_of_lt_pow hk.ne' ?_).le
    rw [pow_add]
    refine (Nat.lt_mul_div_succ k hM).trans_le (Nat.mul_le_mul (Nat.lt_pow_self hq).le (Nat.lt_pow_self hq))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  refine ⟨c ^ Nat.log q k * (p : A) ^ d * b, ?_⟩
  have h2 : (p : K) = a π * a c := by rw [← map_mul, ← hc, map_natCast]
  simp only [hd, map_mul, map_pow, map_natCast, ← hb, pow_add]
  rw [show (p : K) ^ Nat.log q k = (a π * a c) ^ Nat.log q k by rw [h2]]
  ring

end GlobalTheory.DiscEval
end

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal GlobalTheory.Prism IsLocalRing Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.DiscEval
open GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AcrisK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

variable (l) in

abbrev aC : Ainf l →+* Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l)

scoped instance algWC : Algebra (W0 K) (Per.Acris l) := ((aC l).comp (wA l (fK K)).toRingHom).toAlgebra

def CK : Type := Per.Acris l ⊗[W0 K] ↥(OL K)

instance : CommRing (CK K) := inferInstanceAs (CommRing (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Algebra (Per.Acris l) (CK K) :=
  inferInstanceAs (Algebra (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Algebra ↥(OL K) (CK K) :=
  (Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Per.Acris l ⊗[W0 K] ↥(OL K)).toRingHom.toAlgebra

instance : Module.Free (Per.Acris l) (CK K) :=
  inferInstanceAs (Module.Free (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Module.Finite (Per.Acris l) (CK K) :=
  inferInstanceAs (Module.Finite (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

abbrev inC : Per.Acris l →+* CK K := algebraMap (Per.Acris l) (CK K)

abbrev inI : ↥(OL K) →+* CK K := algebraMap ↥(OL K) (CK K)

theorem tmul_eq (a : Per.Acris l) (c : ↥(OL K)) : (show CK K from a ⊗ₜ[W0 K] c) = inC K a * inI K c := by
  change a ⊗ₜ[W0 K] c = (a ⊗ₜ[W0 K] (1 : ↥(OL K))) * ((1 : Per.Acris l) ⊗ₜ[W0 K] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem inC_wA (w : W0 K) : inC K (aC l (wA l (fK K) w)) = inI K (thetaW (fK K) K w) :=
  ((Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Per.Acris l ⊗[W0 K] ↥(OL K)).commutes w).symm

variable {K} in

@[elab_as_elim] theorem induction_on {p : CK K → Prop} (x : CK K) (mul : ∀ a c, p (inC K a * inI K c))
    (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  TensorProduct.induction_on (motive := p) x (by
    have := mul 0 0; rwa [map_zero, zero_mul] at this) (fun a c => by
    have := mul a c; rwa [← tmul_eq] at this) add

variable {K} in

theorem ringHom_ext {S : Type*} [CommRing S] {u v : CK K →+* S} (hA : ∀ a, u (inC K a) = v (inC K a))
    (hO : ∀ c, u (inI K c) = v (inI K c)) : u = v :=
  RingHom.ext fun x => induction_on x (fun a c => by rw [map_mul, map_mul, hA, hO])
    fun x y hx hy => by rw [map_add, map_add, hx, hy]

section Lift

variable {K} {S : Type*} [CommRing S] (u : Per.Acris l →+* S) (v : ↥(OL K) →+* S)
  (h : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = v (thetaW (fK K) K w))

def lift : CK K →+* S :=
  letI : Algebra (W0 K) S := (u.comp ((aC l).comp (wA l (fK K)).toRingHom)).toAlgebra
  (Algebra.TensorProduct.productMap (R := W0 K) { toRingHom := u, commutes' := fun _ => rfl }
    { toRingHom := v, commutes' := fun w => (h w).symm }).toRingHom

@[simp] theorem lift_inC (a : Per.Acris l) : lift u v h (inC K a) = u a := by
  change u a * v 1 = u a
  rw [map_one, mul_one]

@[simp] theorem lift_inI (c : ↥(OL K)) : lift u v h (inI K c) = v c := by
  change u 1 * v c = v c
  rw [map_one, one_mul]

end Lift

def ofA : AK K →+* CK K := AinfK.lift ((inC K).comp (aC l)) (inI K) (inC_wA K)

theorem ofA_inA (a : Ainf l) : ofA K (inA K a) = inC K (aC l a) := lift_inA _ _ _ a

theorem ofA_inO (c : ↥(OL K)) : ofA K (inO K c) = inI K c := lift_inO _ _ _ c

instance complete_l : IsAdicComplete (Ideal.span {(l : CK K)}) (CK K) := by
  have h := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis (W0 K) ↥(OL K)) (l : Per.Acris l)
    (h := (acris_basic l).1)
  let e : ↥(OL K) ⊗[W0 K] Per.Acris l ≃+* CK K :=
    (Algebra.TensorProduct.comm (W0 K) ↥(OL K) (Per.Acris l)).toRingEquiv
  rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton] at h
  have e1 : e ((1 : ↥(OL K)) ⊗ₜ[W0 K] (l : Per.Acris l)) = (l : CK K) := map_natCast (inC K) l
  rwa [e1] at h

variable {K} in

theorem eq_zero_of_l_mul {x : CK K} (h : (l : CK K) * x = 0) : x = 0 := by
  rw [← map_natCast (inC K), ← Algebra.smul_def] at h
  refine (Module.Free.chooseBasis (Per.Acris l) (CK K)).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis (Per.Acris l) (CK K)).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (acris_basic l).2.1 _ h1

theorem phiA_pow_aC (n : ℕ) (a : Ainf l) : (phiA l ^ n) (aC l a) = aC l ((Per.φA l ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', RingHom.coe_mul, RingHom.coe_mul, Function.comp_apply, Function.comp_apply, ih]
    exact (GlobalTheory.CrisMaps.phiA_extends l).alg _

def frobC : CK K →+* CK K :=
  lift ((inC K).comp (phiA l ^ fK K)) (inI K) fun w => by
    rw [RingHom.comp_apply, phiA_pow_aC, iter_wA, inC_wA]

theorem frobC_inC (a : Per.Acris l) : frobC K (inC K a) = inC K ((⇑(phiA l))^[fK K] a) := by
  rw [frobC, lift_inC, RingHom.comp_apply, RingHom.coe_pow]

theorem frobC_inI (c : ↥(OL K)) : frobC K (inI K c) = inI K c := lift_inI _ _ _ c

theorem frobC_ofA (x : AK K) : frobC K (ofA K x) = ofA K (frobq K x) :=
  AinfK.induction_on x (fun a c => by
    simp only [map_mul, ofA_inA, ofA_inO, frobC_inC, frobC_inI, frobq_inA, frobq_inO]
    rw [← RingHom.coe_pow, ← RingHom.coe_pow, phiA_pow_aC])
    fun x y hx hy => by simp only [map_add, hx, hy]

variable {K}

theorem sigA_aC (g : GQ l) (a : Ainf l) : sigA g (aC l a) = aC l (Per.σA g a) := (GlobalTheory.CrisMaps.sigA_extends g).alg a

def galC (g : ↥(GK K)) : CK K →+* CK K :=
  lift ((inC K).comp (sigA (g : GQ l))) (inI K) fun w => by
    rw [RingHom.comp_apply, sigA_aC, σA_wA, inC_wA]

theorem galC_inC (g : ↥(GK K)) (a : Per.Acris l) : galC g (inC K a) = inC K (sigA (g : GQ l) a) :=
  lift_inC _ _ _ a

theorem galC_inI (g : ↥(GK K)) (c : ↥(OL K)) : galC g (inI K c) = inI K c := lift_inI _ _ _ c

theorem galC_ofA (g : ↥(GK K)) (x : AK K) : galC g (ofA K x) = ofA K (gal K g x) :=
  AinfK.induction_on x (fun a c => by
    simp only [map_mul, ofA_inA, ofA_inO, galC_inC, galC_inI, gal_inA, gal_inO, sigA_aC])
    fun x y hx hy => by simp only [map_add, hx, hy]

theorem l_dvd_pow {x : Ainf l} (hx : Per.θ l x = 0) : (l : Per.Acris l) ∣ aC l x ^ l := by
  obtain ⟨g, hg, e⟩ := exists_dividedPower_mem_Acris0 l x hx l
  have e' : ((l.factorial : ℕ) : Per.Acris0 l) * ⟨g, hg⟩ = algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ l :=
    Subtype.ext (by simpa using e)
  have e2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e'
  rw [map_mul, map_natCast, map_pow] at e2
  rw [← GlobalTheory.RingIface.tower l x] at e2
  change _ = aC l x ^ l at e2
  rw [← e2]
  exact (Nat.cast_dvd_cast (Nat.dvd_factorial hl.out.pos le_rfl)).mul_right _

variable (K) in

theorem exists_ker_pow_dvd : ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ), ∀ z ∈ RingHom.ker (thetaK K) ^ k,
    (l : CK K) ^ (k / M) ∣ ofA K z := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  obtain ⟨N, hN⟩ := exists_ker_pow_le K
  have h1 : Ideal.span {(l : AK K)} ⊔ (RingHom.ker (Per.θ l)).map (inA K) ≤
      (Ideal.span {(l : CK K)}).radical.comap (ofA K) := by
    refine sup_le ?_ (Ideal.map_le_iff_le_comap.2 fun x hx => ⟨l, ?_⟩)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
    · rw [ofA_inA, ← map_pow, Ideal.mem_span_singleton, ← map_natCast (inC K)]
      exact map_dvd _ (l_dvd_pow hx)
  obtain ⟨m, hm⟩ := h1 (hN (Ideal.pow_mem_pow (thetaK_eta hp) N))
  rw [map_pow, ← pow_mul, Ideal.mem_span_singleton] at hm
  obtain ⟨M, hM, h2⟩ := exists_pos_pow ⟨_, hm⟩
  refine ⟨M, hM, fun k z hz => ?_⟩
  rw [ker_thetaK hπ hp, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  refine (pow_div_dvd h2 k).trans ?_
  rw [← map_pow]
  exact map_dvd _ hz

theorem exists_l_dvd_pow {x : AK K} (hx : thetaK K x = 0) : ∃ M : ℕ, (l : CK K) ∣ ofA K x ^ M := by
  obtain ⟨M, hM, h⟩ := exists_ker_pow_dvd K
  refine ⟨M, ?_⟩
  have := h M _ (Ideal.pow_mem_pow hx M)
  rwa [Nat.div_self hM, pow_one, map_pow] at this

variable (K)

def BK : Type := Localization.Away (l : CK K)

instance : CommRing (BK K) := inferInstanceAs (CommRing (Localization.Away (l : CK K)))

instance : Algebra (CK K) (BK K) := inferInstanceAs (Algebra (CK K) (Localization.Away (l : CK K)))

instance : IsLocalization.Away (l : CK K) (BK K) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away (l : CK K)))

abbrev toB : CK K →+* BK K := algebraMap (CK K) (BK K)

theorem isUnit_l : IsUnit (l : BK K) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := BK K) (l : CK K)
  rwa [map_natCast] at h

theorem toB_injective : Function.Injective (toB K) :=
  IsLocalization.injective (M := Submonoid.powers (l : CK K)) (BK K) (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_l_mul h))

variable {K} in

theorem exists_pow_mul (b : BK K) : ∃ (D : ℕ) (z : CK K), (l : BK K) ^ D * b = toB K z := by
  obtain ⟨D, z, h⟩ := IsLocalization.Away.surj (l : CK K) b
  exact ⟨D, z, by rw [← h, map_natCast, mul_comm]⟩

variable {K} in

theorem isUnit_map {S : Type*} [CommRing S] (hS : IsUnit (l : S)) (v : ↥(OL K) →+* S)
    (c : nonZeroDivisors ↥(OL K)) : IsUnit (v c) := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.coe_ne_zero c) hπ
  have h1 := map_dvd v (h.dvd.trans (pow_dvd_pow_of_dvd (dvd_of_not_isUnit hπ (l_mem_max K)) n))
  rw [map_pow, map_natCast] at h1
  exact isUnit_of_dvd_unit h1 (hS.pow n)

abbrev oK : ↥(OL K) →+* ↥K.1 := algebraMap ↥(OL K) ↥K.1

def inK : ↥K.1 →+* BK K :=
  IsLocalization.lift (M := nonZeroDivisors ↥(OL K)) (g := (toB K).comp (inI K)) (isUnit_map (isUnit_l K) _)

theorem inK_oK (c : ↥(OL K)) : inK K (oK K c) = toB K (inI K c) := IsLocalization.lift_eq _ c

def inP : BcrisP l →+* BK K := plusLift ((toB K).comp (inC K)) (isUnit_l K)

theorem inP_algebraMap (a : Per.Acris l) : inP K (algebraMap _ _ a) = toB K (inC K a) := plusLift_alg _ _ a

variable {K}

theorem ringHom_extB {S : Type*} [CommRing S] {u v : BK K →+* S} (h : ∀ z, u (toB K z) = v (toB K z)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers (l : CK K)) (RingHom.ext h)

theorem ringHom_extK {S : Type*} [CommRing S] {u v : ↥K.1 →+* S} (h : ∀ c, u (oK K c) = v (oK K c)) : u = v :=
  IsLocalization.ringHom_ext (nonZeroDivisors ↥(OL K)) (RingHom.ext h)

def awayLift {S : Type*} [CommRing S] (f : CK K →+* S) (h : IsUnit (l : S)) : BK K →+* S :=
  IsLocalization.Away.lift (l : CK K) (g := f) (by rwa [map_natCast])

theorem awayLift_toB {S : Type*} [CommRing S] (f : CK K →+* S) (h : IsUnit (l : S)) (z : CK K) :
    awayLift f h (toB K z) = f z := IsLocalization.Away.lift_eq _ _ z

section LiftB

variable {S : Type*} [CommRing S] (u : Per.Acris l →+* S) (v : ↥K.1 →+* S)
  (h : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = v (oK K (thetaW (fK K) K w)))

include v in
theorem isUnit_l_of : IsUnit (l : S) := by
  have : IsUnit (l : ↥K.1) := (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : ↥K.1) ≠ 0).isUnit
  simpa using this.map v

def liftB : BK K →+* S := awayLift (lift u (v.comp (oK K)) h) (isUnit_l_of v)

theorem liftB_toB (z : CK K) : liftB u v h (toB K z) = lift u (v.comp (oK K)) h z := awayLift_toB _ _ z

theorem liftB_inC (a : Per.Acris l) : liftB u v h (toB K (inC K a)) = u a := by rw [liftB_toB, lift_inC]

theorem liftB_inK (c : ↥K.1) : liftB u v h (inK K c) = v c :=
  RingHom.congr_fun (ringHom_extK (u := (liftB u v h).comp (inK K)) (v := v) fun c => by
    rw [RingHom.comp_apply, inK_oK, liftB_toB, lift_inI, RingHom.comp_apply]) c

end LiftB

theorem awayLift_inK (s : CK K →+* CK K) (hs : ∀ c, s (inI K c) = inI K c) (c : ↥K.1) :
    awayLift ((toB K).comp s) (isUnit_l K) (inK K c) = inK K c :=
  RingHom.congr_fun (ringHom_extK (u := (awayLift ((toB K).comp s) (isUnit_l K)).comp (inK K)) (v := inK K)
    fun c => by rw [RingHom.comp_apply, inK_oK, awayLift_toB, RingHom.comp_apply, hs]) c

variable (K) in

def frobB : BK K →+* BK K := awayLift ((toB K).comp (frobC K)) (isUnit_l K)

theorem frobB_toB (z : CK K) : frobB K (toB K z) = toB K (frobC K z) := awayLift_toB _ _ z

theorem frobB_inK (c : ↥K.1) : frobB K (inK K c) = inK K c := awayLift_inK _ (frobC_inI K) c

def galB (g : ↥(GK K)) : BK K →+* BK K := awayLift ((toB K).comp (galC g)) (isUnit_l K)

theorem galB_toB (g : ↥(GK K)) (z : CK K) : galB g (toB K z) = toB K (galC g z) := awayLift_toB _ _ z

theorem galB_inK (g : ↥(GK K)) (c : ↥K.1) : galB g (inK K c) = inK K c := awayLift_inK _ (galC_inI g) c

variable (K)

scoped instance algWP : Algebra (W0 K) (BcrisP l) :=
  ((algebraMap (Per.Acris l) (BcrisP l)).comp ((aC l).comp (wA l (fK K)).toRingHom)).toAlgebra

scoped instance algWK : Algebra (W0 K) ↥K.1 := ((oK K).comp (thetaW (fK K) K).toRingHom).toAlgebra

abbrev PK : Type := BcrisP l ⊗[W0 K] ↥K.1

def toPK : BK K →+* PK K :=
  liftB ((Algebra.TensorProduct.includeLeftRingHom : BcrisP l →+* PK K).comp (algebraMap (Per.Acris l) (BcrisP l)))
    (Algebra.TensorProduct.includeRight : ↥K.1 →ₐ[W0 K] PK K).toRingHom fun w =>
      ((Algebra.TensorProduct.includeRight : ↥K.1 →ₐ[W0 K] PK K).commutes w).symm

theorem toPK_inP (b : BcrisP l) : toPK K (inP K b) = b ⊗ₜ[W0 K] (1 : ↥K.1) :=
  RingHom.congr_fun (plus_ext (f := (toPK K).comp (inP K))
    (f' := (Algebra.TensorProduct.includeLeftRingHom : BcrisP l →+* PK K)) fun a => by
      rw [RingHom.comp_apply, inP_algebraMap, toPK, liftB_inC, RingHom.comp_apply]) b

theorem toPK_inK (c : ↥K.1) : toPK K (inK K c) = (1 : BcrisP l) ⊗ₜ[W0 K] c := liftB_inK _ _ _ c

def ofPK : PK K →+* BK K :=
  letI : Algebra (W0 K) (BK K) := ((inP K).comp (algebraMap (W0 K) (BcrisP l))).toAlgebra
  (Algebra.TensorProduct.productMap (R := W0 K) { toRingHom := inP K, commutes' := fun _ => rfl }
    { toRingHom := inK K
      commutes' := fun w => ((inK_oK K _).trans (congrArg (toB K) (inC_wA K w).symm)).trans (inP_algebraMap K _).symm
    }).toRingHom

theorem ofPK_tmul (b : BcrisP l) (c : ↥K.1) : ofPK K (b ⊗ₜ[W0 K] c) = inP K b * inK K c := rfl

def equivPK : BK K ≃+* PK K :=
  RingEquiv.ofRingHom (toPK K) (ofPK K)
    (RingHom.ext fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b c =>
        rw [RingHom.comp_apply, ofPK_tmul, map_mul, toPK_inP, toPK_inK, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, RingHom.id_apply]
      | add x y hx hy => simp only [map_add, hx, hy])
    (ringHom_extB fun z => induction_on z (fun a c => by
      rw [map_mul, ← inP_algebraMap, ← inK_oK, RingHom.comp_apply, map_mul, toPK_inP, toPK_inK, map_mul, ofPK_tmul,
        ofPK_tmul, map_one, map_one, mul_one, one_mul, RingHom.id_apply])
      fun x y hx hy => by simp only [map_add, hx, hy])

variable {K}

def Ev (L : PowerSeries ↥K.1) (x : AK K) (y : BK K) : Prop := IsEval l (toB K) (inK K) L (toB K (ofA K x)) y

theorem Ev.unique {L : PowerSeries ↥K.1} {x : AK K} {y y' : BK K} (h : Ev L x y) (h' : Ev L x y') : y = y' :=
  Tends.unique (toB_injective K) h h'

theorem existsUnique_ev {L : PowerSeries ↥K.1} (hL : OnDisc l (oK K) L) {x : AK K} (hx : thetaK K x = 0) :
    ∃! y, Ev L x y :=
  existsUnique_isEval (toB_injective K) (isUnit_l K) (fun c => (inK_oK K c).symm) hL (exists_l_dvd_pow hx)

theorem Ev.frob {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) : Ev L (frobq K x) (frobB K y) := by
  have := IsEval.map (i' := toB K) (κ' := inK K) (frobB K) (RingHom.id _) (fun z => ⟨_, frobB_toB z⟩) frobB_inK h
  rwa [PowerSeries.map_id, frobB_toB, frobC_ofA] at this

theorem Ev.gal (g : ↥(GK K)) {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) :
    Ev L (gal K g x) (galB g y) := by
  have := IsEval.map (i' := toB K) (κ' := inK K) (galB g) (RingHom.id _) (fun z => ⟨_, galB_toB g z⟩) (galB_inK g) h
  rwa [PowerSeries.map_id, galB_toB, galC_ofA] at this

theorem Ev.C_mul (c : ↥K.1) {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) :
    Ev (PowerSeries.C c * L) x (inK K c * y) :=
  IsEval.C_mul (isUnit_l K) (exists_pow_mul _) h

theorem Ev.subst {L : PowerSeries ↥K.1} (hL : OnDisc l (oK K) L) {u : PowerSeries ↥(OL K)}
    (hu : PowerSeries.constantCoeff u = 0) {x y : AK K} (hx : thetaK K x = 0)
    (hy : ∀ n, y - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j u) * x ^ j ∈ RingHom.ker (thetaK K) ^ n)
    {w : BK K} (hw : Ev L y w) : Ev (L.subst (PowerSeries.map (oK K) u)) x w := by
  obtain ⟨M, hM, h⟩ := exists_ker_pow_dvd K
  refine IsEval.subst (o := inI K) (isUnit_l K) (fun c => (inK_oK K c).symm) hL hu hM ?_ (fun n => ?_) hw
  · have := h M _ (Ideal.pow_mem_pow hx M)
    rwa [Nat.div_self hM, pow_one, map_pow] at this
  · simpa only [map_sub, map_sum, map_mul, map_pow, ofA_inO] using h n _ (hy n)

section Log

variable {π : ↥(OL K)} (hπ : Irreducible π) {f : PowerSeries ↥(OL K)} (hf : IsLubinTateSeries π f)

theorem onDisc_log : OnDisc l (oK K) (LTLog.log ↥K.1 hπ hf) :=
  have := OL_resFinite K
  onDisc_of_log (dvd_of_not_isUnit hπ (l_mem_max K)) Finite.one_lt_card (LTLog.pow_log_mul_coeff_mem ↥K.1 hπ hf)

def ltLog (x : AK K) (hx : thetaK K x = 0) : BK K := (existsUnique_ev (onDisc_log hπ hf) hx).exists.choose

theorem ev_ltLog (x : AK K) (hx : thetaK K x = 0) : Ev (LTLog.log ↥K.1 hπ hf) x (ltLog hπ hf x hx) :=
  (existsUnique_ev (onDisc_log hπ hf) hx).exists.choose_spec

theorem ev_log_hom (a : ↥(OL K)) {x y : AK K} (hx : thetaK K x = 0)
    (hy : haveI := OL_resFinite K
      ∀ n, y - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j (lubinTateHom hπ hf hf a).toPowerSeries) * x ^ j ∈
        RingHom.ker (thetaK K) ^ n)
    {w : BK K} (hw : Ev (LTLog.log ↥K.1 hπ hf) y w) : w = inK K (oK K a) * ltLog hπ hf x hx := by
  have := OL_resFinite K
  have h := Ev.subst (onDisc_log hπ hf) (isLubinTateLift_lubinTateHom hπ hf hf a).1 hx hy hw
  rw [LTLog.log_subst_lubinTateHom ↥K.1 hπ hf hf a] at h
  exact h.unique (Ev.C_mul _ (ev_ltLog hπ hf x hx))

theorem ev_log_self {x y : AK K} (hx : thetaK K x = 0)
    (hy : ∀ n, y - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j f) * x ^ j ∈ RingHom.ker (thetaK K) ^ n)
    {w : BK K} (hw : Ev (LTLog.log ↥K.1 hπ hf) y w) : w = inK K (oK K π) * ltLog hπ hf x hx := by
  have h := Ev.subst (onDisc_log hπ hf) hf.constantCoeff_eq_zero hx hy hw
  rw [LTLog.log_subst_self ↥K.1 hπ hf] at h
  exact h.unique (Ev.C_mul _ (ev_ltLog hπ hf x hx))

end Log

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    IsAdicComplete (Ideal.span {(l : CK K)}) (CK K) ∧ Function.Injective (toB K) ∧
    (∀ b, equivPK K (inP K b) = b ⊗ₜ[W0 K] (1 : ↥K.1)) ∧ (∀ c, equivPK K (inK K c) = (1 : BcrisP l) ⊗ₜ[W0 K] c) ∧
    ∀ (π : ↥(OL K)) (hπ : Irreducible π) (f : PowerSeries ↥(OL K)) (hf : IsLubinTateSeries π f) (x : AK K),
      thetaK K x = 0 →
      (∃ D N : ℕ, 0 < N ∧ ∀ k : ℕ, ∃ z : CK K,
        (l : BK K) ^ D * (inK K (PowerSeries.coeff k (LTLog.log ↥K.1 hπ hf)) * toB K (ofA K x) ^ k) =
          toB K ((l : CK K) ^ (k / N) * z)) ∧
      ∃! y : BK K, ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ z : CK K,
        ∑ k ∈ Finset.range n, inK K (PowerSeries.coeff k (LTLog.log ↥K.1 hπ hf)) * toB K (ofA K x) ^ k - y =
          toB K ((l : CK K) ^ r * z) := by
  intro l _ K
  refine ⟨complete_l K, toB_injective K, toPK_inP K, toPK_inK K, fun π hπ f hf x hx =>
    ⟨?_, existsUnique_ev (onDisc_log hπ hf) hx⟩⟩
  obtain ⟨-, -, D, N, hN, h, -⟩ := exists_isEval_rate (isUnit_l K) (fun c => (inK_oK K c).symm)
    (onDisc_log hπ hf) (exists_l_dvd_pow hx)
  exact ⟨D, N, hN, h⟩

end GlobalTheory.AcrisK
end
end
