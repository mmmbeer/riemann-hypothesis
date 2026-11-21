import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import BuildAid.ForwardExisting

section
section
noncomputable section

namespace GlobalTheory.SubKur

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM Filter Topology

section General

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max x (-y)

theorem norm_sum_le {ι : Type} (s : Finset ι) (f : ι → K) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, ‖f i‖ ≤ r) :
    ‖∑ i ∈ s, f i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_pow_sub_pow_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)‖ ≤ 1 := by
    refine norm_sum_le _ _ zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (by positivity) (pow_le_one₀ (norm_nonneg _) hb)
  calc _ ≤ 1 * ‖a - b‖ := by gcongr
    _ = _ := one_mul _

theorem norm_pow_l_sub_le (l : ℕ) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hab : ‖a - b‖ ≤ ‖(l : K)‖) :
    ‖a ^ l - b ^ l‖ ≤ ‖(l : K)‖ * ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  have hsplit : ∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i) =
      ∑ i ∈ Finset.range l, (a ^ i - b ^ i) * b ^ (l - 1 - i) + (l : K) * b ^ (l - 1) := by
    have h1 : ∀ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i) = (a ^ i - b ^ i) * b ^ (l - 1 - i) + b ^ (l - 1) := by
      intro i hi
      have hi' : i + (l - 1 - i) = l - 1 := by
        have := Finset.mem_range.1 hi
        omega
      rw [sub_mul, ← pow_add, hi']
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine norm_sum_le _ _ (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow]
    calc ‖a ^ i - b ^ i‖ * ‖b‖ ^ (l - 1 - i) ≤ ‖a - b‖ * 1 := by
          gcongr
          · exact norm_pow_sub_pow_le ha hb i
          · exact pow_le_one₀ (norm_nonneg _) hb
      _ ≤ _ := by rw [mul_one]; exact hab
  · rw [norm_mul, norm_pow]
    calc ‖(l : K)‖ * ‖b‖ ^ (l - 1) ≤ ‖(l : K)‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hb
      _ = _ := mul_one _

theorem norm_pow_l_pow_sub_le (l : ℕ) (hl : ‖(l : K)‖ ≤ 1) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : ‖a - b‖ ≤ ‖(l : K)‖) (m : ℕ) :
    ‖a ^ (l ^ m) - b ^ (l ^ m)‖ ≤ ‖(l : K)‖ ^ m * ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha' : ‖a ^ (l ^ m)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    have hb' : ‖b ^ (l ^ m)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    have hpm : ‖(l : K)‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hl
    have hd : ‖a ^ (l ^ m) - b ^ (l ^ m)‖ ≤ ‖(l : K)‖ :=
      ih.trans ((mul_le_of_le_one_left (norm_nonneg _) hpm).trans hab)
    rw [pow_succ, pow_mul, pow_mul]
    calc _ ≤ ‖(l : K)‖ * ‖a ^ (l ^ m) - b ^ (l ^ m)‖ := norm_pow_l_sub_le l ha' hb' hd
      _ ≤ ‖(l : K)‖ * (‖(l : K)‖ ^ m * ‖a - b‖) := by gcongr
      _ = _ := by ring

end General

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_lt_one : ‖(l : ℂ_[l])‖ < 1 := by
  have h : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_l_pos : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_pos_iff]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem mem_Kur_of_pow_eq {N : ℕ} (hN : 0 < N) {t : ℂ_[l]} (ht : t ^ (l ^ N) = t) : t ∈ MaximalUnramifiedExtension l := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact (MaximalUnramifiedExtension l).zero_mem
  have hp : l.Prime := Fact.out
  have hq1 : 2 ≤ l ^ N := le_trans hp.two_le (Nat.le_self_pow hN.ne' l)
  have hpow : t ^ (l ^ N - 1) = 1 := by
    have h2 : t ^ (l ^ N - 1) * t = 1 * t := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), ht, one_mul]
    exact mul_right_cancel₀ h0 h2
  have hnd : ¬ l ∣ l ^ N - 1 := by
    intro hd
    have h1 : l ∣ l ^ N := dvd_pow_self l hN.ne'
    have h3 : l ∣ l ^ N - (l ^ N - 1) := Nat.dvd_sub h1 hd
    rw [show l ^ N - (l ^ N - 1) = 1 by omega] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  exact Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨l ^ N - 1, by omega, hnd, hpow⟩)

variable (F : Subfield ℂ_[l]) (N : ℕ)

theorem closure_res (h1 : ∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖)
    (h2 : ∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) :
    ∀ y ∈ F.topologicalClosure, ‖y‖ ≤ 1 → ‖y ^ (l ^ N) - y‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro y hy hy1
  obtain ⟨y', hy'F, hyy'⟩ := Metric.mem_closure_iff.1 hy _ (norm_l_pos (l := l))
  rw [dist_eq_norm] at hyy'
  have hl1 := (norm_l_lt_one (l := l)).le
  have hy'1 : ‖y'‖ ≤ 1 := by
    have : y' = y - (y - y') := by ring
    rw [this]
    exact (norm_sub_le_max _ _).trans (max_le hy1 (hyy'.le.trans hl1))
  have hF : ‖y' ^ (l ^ N) - y'‖ ≤ ‖(l : ℂ_[l])‖ :=
    h1 _ (F.sub_mem (F.pow_mem hy'F _) hy'F) (h2 y' hy'F hy'1)
  have hP : ‖y ^ (l ^ N) - y' ^ (l ^ N)‖ ≤ ‖(l : ℂ_[l])‖ :=
    (norm_pow_sub_pow_le hy1 hy'1 _).trans hyy'.le
  have : y ^ (l ^ N) - y = (y ^ (l ^ N) - y' ^ (l ^ N)) + ((y' ^ (l ^ N) - y') - (y - y')) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hP
    ((norm_sub_le_max _ _).trans (max_le hF hyy'.le)))

theorem teich (hN : 0 < N) (G : Subfield ℂ_[l]) (hGc : IsClosed (G : Set ℂ_[l]))
    (hG : ∀ y ∈ G, ‖y‖ ≤ 1 → ‖y ^ (l ^ N) - y‖ ≤ ‖(l : ℂ_[l])‖) {x : ℂ_[l]} (hx : x ∈ G) (hx1 : ‖x‖ ≤ 1) :
    ∃ t ∈ G, t ∈ MaximalUnramifiedExtension l ∧ ‖x - t‖ ≤ ‖(l : ℂ_[l])‖ := by
  set q := l ^ N
  set L := ‖(l : ℂ_[l])‖ with hL
  have hl1 : L < 1 := norm_l_lt_one
  have hl0 : 0 < L := norm_l_pos
  let y : ℕ → ℂ_[l] := fun n => x ^ (q ^ n)
  have hys : ∀ n, y (n + 1) = y n ^ q := fun n => by
    simp only [y, pow_succ, pow_mul]
  have hy1 : ∀ n, ‖y n‖ ≤ 1 := fun n => by
    simp only [y, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1
  have hyG : ∀ n, y n ∈ G := fun n => G.pow_mem hx _
  have hLN : L ^ N ≤ L := pow_le_of_le_one hl0.le hl1.le hN.ne'
  have hstep : ∀ n, ‖y (n + 1) - y n‖ ≤ L * L ^ n := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, mul_one, hys]
      simpa [y] using hG x hx hx1
    | succ n ih =>
      have hd : ‖y (n + 1) - y n‖ ≤ L := ih.trans (mul_le_of_le_one_right hl0.le (pow_le_one₀ hl0.le hl1.le))
      rw [hys (n + 1), hys n]
      calc _ ≤ L ^ N * ‖y (n + 1) - y n‖ :=
            norm_pow_l_pow_sub_le l hl1.le (hy1 _) (hy1 _) (hys n ▸ hd) N |>.trans_eq' (by rw [hys n])
        _ ≤ L * (L * L ^ n) := by gcongr
        _ = L * L ^ (n + 1) := by ring
  have hcau : CauchySeq y := by
    refine cauchySeq_of_le_geometric L L hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev]
    exact hstep n
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hcau
  have htG : t ∈ G := hGc.mem_of_tendsto ht (Eventually.of_forall hyG)
  have htq : t ^ q = t := by
    have hA : Tendsto (fun n => y (n + 1)) atTop (𝓝 t) := (tendsto_add_atTop_iff_nat 1).2 ht
    have hB : Tendsto (fun n => y (n + 1)) atTop (𝓝 (t ^ q)) := by
      simp only [hys]
      exact ht.pow q
    exact tendsto_nhds_unique hB hA
  have hball : ∀ n, y n ∈ Metric.closedBall x L := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    induction n with
    | zero => simp [y, hl0.le]
    | succ n ih =>
      have : y (n + 1) - x = (y (n + 1) - y n) + (y n - x) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((hstep n).trans (mul_le_of_le_one_right hl0.le (pow_le_one₀ hl0.le hl1.le))) ih)
  have htb := Metric.isClosed_closedBall.mem_of_tendsto ht (Eventually.of_forall hball)
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at htb
  exact ⟨t, htG, mem_Kur_of_pow_eq hN htq, htb⟩

end Padic

section Main

variable {l : ℕ} [Fact l.Prime]

theorem approx {N : ℕ} (hN : 0 < N) (G : Subfield ℂ_[l]) (hGc : IsClosed (G : Set ℂ_[l]))
    (hG : ∀ y ∈ G, ‖y‖ ≤ 1 → ‖y ^ (l ^ N) - y‖ ≤ ‖(l : ℂ_[l])‖) (k : ℕ) :
    ∀ x ∈ G, ‖x‖ ≤ 1 → ∃ s ∈ MaximalUnramifiedExtension l, ‖x - s‖ ≤ ‖(l : ℂ_[l])‖ ^ k := by
  induction k with
  | zero => exact fun x _ hx1 => ⟨0, (MaximalUnramifiedExtension l).zero_mem, by simpa using hx1⟩
  | succ k ih =>
    intro x hx hx1
    obtain ⟨t, htG, htK, hxt⟩ := teich N hN G hGc hG hx hx1
    have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_l_pos
    have hl0' : (l : ℂ_[l]) ≠ 0 := norm_pos_iff.1 hl0
    set x₁ := (x - t) / (l : ℂ_[l])
    have hx₁G : x₁ ∈ G := G.div_mem (G.sub_mem hx htG) (natCast_mem G l)
    have hx₁1 : ‖x₁‖ ≤ 1 := by
      rw [norm_div]; exact (div_le_one hl0).2 hxt
    obtain ⟨s₁, hs₁K, hs₁⟩ := ih x₁ hx₁G hx₁1
    refine ⟨t + (l : ℂ_[l]) * s₁, (MaximalUnramifiedExtension l).add_mem htK ((MaximalUnramifiedExtension l).mul_mem (natCast_mem (MaximalUnramifiedExtension l) l) hs₁K), ?_⟩
    have : x - (t + (l : ℂ_[l]) * s₁) = (l : ℂ_[l]) * (x₁ - s₁) := by
      simp only [x₁]; field_simp; ring
    rw [this, norm_mul, pow_succ']
    gcongr

end Main

open GlobalTheory.SubKur in

theorem le_Kur : ∀ (l : ℕ) [Fact l.Prime] (F : Subfield ℂ_[l]) (N : ℕ), 0 < N → (∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖) →
    (∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) → F ≤ MaximalUnramifiedExtension l := by
  intro l _ F N hN h1 h2
  have hG := closure_res F N h1 h2
  have hGc := F.isClosed_topologicalClosure
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one
  have hKc : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := Subfield.isClosed_topologicalClosure _
  have hint : ∀ x ∈ F, ‖x‖ ≤ 1 → x ∈ MaximalUnramifiedExtension l := by
    intro x hx hx1
    have hxG : x ∈ F.topologicalClosure := F.le_topologicalClosure hx
    rw [← SetLike.mem_coe, ← hKc.closure_eq]
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hl1
    obtain ⟨s, hsK, hs⟩ := approx hN _ hGc hG k x hxG hx1
    exact ⟨s, hsK, by rw [dist_eq_norm]; exact hs.trans_lt hk⟩
  intro x hx
  by_cases hx1 : ‖x‖ ≤ 1
  · exact hint x hx hx1
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx1
    have hi : ‖x⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx1))
    have := (MaximalUnramifiedExtension l).inv_mem (hint x⁻¹ (F.inv_mem hx) hi)
    rwa [inv_inv] at this

end GlobalTheory.SubKur
end
end

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_subfield_criterion : ∀ (l : ℕ) [Fact l.Prime] (F : Subfield ℂ_[l]) (N : ℕ), 0 < N → (∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖) → (∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) → F ≤ MaximalUnramifiedExtension l := by
  atlas_forward_decl GlobalTheory.SubKur.le_Kur
end

section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM NumberField

noncomputable section

namespace GlobalTheory.NfKur

variable {M : Type} [Field M] [NumberField M] {l : ℕ} [Fact l.Prime]

theorem norm_int_le (φ : M →+* ℂ_[l]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (φ (a : M)) := by
    convert map_isIntegral_int φ a.isIntegral_coe; exact Subsingleton.elim _ _
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[l])).integer (φ (a : M)) := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[l]))).mem_of_integral h1
  have h3 : ‖φ (a : M)‖₊ ≤ 1 := h2
  exact_mod_cast h3

def primeAt (φ : M →+* ℂ_[l]) : Ideal (𝓞 M) where
  carrier := {a | ‖φ (a : M)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := fun c {a} ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le φ c) (norm_nonneg _) ha

theorem mem_primeAt (φ : M →+* ℂ_[l]) (a : 𝓞 M) : a ∈ primeAt φ ↔ ‖φ (a : M)‖ < 1 := Iff.rfl

theorem notMem_primeAt (φ : M →+* ℂ_[l]) (a : 𝓞 M) : a ∉ primeAt φ ↔ ‖φ (a : M)‖ = 1 :=
  ⟨fun h => le_antisymm (norm_int_le φ a) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩

instance primeAt_isPrime (φ : M →+* ℂ_[l]) : (primeAt φ).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).2 ((notMem_primeAt φ 1).2 (by simp)), fun {a b} hab => ?_⟩
  by_contra hc
  rw [not_or, notMem_primeAt, notMem_primeAt] at hc
  exact (notMem_primeAt φ (a * b)).2 (by simp [hc.1, hc.2]) hab

theorem norm_l (φ : M →+* ℂ_[l]) : ‖φ ((l : 𝓞 M) : M)‖ = ‖(l : ℂ_[l])‖ := by simp

theorem norm_l_lt_one : ‖(l : ℂ_[l])‖ < 1 := by
  have : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem l_mem_primeAt (φ : M →+* ℂ_[l]) : (l : 𝓞 M) ∈ primeAt φ := by
  rw [mem_primeAt, norm_l]; exact norm_l_lt_one

theorem primeAt_ne_bot (φ : M →+* ℂ_[l]) : primeAt φ ≠ ⊥ := fun h => by
  have h1 := l_mem_primeAt φ
  rw [h, Ideal.mem_bot] at h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)

theorem exists_denom (φ : M →+* ℂ_[l]) (x : M) (hx : ‖φ x‖ ≤ 1) :
    ∃ s n : 𝓞 M, ‖φ (s : M)‖ = 1 ∧ (s : M) * x = n := by
  obtain ⟨n, d, h | h⟩ := (⟨primeAt φ, inferInstance, primeAt_ne_bot φ⟩ :
    IsDedekindDomain.HeightOneSpectrum (𝓞 M)).exists_primeCompl_mul_eq_or_mul_eq (K := M) x
  · exact ⟨d, n, (notMem_primeAt φ _).1 d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, le_antisymm (norm_int_le φ n) ?_, by rw [mul_comm]; exact h⟩
    have h1 : ‖φ x‖ * ‖φ (n : M)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← (notMem_primeAt φ _).1 d.2]
      exact congrArg (fun y => ‖φ y‖) h
    nlinarith [norm_nonneg (φ (n : M)), norm_nonneg (φ x)]

theorem exists_mul_dvd_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (a : R)
    (ha : a ∈ P) (hP : a ∉ P ^ 2) : ∃ s : R, s ∉ P ∧ ∀ b ∈ P, a ∣ s * b := by
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 ha
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hP
    have h1 : a ∈ P * J := hJ ▸ Ideal.mem_span_singleton_self a
    rw [pow_two]
    exact Ideal.mul_mono_right h h1
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨s, hsP, fun b hb => ?_⟩
  have : s * b ∈ Ideal.span {a} := by
    rw [hJ, mul_comm s b]; exact Ideal.mul_mem_mul hb hsJ
  exact Ideal.mem_span_singleton.1 this

theorem exists_pow_mem (P : Ideal (𝓞 M)) [hP : P.IsPrime] (h0 : P ≠ ⊥) (hl : (l : 𝓞 M) ∈ P) :
    ∃ N : ℕ, 0 < N ∧ ∀ s n : 𝓞 M, s ∉ P → n ^ (l ^ N) - s ^ (l ^ N - 1) * n ∈ P := by
  classical
  haveI : P.IsMaximal := hP.isMaximal h0
  letI : Field (𝓞 M ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P h0
  letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _
  have hl0 : (l : 𝓞 M ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hl
  haveI : CharP (𝓞 M ⧸ P) l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl0
  obtain ⟨N, -, hN⟩ := FiniteField.card (𝓞 M ⧸ P) l
  refine ⟨N, N.pos, fun s n hs => ?_⟩
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, ← hN, FiniteField.pow_card,
    FiniteField.pow_card_sub_one_eq_one _ hs0, one_mul, sub_self]

theorem exists_norm_pow_sub (φ : M →+* ℂ_[l]) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : M, ‖φ x‖ ≤ 1 → ‖φ x ^ (l ^ N) - φ x‖ < 1 := by
  obtain ⟨N, hN, h⟩ := exists_pow_mem (primeAt φ) (primeAt_ne_bot φ) (l_mem_primeAt φ)
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨s, n, hs, hn⟩ := exists_denom φ x hx
  have h1 := (mem_primeAt φ _).1 (h s n ((notMem_primeAt φ s).2 hs))
  have hq : l ^ N ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hn' : φ (n : M) = φ (s : M) * φ x := by rw [← hn, map_mul]
  have h2 : φ ((n ^ (l ^ N) - s ^ (l ^ N - 1) * n : 𝓞 M) : M)
      = φ (s : M) ^ (l ^ N) * (φ x ^ (l ^ N) - φ x) := by
    have h3 : φ ((n ^ (l ^ N) - s ^ (l ^ N - 1) * n : 𝓞 M) : M)
        = φ (n : M) ^ (l ^ N) - φ (s : M) ^ (l ^ N - 1) * φ (n : M) := by simp
    rw [h3, hn', ← mul_assoc, pow_sub_one_mul hq, mul_pow, mul_sub]
  rwa [h2, norm_mul, norm_pow, hs, one_pow, one_mul] at h1

end GlobalTheory.NfKur
end
end
