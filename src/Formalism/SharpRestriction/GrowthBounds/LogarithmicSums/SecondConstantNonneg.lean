import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

section
noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

theorem sum_ite_mem_le {S R : Finset ℕ} (f : ℕ → ℝ) (hf : ∀ p ∈ R, 0 ≤ f p) :
    ∑ p ∈ S, (if p ∈ R then f p else 0) ≤ ∑ p ∈ R, f p := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp; exact (Finset.mem_filter.1 hp).2
  · intro p hp _; exact hf p hp

def prB (y : ℝ) : Finset ℕ := (Finset.range ⌈y⌉₊).filter Nat.Prime

theorem mem_prB {y : ℝ} {p : ℕ} : p ∈ prB y ↔ p.Prime ∧ (p : ℝ) < y := by
  simp [prB, Nat.lt_ceil, and_comm]

theorem card_prB_le (y : ℝ) (hy : 0 ≤ y) : ((prB y).card : ℝ) ≤ y + 1 := by
  have h1 : (prB y).card ≤ ⌈y⌉₊ := by
    have := Finset.card_filter_le (Finset.range ⌈y⌉₊) Nat.Prime
    simpa [prB] using this
  have h2 : ((prB y).card : ℝ) ≤ (⌈y⌉₊ : ℝ) := by exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one hy
  linarith

theorem sum_log_prB (y : ℝ) (hy : 0 ≤ y) : ∑ p ∈ prB y, Real.log p ≤ Real.log 4 * y := by
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hy)
  unfold Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_prB.1 hp
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1.pos, Nat.le_floor h2.le⟩, h1⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le)

theorem sum_logdiv_prB (y : ℝ) (hy : 1 ≤ y) :
    ∑ p ∈ prB y, Real.log p / p ≤ Real.log y * (1 + Real.log y) := by
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : ∑ p ∈ prB y, Real.log p / p ≤ ∑ p ∈ prB y, Real.log y * ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_prB.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1.pos
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hp2.le) (inv_nonneg.2 hp0.le)
  refine le_trans h1 ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hly
  have h2 : ∑ p ∈ prB y, ((p : ℝ))⁻¹ ≤ ∑ p ∈ Finset.Icc 1 ⌊y⌋₊, ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_prB.1 hp
      exact Finset.mem_Icc.2 ⟨hp1.pos, Nat.le_floor hp2.le⟩
    · intro p _ _
      positivity
  refine le_trans h2 ?_
  have h3 := harmonic_le_one_add_log ⌊y⌋₊
  rw [harmonic_eq_sum_Icc] at h3
  push_cast at h3
  refine le_trans h3 ?_
  have h4 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by simpa using hy)
  have h5 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

private lemma scale_a_pos' (s : Scale) : 0 < s.a := by
  unfold Scale.a Scale.b
  exact mul_pos (by linarith [s.one_lt_alt]) (Real.exp_pos _)

private lemma scale_b_pos (s : Scale) : 0 < s.b := by
  unfold Scale.b
  exact Real.exp_pos _

theorem sc_b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.X'
  exact div_pos (scale_a_pos' s) (Real.exp_pos _)

theorem sc_w''_pos (s : Scale) (n : ℕ) (hn : 1 ≤ n) : 0 < s.w'' n := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Scale.w''
  exact div_pos (sc_b'_pos s) (mul_pos hx hn')

theorem n_pos (D : D7) : 1 ≤ D.R.n := by
  unfold Ranks.n
  have h1 := D.R.m_le_f
  have h2 := D.R.two_le_m
  omega

private lemma scale_w_double_prime_le_b_prime_div_x_of_one_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.b' / s.x := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold Scale.w''
  rw [← div_div]
  exact div_le_self (div_nonneg (sc_b'_pos s).le hx.le) hn'

private lemma scale_b_prime_div_x_le_b (s : Scale) : s.b' / s.x ≤ s.b := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hX : 1 ≤ s.X' := by
    unfold Scale.X'
    exact Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hX0 : s.X' ≠ 0 := (lt_of_lt_of_le one_pos hX).ne'
  have hb := scale_b_pos s
  have h : s.b' / s.x = s.b / s.X' := by
    unfold Scale.b' Scale.a
    field_simp <;> ring
  rw [h]
  exact div_le_self hb.le hX

theorem fill_ge (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)) (j : ℕ)
    (z : Bool × HH D) : L.sc.w'' D.R.n ≤ fill X b j z := by
  have hn := n_pos D
  have hI : X.off j z ≤ fill X b j z := by
    unfold fill
    split_ifs with h
    · have := hb z.2 h.2
      have := sc_b'_pos L.sc
      linarith
    · linarith
  have h1 := scale_w_double_prime_le_b_prime_div_x_of_one_le L.sc D.R.n hn
  have h2 := scale_b_prime_div_x_le_b L.sc
  by_cases ht : IsTopPl D z
  · have := (X.off_top j z ht).1
    linarith
  · by_cases hk : IsThickPl D z
    · have := (X.off_thick j z hk).1
      linarith
    · have := (X.off_thin j z ⟨ht, hk⟩).1
      linarith

theorem Sc_facts (P : ParameterChoice' D L) : 100 ≤ L.Sc ∧ 5 * L.Sc ≤ L.sc.w'' D.R.n := by
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    have h3 : 5 ≤ D.R.k := by omega
    exact_mod_cast h3
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hD := P.Del_ge.2.2.2
  have hN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    exact Nat.le_add_right _ _
  have hNr : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN
  have hm10 : (1024 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
    calc (1024 : ℝ) = 2 ^ 10 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hm 10
  have hprod : (5 : ℝ) * 1024 ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
    mul_le_mul (by linarith) hm10 (by norm_num) (by linarith)
  have hDel : (5120 : ℝ) ≤ (D.s.Del : ℝ) := by linarith
  have hkD := mul_le_mul hk hDel (by norm_num) (by linarith)
  have hSc := L.Sc_eq
  have hSc0 : 0 ≤ L.Sc := by
    rw [hSc]
    nlinarith
  constructor
  · rw [hSc]
    nlinarith
  · have h1 := P.kS_le
    nlinarith [mul_le_mul_of_nonneg_right hk hSc0]

theorem fillG_ge (P : ParameterChoice' D L) (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (z : Bool × HH D) : L.sc.w'' D.R.n - L.Sc ≤ fillG X b j z := by
  have hf := fill_ge X b hb j z
  unfold SizeData₂.lifts at hj
  have hj' := Finset.mem_Icc.mp hj
  have hjm : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj'.2
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj'.1
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    have h3 : 5 ≤ D.R.k := by omega
    exact_mod_cast h3
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hD := P.Del_ge.2.2.2
  have hNr : ((D.R.N D.R.m : ℕ) : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by
    unfold Ranks.N
    push_cast <;> ring
  have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hNle : (D.R.N D.R.m : ℝ) ≤ D.s.Del := by
    nlinarith [mul_le_mul_of_nonneg_left hm10 hN0]
  have hDel0 : (0 : ℝ) ≤ D.s.Del := by linarith
  have hSc := L.Sc_eq
  have hka : kaJ D j ≤ L.Sc := by
    unfold kaJ
    rw [hSc]
    nlinarith [mul_le_mul_of_nonneg_right hjm (by linarith : (0 : ℝ) ≤ D.R.t + 1),
      mul_le_mul_of_nonneg_right hk hDel0]
  unfold fillG
  linarith

theorem summable_and_tsum_le_two_mul_div_of_le_div_pow (p y : ℝ) (hp : 2 ≤ p) (f : ℕ → ℝ) (h0 : ∀ e, 0 ≤ f e) (hz : f 0 = 0)
    (h1 : ∀ e, f e ≤ y / p ^ e) : Summable f ∧ ∑' e, f e ≤ 2 * y / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hy : 0 ≤ y := by
    have h := h1 0
    rw [pow_zero, div_one, hz] at h
    exact h
  have hr0 : (0 : ℝ) ≤ 1 / p := (one_div_pos.mpr hp0).le
  have hr1 : 1 / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hgeo := summable_geometric_of_lt_one hr0 hr1
  have hfg : ∀ e, f e ≤ y * (1 / p) ^ e := fun e => by
    rw [one_div_pow, ← div_eq_mul_one_div]
    exact h1 e
  have hf : Summable f := Summable.of_nonneg_of_le h0 hfg (hgeo.mul_left y)
  refine ⟨hf, ?_⟩
  have hshift : Summable (fun e => f (e + 1)) := (summable_nat_add_iff 1).mpr hf
  rw [hf.tsum_eq_zero_add, hz, zero_add]
  have hle : ∀ e : ℕ, f (e + 1) ≤ y / p * (1 / p) ^ e := fun e => by
    have h := h1 (e + 1)
    calc f (e + 1) ≤ y / p ^ (e + 1) := h
      _ = y / p * (1 / p) ^ e := by
        rw [pow_succ, one_div_pow, div_mul_div_comm, mul_one, mul_comm (p ^ e) p]
  calc ∑' e, f (e + 1) ≤ ∑' e : ℕ, y / p * (1 / p) ^ e :=
        Summable.tsum_le_tsum hle hshift (hgeo.mul_left (y / p))
    _ = y / p * (1 - 1 / p)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = y / (p - 1) := by
        rw [one_sub_div hpne, inv_div, div_mul_div_comm, mul_comm p (p - 1), mul_div_mul_right _ _ hpne]
    _ ≤ 2 * y / p := by
        have hp1' : (0 : ℝ) < p - 1 := by linarith
        rw [div_le_iff₀ hp1', div_mul_eq_mul_div, le_div_iff₀ hp0]
        nlinarith

def thW (D : D7) (s : Scale) : ℝ := 1 / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))

theorem k_ge (D : D7) : (5 : ℝ) ≤ (D.R.k : ℝ) := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  have h3 : 5 ≤ D.R.k := by omega
  exact_mod_cast h3

theorem thW_bounds (D : D7) (s : Scale) : 0 < thW D s ∧ thW D s ≤ 1 / 5 := by
  have hk := k_ge D
  have hx : 1 ≤ s.x ^ (Scale.A / 2) :=
    Real.one_le_rpow s.one_lt_alt.le (by norm_num [Scale.A])
  have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * s.x ^ (Scale.A / 2) := by nlinarith
  have hpos : 0 < (D.R.k : ℝ) * s.x ^ (Scale.A / 2) := by linarith
  unfold thW
  exact ⟨one_div_pos.mpr hpos, one_div_le_one_div_of_le (by norm_num) h5⟩

theorem inWin_le {a b : HH D → ℤ} (h : InWin L a b) {t : HH D} (ht : t ∈ D.host.TT) :
    (a t : ℝ) ≤ L.sc.a * (1 + thW D L.sc) := by
  have h1 := (h t ht).2.1
  unfold thW
  calc (a t : ℝ) ≤ L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := h1
    _ = L.sc.a * (1 + 1 / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))) := by ring

theorem ask_bounds (P : ParameterChoice' D L) (X : Inst D L) {a b : HH D → ℤ} (h : InWin L a b) (p : ℕ) (hp : p.Prime) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (s : HH D)
    (hs : s ∈ D.host.TT) : 0 ≤ askG X a b p j s ∧ askG X a b p j s ≤ 3 * L.sc.a / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨hS100, hS5⟩ := Sc_facts P
  have hbT : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (h t ht).2.2
  have hfG : ∀ z, 0 ≤ fillG X b j z := fun z => by
    have := fillG_ge P X b hbT j hj z
    linarith
  have hapos := scale_a_pos' L.sc
  have has0 : 0 ≤ (a s : ℝ) := by linarith [(h s hs).1]
  have hn0 : ¬ Odd (0 : ℕ) := by
    rintro ⟨m, hm⟩
    omega
  have h0 : ∀ e : ℕ, 0 ≤ (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e -
      fillG X b j (partner D p s e)) else 0) := by
    intro e
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hz : (if Odd 0 then max 0 ((a s : ℝ) / (p : ℝ) ^ 0 -
      fillG X b j (partner D p s 0)) else 0) = 0 := if_neg hn0
  have h1 : ∀ e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e -
      fillG X b j (partner D p s e)) else 0) ≤ (a s : ℝ) / (p : ℝ) ^ e := by
    intro e
    split_ifs
    · exact max_le (div_nonneg has0 (by positivity)) (by linarith [hfG (partner D p s e)])
    · exact div_nonneg has0 (by positivity)
  obtain ⟨_, hle⟩ := summable_and_tsum_le_two_mul_div_of_le_div_pow (p : ℝ) (a s : ℝ) hp2 _ h0 hz h1
  have hθ := thW_bounds D L.sc
  have haw := inWin_le h hs
  refine ⟨tsum_nonneg h0, ?_⟩
  have h6 : 2 * (a s : ℝ) ≤ 3 * L.sc.a := by
    nlinarith [mul_le_mul_of_nonneg_left hθ.2 hapos.le]
  calc askG X a b p j s ≤ 2 * (a s : ℝ) / p := hle
    _ ≤ 3 * L.sc.a / p := by
      apply div_le_div_of_nonneg_right h6
      positivity

theorem X''_eq (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.w'' n * s.X'' n = s.a := by
  have hw := (sc_w''_pos s n hn).ne'
  unfold Scale.X''
  field_simp

def thS (L : SizeData₂ D) : ℝ := thW D L.sc + 3 * L.Sc / L.sc.w'' D.R.n

theorem thS_bounds (P : ParameterChoice' D L) : thW D L.sc ≤ thS L ∧ thS L ≤ 4 / 5 := by
  obtain ⟨h100, h5⟩ := Sc_facts P
  have hθ := thW_bounds D L.sc
  have hW : 0 < L.sc.w'' D.R.n := by linarith
  have hq0 : 0 ≤ 3 * L.Sc / L.sc.w'' D.R.n := div_nonneg (by linarith) hW.le
  have hq1 : 3 * L.Sc / L.sc.w'' D.R.n ≤ 3 / 5 := by
    rw [div_le_iff₀ hW]
    linarith
  unfold thS
  constructor <;> linarith [hθ.2]

theorem thS_key (P : ParameterChoice' D L) :
    L.sc.w'' D.R.n * (1 + thW D L.sc) ≤ (L.sc.w'' D.R.n - L.Sc) * (1 + thS L) := by
  obtain ⟨h100, h5⟩ := Sc_facts P
  have hθ := thW_bounds D L.sc
  have hW : 0 < L.sc.w'' D.R.n := by linarith
  have hSc : 0 ≤ L.Sc := by linarith
  have hq : 3 * L.Sc / L.sc.w'' D.R.n * L.sc.w'' D.R.n = 3 * L.Sc := div_mul_cancel₀ _ hW.ne'
  have hq1 : 3 * L.Sc / L.sc.w'' D.R.n ≤ 3 / 5 := by
    rw [div_le_iff₀ hW]
    linarith
  unfold thS
  nlinarith [mul_le_mul_of_nonneg_left hθ.2 hSc, mul_le_mul_of_nonneg_left hq1 hSc]

private lemma scale_b_le_a (s : Scale) : s.b ≤ s.a := by
  have hb := scale_b_pos s
  have h := mul_pos (sub_pos.mpr s.one_lt_alt) hb
  unfold Scale.a
  nlinarith

theorem ask_high (P : ParameterChoice' D L) (X : Inst D L) {a b : HH D → ℤ} (h : InWin L a b) (p : ℕ)
    (hpX : L.sc.X'' D.R.n < (p : ℝ)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : HH D) (hs : s ∈ D.host.TT) :
    askG X a b p j s ≤
      if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0 := by
  obtain ⟨hS100, hS5⟩ := Sc_facts P
  have hn := n_pos D
  have hW : 0 < L.sc.w'' D.R.n := sc_w''_pos L.sc D.R.n hn
  have hθ := thW_bounds D L.sc
  have hkey := thS_key P
  have hapos := scale_a_pos' L.sc
  have hXa := X''_eq L.sc D.R.n hn
  have hX : 0 < L.sc.X'' D.R.n := by
    unfold Scale.X''
    exact div_pos hapos hW
  have hX1 : 1 ≤ L.sc.X'' D.R.n := by
    have h1 := scale_w_double_prime_le_b_prime_div_x_of_one_le L.sc D.R.n hn
    have h2 := scale_b_prime_div_x_le_b L.sc
    have h3 := scale_b_le_a L.sc
    unfold Scale.X''
    rw [le_div_iff₀ hW]
    linarith
  have hp : (0 : ℝ) < p := lt_trans hX hpX
  have hp2 : (2 : ℝ) ≤ p := by
    have h1 : (1 : ℝ) < p := lt_of_le_of_lt hX1 hpX
    have h2 : 1 < p := by exact_mod_cast h1
    have h3 : 2 ≤ p := by omega
    exact_mod_cast h3
  have hbT : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (h t ht).2.2
  have hfG : ∀ z, L.sc.w'' D.R.n - L.Sc ≤ fillG X b j z := fun z => fillG_ge P X b hbT j hj z
  have haw := inWin_le h hs
  have has0 : 0 ≤ (a s : ℝ) := by linarith [(h s hs).1]
  have hap0 : (a s : ℝ) ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) * p := by
    have hc : 0 < L.sc.w'' D.R.n * (1 + thW D L.sc) := mul_pos hW (by linarith [hθ.1])
    have h1 := mul_lt_mul_of_pos_left hpX hc
    calc (a s : ℝ) ≤ L.sc.a * (1 + thW D L.sc) := haw
      _ = L.sc.w'' D.R.n * (1 + thW D L.sc) * L.sc.X'' D.R.n := by rw [← hXa]; ring
      _ ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) * p := h1.le
  have hsingle : ∀ e : ℕ, e ≠ 1 → (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e -
      fillG X b j (partner D p s e)) else 0) = 0 := by
    intro e he
    split_ifs with ho
    · refine le_antisymm ?_ (le_max_left _ _)
      apply max_le le_rfl
      have he3 : 3 ≤ e := by
        obtain ⟨m, hm⟩ := ho
        omega
      have hpe : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ e := pow_le_pow_right₀ (by linarith) he3
      have hp3 : 4 * (p : ℝ) ≤ (p : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ p - 2))
          (by linarith : (0 : ℝ) ≤ p + 2)]
      have hwp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ.2 hW.le) hp.le
      have hle : (a s : ℝ) ≤ (L.sc.w'' D.R.n - L.Sc) * (p : ℝ) ^ e := by
        calc (a s : ℝ) ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) * p := hap0
          _ ≤ (4 / 5 * L.sc.w'' D.R.n) * (4 * p) := by nlinarith [mul_pos hW hp]
          _ ≤ (L.sc.w'' D.R.n - L.Sc) * (p : ℝ) ^ e :=
            mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
      have h2 : (a s : ℝ) / (p : ℝ) ^ e ≤ L.sc.w'' D.R.n - L.Sc := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith [hfG (partner D p s e)]
    · rfl
  unfold askG
  rw [tsum_eq_single 1 hsingle, if_pos odd_one, pow_one]
  split_ifs with hlt
  · apply max_le (add_nonneg (mul_nonneg hθ.1.le hW.le) (by linarith))
    have h2 : (a s : ℝ) / p ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) := by
      rw [div_le_iff₀ hp]
      exact hap0
    linarith [hfG (partner D p s 1)]
  · push_neg at hlt
    apply max_le le_rfl
    have hθS := thS_bounds P
    have h1 : (a s : ℝ) ≤ (L.sc.w'' D.R.n - L.Sc) * p := by
      calc (a s : ℝ) ≤ L.sc.a * (1 + thW D L.sc) := haw
        _ = L.sc.X'' D.R.n * (L.sc.w'' D.R.n * (1 + thW D L.sc)) := by rw [← hXa]; ring
        _ ≤ L.sc.X'' D.R.n * ((L.sc.w'' D.R.n - L.Sc) * (1 + thS L)) :=
          mul_le_mul_of_nonneg_left hkey hX.le
        _ = (L.sc.w'' D.R.n - L.Sc) * (L.sc.X'' D.R.n * (1 + thS L)) := by ring
        _ ≤ (L.sc.w'' D.R.n - L.Sc) * p := mul_le_mul_of_nonneg_left hlt (by linarith)
    have h2 : (a s : ℝ) / p ≤ L.sc.w'' D.R.n - L.Sc := by
      rw [div_le_iff₀ hp]
      linarith
    linarith [hfG (partner D p s 1)]

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

theorem ceil_bound (S B R : ℝ) (hSB : S ≤ B) (h : (B = 0 ∧ R = 0) ∨ B + 1 ≤ R) : ((⌈S⌉ : ℤ) : ℝ) ≤ R := by
  rcases h with ⟨hB, hR⟩ | h
  · have h1 : ⌈S⌉ ≤ 0 := Int.ceil_le.2 (by rw [Int.cast_zero]; linarith)
    have h2 : ((⌈S⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h1
    linarith
  · have := Int.ceil_lt_add_one S
    linarith

theorem fin_arith (m N q : ℝ) (hm : 2 ≤ m) (hN : 1 ≤ N) (hq : 500 ≤ q) :
    m * (8 / 5 * (N * q)) + 1 ≤ 2 * (m * (N * q)) := by
  have h2 : 500 ≤ N * q := by nlinarith
  have h3 : 1000 ≤ m * (N * q) := by nlinarith
  linarith

set_option maxHeartbeats 800000 in
theorem sv_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) {a b : HH D → ℤ} (h : InWin L a b) (p : ℕ)
    (hp : p.Prime) (hpX : (p : ℝ) < L.sc.X') (t0 : HH D) :
    Sv X K a b p t0 ≤ 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hdl1, hdl2, hPr1, hPr2⟩ := hK
  obtain ⟨hk, hN, hSc⟩ := Nm_le_Sc P
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n hn
  have hkS := P.kS_le
  have hab := two_b'_le_a L.sc
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hb' := sc_b'_nonneg L.sc
  have hw0 := sc_w''_nonneg L.sc D.R.n
  have hη := L.etaSz_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk (by linarith)
  have hw500 : 500 ≤ L.sc.w'' D.R.n := by linarith
  have hlg : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  have hTT : ∀ s ∈ topsOn X p t0, s ∈ D.host.TT := fun s hs => (Finset.mem_filter.1 hs).1

  have hal : ∀ s ∈ topsOn X p t0, 0 ≤ al L a s ∧ al L a s ≤ 6 / 5 * L.sc.a := by
    intro s hs
    obtain ⟨h2, h3, _⟩ := h s (hTT s hs)
    have h4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
      have : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
      nlinarith
    unfold al cG
    constructor <;> linarith
  have hdl : 0 ≤ dl X K p t0 := by
    unfold dl
    have h1 : 0 ≤ K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) :=
      mul_nonneg (mul_nonneg (mul_nonneg hdl1 (Nat.cast_nonneg _)) (by positivity)) hlg
    have h2 : 0 ≤ K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 :=
      mul_nonneg (mul_nonneg hdl2 (Nat.cast_nonneg _)) (by positivity)
    linarith
  have hgU : ∀ j ∈ SizeData₂.lifts D,
      gU X K a b p j t0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s := by
    intro j hj
    unfold gU
    refine le_trans (sub_le_self _ hdl) (sub_le_self _ ?_)
    apply Finset.sum_nonneg
    intro s hs
    apply tsum_nonneg
    intro e
    split_ifs
    · apply le_min
      · exact div_nonneg (hal s (Finset.mem_filter.1 hs).1).1 (by positivity)
      · unfold capU fillG cG
        have := fill_ge X b (fun t ht => (h t ht).2.2) j (partner D p s e)
        have := kaJ_le P j hj
        linarith
    · exact le_rfl
  have hbase : 0 ≤ L.sc.w'' D.R.n + L.etaSz + cG L + Nm D := by linarith
  have hPr : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Pr X K b p j t0 := by
    intro j hj
    unfold Pr
    split_ifs with h0
    · apply add_nonneg
      · apply Finset.sum_nonneg
        intro s hs
        have hs' := hTT s (Finset.mem_filter.1 hs).1
        have h1 : fill X b j (false, s) = (b s : ℝ) + X.off j (false, s) := by
          unfold fill
          rw [if_pos ⟨rfl, hs'⟩]
        have h2 := (X.off_top j (false, s) ⟨rfl, hs'⟩).1
        have h3 := kaJ_le P j hj
        unfold fillG
        rw [h1]
        linarith
      · exact mul_nonneg (mul_nonneg hPr1 (Nat.cast_nonneg _)) hbase
    · exact mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hbase))
  have hgam : 0 ≤ gam p ∧ gam p * L.sc.a ≤ 4 / 3 * (L.sc.a / p) := by
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hd : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by linarith
    unfold gam
    refine ⟨div_nonneg hp0.le hd.le, ?_⟩
    have h1 : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 4 / 3 * (1 / p) := by
      rw [div_le_iff₀ hd]
      field_simp
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L.sc.a)
    calc (p : ℝ) / ((p : ℝ) ^ 2 - 1) * L.sc.a ≤ 4 / 3 * (1 / p) * L.sc.a := h2
      _ = 4 / 3 * (L.sc.a / p) := by ring
  have hsum : ∑ s ∈ topsOn X p t0, al L a s ≤ (Nv X p t0 : ℝ) * (6 / 5 * L.sc.a) := by
    unfold Nv
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun s hs => (hal s hs).2)
  set q : ℝ := L.sc.a / p with hq
  have hq0 : L.sc.b' ≤ q := by
    have hX : 0 < L.sc.X' := by unfold Scale.X'; exact Real.exp_pos _
    rw [hq]
    unfold Scale.b'
    exact div_le_div_of_nonneg_left (by linarith) hp0 hpX.le
  have hterm : ∀ j ∈ SizeData₂.lifts D,
      max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0) ≤
        8 / 5 * ((Nv X p t0 : ℝ) * q) := by
    intro j hj
    have hNv : (0 : ℝ) ≤ (Nv X p t0 : ℝ) := Nat.cast_nonneg _
    have h1 := hgU j hj
    have h2 := hPr j hj
    have h3 : 0 ≤ max (g0 X K a b p j t0) 0 := le_max_right _ _
    have h4 := mul_le_mul_of_nonneg_left hsum hgam.1
    have h5 := mul_le_mul_of_nonneg_left hgam.2 hNv
    have h6 : 0 ≤ (Nv X p t0 : ℝ) * q := mul_nonneg hNv (by linarith)
    apply max_le (by linarith)
    nlinarith
  have htot : ∑ j ∈ SizeData₂.lifts D,
      max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0) ≤
        (D.R.m : ℝ) * (8 / 5 * ((Nv X p t0 : ℝ) * q)) := by
    have h := Finset.sum_le_card_nsmul _ _ _ hterm
    have hc : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp
    rw [hc, nsmul_eq_mul] at h
    exact h
  have hR : 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p = 2 * ((D.R.m : ℝ) * ((Nv X p t0 : ℝ) * q)) := by
    rw [hq]; ring
  rw [hR]
  unfold Sv
  apply ceil_bound _ _ _ htot
  rcases Nat.eq_zero_or_pos (Nv X p t0) with h0 | h0
  · left
    have h0' : (Nv X p t0 : ℝ) = 0 := by exact_mod_cast h0
    rw [h0']
    constructor <;> ring
  · right
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    have hNv : (1 : ℝ) ≤ (Nv X p t0 : ℝ) := by exact_mod_cast h0
    have hq500 : 500 ≤ q := le_trans hw500 (le_trans hw1 (le_trans hw2 hq0))
    exact fin_arith _ _ _ hm hNv hq500

def c1 (L : SizeData₂ D) (C : ℝ) : ℝ := C * (cG L + L.etaSz) * Real.log (2 * L.sc.a)
def c2 (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x +
    C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹))
def c3 (L : SizeData₂ D) (C bo : ℝ) : ℝ :=
  L.sc.b' / L.sc.x + L.etaSz + C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 + bo
def c4 (K : Consts) (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k + L.sc.a / L.sc.p0 D.R.k)
def cfl (D : D7) (s : Scale) (C : ℝ) : ℝ :=
  C * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log s.a + Real.log s.a ^ 2 / Real.log 2)

theorem logx_nonneg (s : Scale) : 0 ≤ Real.log s.x := Real.log_nonneg s.one_lt_alt.le

theorem La_nonneg (K : Consts) (hK : 0 ≤ K.La) (s : Scale) : 0 ≤ La K s := by
  unfold La
  exact mul_nonneg (mul_nonneg hK (by positivity)) (Real.log_nonneg (sc_one_lt_a s).le)

theorem p0_pos (D : D7) (s : Scale) : 0 < s.p0 D.R.k := by
  have := k_ge D
  have := sc_x_pos s
  unfold Scale.p0
  positivity

theorem third_constant_nonneg (L : SizeData₂ D) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo) : 0 ≤ c3 L C bo := by
  unfold c3
  have h1 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (sc_b'_nonneg _) (sc_x_pos _).le
  have h2 := L.etaSz_pos
  have h3 : 0 ≤ C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
    div_nonneg (mul_nonneg (mul_nonneg hC (sc_w''_nonneg _ _)) (logx_nonneg _)) (sc_delta1_pos _).le
  linarith

theorem prime_rpow_neg_level_le (D : D7) (s : Scale) (p : ℕ) (hp : p.Prime) :
    (p : ℝ) ^ (-(L1 D s p : ℝ)) ≤ (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hk := k_ge D
  have hx := sc_x_pos s
  have hY : 0 < ((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4 := by positivity
  rw [Real.rpow_neg hp0.le]
  apply inv_anti₀ hY
  calc ((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4 = (p : ℝ) ^ Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4) :=
        (Real.rpow_logb hp0 hp1.ne' hY).symm
    _ ≤ (p : ℝ) ^ (L1 D s p : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hp1.le
        unfold L1
        exact Nat.le_ceil _

theorem lo_bounds (K : Consts) (hK : 0 ≤ K.La) (L : SizeData₂ D) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo) (p : ℕ) (hp : p.Prime)
    (hc0 : IsResidueClassZero D p) :
    0 ≤ lo K L C bo p ∧
    Real.log p * lo K L C bo p ≤ c1 L C + (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) * c2 L C +
      (if p ∈ prB L.sc.X' then Real.log p else 0) * c3 L C bo +
      (if p ∈ prB L.sc.X' then Real.log p / p else 0) * c4 K L C := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hl : 0 < Real.log p := Real.log_pos hp1
  have hk := k_ge D
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have ha0 : 0 < L.sc.a := by linarith
  have hlx := logx_nonneg L.sc
  have hLa := La_nonneg K hK L.sc
  have hP0 := p0_pos D L.sc
  have hc3 := third_constant_nonneg L C bo hC hbo
  have hb' := sc_b'_nonneg L.sc
  have hcG : 0 ≤ cG L := by unfold cG; have := L.Sc_pos; linarith
  have hη := L.etaSz_pos
  have hlg : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hcp0 : 0 ≤ C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) :=
    mul_nonneg (mul_nonneg hC (by linarith)) hlg
  have hcp : Real.log p * (C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)) = c1 L C := by
    unfold c1 Real.logb
    field_simp
  have hu : 0 ≤ C * Real.log L.sc.x := mul_nonneg hC hlx
  have hr : 0 ≤ C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hb') hlx
  have hY : 0 < ((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4 := by positivity
  have hPL := prime_rpow_neg_level_le D L.sc p hp
  have hPL0 : 0 ≤ (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) := Real.rpow_nonneg hp0.le _
  have hc2 : 0 ≤ c2 L C := by
    unfold c2
    have : 0 ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
      mul_nonneg hu (mul_nonneg ha0.le (inv_nonneg.2 hY.le))
    linarith
  have hc4a : 0 ≤ C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k) :=
    mul_nonneg hu (div_nonneg (mul_nonneg hLa ha0.le) hk0.le)
  have hc4b : 0 ≤ C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k) := mul_nonneg hu (div_nonneg ha0.le hP0.le)
  have hc4 : c4 K L C = C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k) +
      C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k) := by unfold c4; ring
  have hlp : 0 ≤ Real.log p / p := div_nonneg hl.le hp0.le
  have hLaT : Real.log p * (C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))) =
      Real.log p / p * (C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k)) := by
    field_simp
  have hLaT0 : 0 ≤ C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) :=
    mul_nonneg hu (div_nonneg (mul_nonneg hLa ha0.le) (by positivity))
  by_cases h1 : (p : ℝ) < L.sc.p0 D.R.k
  · have m1 : p ∈ prB (L.sc.p0 D.R.k) := mem_prB.2 ⟨hp, h1⟩
    by_cases h2 : (p : ℝ) < L.sc.X'
    · have m2 : p ∈ prB L.sc.X' := mem_prB.2 ⟨hp, h2⟩
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
          C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x +
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) := by
        unfold lo
        simp only [if_pos hc0, if_pos h1, if_pos (And.intro hc0 h2)]
      have t1 : C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) ≤
          C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPL ha0.le) hu
      have t0 : 0 ≤ C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) :=
        mul_nonneg hu (mul_nonneg ha0.le hPL0)
      rw [e, if_pos m1, if_pos m2, if_pos m2]
      constructor
      · have : C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) =
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
          C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) := by ring
        linarith
      · have t1' := mul_le_mul_of_nonneg_left t1 hl.le
        have t3 := mul_nonneg hl.le hc3
        have t4 := mul_nonneg hlp hc4b
        rw [hc4]
        unfold c2
        linarith [hcp, hLaT, t1', t3, t4]
    · have m2 : p ∉ prB L.sc.X' := fun h => h2 (mem_prB.1 h).2
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
          C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x + 0 := by
        unfold lo
        simp only [if_pos hc0, if_pos h1, if_neg (fun h : IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' => h2 h.2)]
      rw [e, if_pos m1, if_neg m2, if_neg m2]
      constructor
      · linarith
      · have t2 : 0 ≤ Real.log p * (C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹))) :=
          mul_nonneg hl.le (mul_nonneg hu (mul_nonneg ha0.le (inv_nonneg.2 hY.le)))
        unfold c2
        linarith [hcp, t2]
  · have m1 : p ∉ prB (L.sc.p0 D.R.k) := fun h => h1 (mem_prB.1 h).2
    by_cases h2 : (p : ℝ) < L.sc.X'
    · have m2 : p ∈ prB L.sc.X' := mem_prB.2 ⟨hp, h2⟩
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + c3 L C bo +
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2) := by
        unfold lo c3
        simp only [if_pos hc0, if_neg h1, if_pos h2, if_pos (And.intro hc0 h2)]
      have hpp : L.sc.a / (p : ℝ) ^ 2 ≤ 1 / p * (L.sc.a / L.sc.p0 D.R.k) := by
        rw [div_mul_div_comm, one_mul]
        apply div_le_div_of_nonneg_left ha0.le (by positivity)
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (not_lt.1 h1) hp0.le
      have t0 : 0 ≤ C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2) := mul_nonneg hu (by positivity)
      have t1 : Real.log p * (C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2)) ≤
          Real.log p / p * (C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k)) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpp hu) hl.le
        calc _ ≤ Real.log p * (C * Real.log L.sc.x * (1 / p * (L.sc.a / L.sc.p0 D.R.k))) := this
          _ = _ := by ring
      rw [e, if_neg m1, if_pos m2, if_pos m2]
      constructor
      · have : C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2) =
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
          C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2) := by ring
        linarith
      · rw [hc4]
        linarith [hcp, hLaT, t1]
    · have m2 : p ∉ prB L.sc.X' := fun h => h2 (mem_prB.1 h).2
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + 0 + 0 := by
        unfold lo
        simp only [if_pos hc0, if_neg h1, if_neg h2, if_neg (fun h : IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' => h2 h.2)]
      rw [e, if_neg m1, if_neg m2, if_neg m2]
      constructor
      · linarith
      · linarith [hcp]

theorem fl_bounds (D : D7) (s : Scale) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) :
    0 ≤ fl D s C p ∧ Real.log p * fl D s C p ≤ cfl D s C := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 < Real.log p := Real.log_pos hp1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have ha := sc_one_lt_a s
  have hla : 0 ≤ Real.log s.a := Real.log_nonneg ha.le
  have hlb : 0 ≤ Real.logb p s.a := Real.logb_nonneg hp1 ha.le
  have hCf : 0 ≤ C * (D.R.f : ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
  constructor
  · unfold fl
    have h1 : 0 ≤ C * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a := mul_nonneg (mul_nonneg hCf (by positivity)) hlb
    have h2 : 0 ≤ C * (D.R.f : ℝ) * Real.logb p s.a ^ 2 := mul_nonneg hCf (by positivity)
    linarith
  · have e : Real.log p * fl D s C p = C * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log s.a + Real.log s.a ^ 2 / Real.log p) := by
      unfold fl Real.logb
      field_simp
    rw [e]
    unfold cfl
    apply mul_le_mul_of_nonneg_left _ hCf
    have : Real.log s.a ^ 2 / Real.log p ≤ Real.log s.a ^ 2 / Real.log 2 :=
      div_le_div_of_nonneg_left (by positivity) hl2 hl2p
    linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

open Classical in

def dropI (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then 1 else 0

theorem dropI_nonneg (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : 0 ≤ dropI X K a b p := by
  unfold dropI; split_ifs <;> norm_num

theorem WReq_iff (X : Inst D L) (K : Consts) (a b : HH D → ℤ) :
    WReq X K a b ↔ ∑ p ∈ candF D L K, Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) ≤
      L.sc.x ^ (-9 : ℝ) := Iff.rfl

theorem mem_candF {K : Consts} {p : ℕ} (h : Cand D L K p) : p ∈ candF D L K := by
  classical
  unfold candF
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 h.2.1), h⟩

theorem cand_of_mem {K : Consts} {p : ℕ} (h : p ∈ candF D L K) : Cand D L K p := by
  classical
  unfold candF at h
  exact (Finset.mem_filter.1 h).2

theorem lp_nonneg (p : ℕ) : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem lifts_card (D : D7) : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp

def Dfc (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) -
    ((∑ j ∈ SizeData₂.lifts D, gainP X K a b p j) - tauP X K a b p - ioP X K a b p)

theorem io_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) {a b : HH D → ℤ} (h : InWin L a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p) (p : ℕ) :
    Real.log p * ioP X K a b p ≤
      (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
        (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
  classical
  have ha := sc_one_lt_a L.sc
  unfold ioP
  split_ifs with hne hc hc
  · have hC := cand_of_mem hc
    have hp := hC.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hs := hSig p hC
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hsup : (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤
        2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p := by
      apply Finset.sup'_le
      intro t0 _
      refine le_trans (sv_le X K hK P h p hp hC.2.1 t0) ?_
      rw [div_le_div_iff_of_pos_right hp0]
      have hN : (Nv X p t0 : ℝ) ≤ (D.host.TT.card : ℝ) := by
        unfold Nv topsOn
        exact_mod_cast Finset.card_filter_le _ _
      have hm : (0 : ℝ) ≤ 2 * (D.R.m : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hN hm
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h1 : 2 * Sig X K a b p * (VV X K a b p).sup' hne (fun t0 => Sv X K a b p t0) ≤
        2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p) :=
      mul_le_mul_of_nonneg_left hsup (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 hl
    refine le_trans h2 ?_
    have hd := dropI_nonneg X K a b p
    have h3 : 0 ≤ Real.log p / p * dropI X K a b p * (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
      have := lp_nonneg p
      positivity
    have e : Real.log p * (2 * Sig X K a b p * (2 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / p)) =
        Real.log p / p * Sig X K a b p * (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
      field_simp
      ring
    rw [e]
    linarith
  · exact absurd (mem_candF (cand_of_VV_ne X K a b p (Finset.nonempty_iff_ne_empty.1 hne))) hc
  · have hC := cand_of_mem hc
    have := hSig p hC
    have := dropI_nonneg X K a b p
    have := lp_nonneg p
    rw [mul_zero]
    positivity
  · simp

theorem not_singular_of_central {p : ℕ} (h : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro h'
  unfold IsResidueClassZero at h
  unfold IsSg at h'
  rw [h] at h'
  cases h'

theorem TTP_subset (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

theorem sdiff_le (X : Inst D L) (K : Consts) {a b : HH D → ℤ}
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ)
    (hA3 : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → (p : ℝ) < L.sc.X' →
      (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) → p ∈ A3)
    (hA4 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → InBand D K L.sc p → p ∈ A4)
    (hPS : ∀ p, Cand D L K p → p ∈ PS)
    (hbad : ∀ p, Cand D L K p →
      ((D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)).card : ℝ) ≤ badf p)
    (hbad0 : ∀ p, 0 ≤ badf p) (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) :
    Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ) ≤
      (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) +
      (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) +
      (if p ∈ PS then Real.log p / p * badf p else 0) +
      (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) * (D.host.TT.card : ℝ) := by
  classical
  have hlp := lp_nonneg p
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have t3 : 0 ≤ (if p ∈ A3 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by
    split_ifs <;> positivity
  have t4 : 0 ≤ (if p ∈ A4 then Real.log p / p else 0) * (D.host.TT.card : ℝ) := by
    split_ifs <;> positivity
  have t2 : 0 ≤ (if p ∈ PS then Real.log p / p * badf p else 0) := by
    split_ifs
    · exact mul_nonneg hlp (hbad0 p)
    · exact le_rfl
  have t8 : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
      (D.host.TT.card : ℝ) := by
    split_ifs with hc
    · have := hSig p (cand_of_mem hc)
      have := dropI_nonneg X K a b p
      positivity
    · simp
  have hall : ((D.host.TT \ TTP X K a b p).card : ℝ) ≤ (D.host.TT.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hall' := mul_le_mul_of_nonneg_left hall hlp
  by_cases hX : (p : ℝ) < L.sc.X'
  · by_cases ho : (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)
    · rw [if_pos (hA3 p hp hc0 hX ho)] at t3 ⊢
      linarith
    · by_cases hb : L.sc.p0 D.R.k ≤ (p : ℝ) ∧ InBand D K L.sc p
      · rw [if_pos (hA4 p hp hX hb.2)] at t4 ⊢
        linarith
      · have hC : Cand D L K p := ⟨hp, hX, hc0, not_lt.1 ho, fun h1 h2 => hb ⟨h1, h2⟩⟩
        have hs := hSig p hC
        by_cases hd : Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps)
        · have hVV : VV X K a b p = goodReps X p := by unfold VV; rw [if_pos ⟨hC, hd⟩]
          have hT : TTP X K a b p = D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p) := by
            unfold TTP
            rw [if_neg (by
              intro h
              rcases h with h | h
              · exact not_singular_of_central hc0 h
              · linarith), hVV]
          rw [hT, if_pos (hPS p hC)] at *
          have := mul_le_mul_of_nonneg_left (hbad p hC) hlp
          linarith
        · have hdI : dropI X K a b p = 1 := by unfold dropI; rw [if_pos (not_le.1 hd)]
          rw [if_pos (mem_candF hC), hdI] at t8 ⊢
          have : Real.log p / p * (D.host.TT.card : ℝ) ≤
              Real.log p / p * (2 * 1 + 4 * Sig X K a b p) * (D.host.TT.card : ℝ) := by
            have h1 : Real.log p / p ≤ Real.log p / p * (2 * 1 + 4 * Sig X K a b p) := by nlinarith
            exact mul_le_mul_of_nonneg_right h1 hN
          linarith
  · have hT : TTP X K a b p = D.host.TT := by
      unfold TTP
      rw [if_pos (Or.inr (not_lt.1 hX))]
    rw [hT, Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero]
    linarith

theorem dfc_le (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C bo : ℝ) {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) (hlo : 0 ≤ lo K L C bo p) :
    Dfc X K a b p ≤ (D.R.m : ℝ) * (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)) +
      (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * lo K L C bo p) + (D.R.m : ℝ) * fl D L.sc C p + ioP X K a b p := by
  classical
  have g := (hG p hp (Or.inl hc0) hpX).2
  have hsub := TTP_subset X K a b p
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤
      ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L C bo p) +
        (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) + (D.host.TT.card : ℝ) * lo K L C bo p) := by
    intro j hjl
    rw [← Finset.sum_sdiff hsub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : ∑ s ∈ D.host.TT \ TTP X K a b p, askG X a b p j s ≤
        ((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p) := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro s hs
      exact (ask_bounds P X h p hp j hjl s (Finset.mem_sdiff.1 hs).1).2
    have h2 : ((TTP X K a b p).card : ℝ) * lo K L C bo p ≤ (D.host.TT.card : ℝ) * lo K L C bo p := by
      apply mul_le_mul_of_nonneg_right _ hlo
      exact_mod_cast Finset.card_le_card hsub
    linarith
  have hs := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_const, lifts_card, nsmul_eq_mul] at hs
  unfold Dfc
  linarith

theorem dfc_high (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) {a b : HH D → ℤ} (h : InWin L a b)
    (p : ℕ) (hpX : L.sc.X'' D.R.n < (p : ℝ)) :
    Dfc X K a b p ≤ (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
      (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0)) := by
  classical
  have hVV : VV X K a b p = ∅ := by
    by_contra hne
    have hC := cand_of_VV_ne X K a b p hne
    have := X'_le_X'' L.sc D.R.n (n_pos D)
    have := hC.2.1
    linarith
  have hg : ∀ j, gainP X K a b p j = 0 := by
    intro j; unfold gainP; rw [if_pos (Or.inr hpX)]
  have ht : tauP X K a b p = 0 := by unfold tauP; rw [if_pos hVV]
  have hi : ioP X K a b p = 0 := by
    unfold ioP; rw [dif_neg (by rw [hVV]; simp)]
  unfold Dfc
  rw [ht, hi]
  simp only [hg, Finset.sum_const_zero, sub_zero]
  have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ (D.host.TT.card : ℝ) *
      (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0) := by
    intro j hjl
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro s hs
    exact ask_high P X h p hpX j hjl s hs
  have hs := Finset.sum_le_card_nsmul _ _ _ hj
  rw [lifts_card, nsmul_eq_mul] at hs
  exact hs

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

def lX (s : Scale) : ℝ := Real.log s.X' * (1 + Real.log s.X')

structure PrimeSumNumericFacts (D : D7) (L : SizeData₂ D) (K : Consts) (C bo : ℝ) : Prop where

  one_le_card_tops : (1 : ℝ) ≤ (D.host.TT.card : ℝ)

  n1 : c1 L C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x / 40

  n1' : cfl D L.sc C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x / 40

  n2 : Real.log 4 * L.sc.p0 D.R.k * c2 L C ≤ L.sc.a / L.sc.x / 40

  n3 : Real.log 4 * L.sc.X' * c3 L C bo ≤ 3 / 2 * (L.sc.a / L.sc.x)

  n4 : lX L.sc * c4 K L C ≤ L.sc.a / L.sc.x / 40

  n5 : 120 ≤ L.sc.x

  n7 : L.sc.x ^ (-2 + L.sc.eps) ≤ 1 / L.sc.x / 120

  n9 : (L.sc.X'' D.R.n * thS L + 2) * (Real.log (2 * L.sc.X'' D.R.n) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) ≤
    L.sc.a / L.sc.x / 40

theorem first_constant_nonneg (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c1 L C := by
  unfold c1 cG
  have := L.Sc_pos
  have := L.etaSz_pos
  have ha := sc_one_lt_a L.sc
  exact mul_nonneg (mul_nonneg hC (by linarith)) (Real.log_nonneg (by linarith))

theorem second_constant_nonneg (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c2 L C := by
  unfold c2
  have hk := k_ge D
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hlx := logx_nonneg L.sc
  have hb' := sc_b'_nonneg L.sc
  have h1 : 0 ≤ C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hb') hlx
  have h2 : 0 ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
    mul_nonneg (mul_nonneg hC hlx) (mul_nonneg (by linarith) (by positivity))
  linarith

theorem fourth_constant_nonneg (K : Consts) (hK : 0 ≤ K.La) (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c4 K L C := by
  unfold c4
  have hk := k_ge D
  have ha := sc_one_lt_a L.sc
  have hLa := La_nonneg K hK L.sc
  have hP0 := p0_pos D L.sc
  exact mul_nonneg (mul_nonneg hC (logx_nonneg _))
    (add_nonneg (div_nonneg (mul_nonneg hLa (by linarith)) (by linarith)) (div_nonneg (by linarith) hP0.le))

theorem cfl_nonneg (D : D7) (s : Scale) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ cfl D s C := by
  unfold cfl
  have hla : 0 ≤ Real.log s.a := Real.log_nonneg (sc_one_lt_a s).le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (add_nonneg (mul_nonneg (by positivity) hla) (by positivity))

theorem one_le_X' (s : Scale) : 1 ≤ s.X' := by
  unfold Scale.X'; exact Real.one_le_exp (Real.rpow_nonneg (sc_x_pos s).le _)

structure Sets (X : Inst D L) (K : Consts) (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) : Prop where
  hA3 : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → (p : ℝ) < L.sc.X' →
      (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) → p ∈ A3
  hA4 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → InBand D K L.sc p → p ∈ A4
  hPS : ∀ p, Cand D L K p → p ∈ PS
  hPSsub : PS ⊆ prB L.sc.X'
  hbad : ∀ p, Cand D L K p →
      ((D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)).card : ℝ) ≤ badf p
  hbad0 : ∀ p, 0 ≤ badf p
  s3 : ∑ p ∈ A3, Real.log p / p ≤ L.sc.x ^ (-hG L.sc + L.sc.eps)
  s4 : ∑ p ∈ A4, Real.log p / p ≤ L.sc.x ^ (-1 : ℝ)
  s2 : ∑ p ∈ PS, Real.log p / p * badf p ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

def E1 (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ) (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) (p : ℕ) : ℝ :=
  (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) *
      ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c1 L C + (D.R.m : ℝ) * cfl D L.sc C) +
  (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c2 L C) +
  (if p ∈ prB L.sc.X' then Real.log p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c3 L C bo) +
  (if p ∈ prB L.sc.X' then Real.log p / p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c4 K L C) +
  (if p ∈ A3 then Real.log p / p else 0) * (3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) +
  (if p ∈ A4 then Real.log p / p else 0) * (3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) +
  (if p ∈ PS then Real.log p / p * badf p else 0) * (3 * (D.R.m : ℝ) * L.sc.a) +
  (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
      (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)

theorem low_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) :
    Real.log p * max 0 (Dfc X K a b p) ≤ E1 X K C bo a b A3 A4 PS badf p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha := sc_one_lt_a L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨hlo0, hlo⟩ := lo_bounds K hK.1 L C bo hC hbo p hp hc0
  obtain ⟨hfl0, hfl⟩ := fl_bounds D L.sc C hC p hp
  have hio := io_le X K hK P h hSig p
  have hsd := sdiff_le X K hSig A3 A4 PS badf T.hA3 T.hA4 T.hPS T.hbad T.hbad0 p hp hc0
  have hd := dfc_le P X K C bo h hG p hp hc0 hpX hlo0
  have m1 : p ∈ prB (L.sc.X'' D.R.n + 1) := mem_prB.2 ⟨hp, by linarith⟩
  have hsd0 : 0 ≤ Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ) :=
    mul_nonneg (lp_nonneg p) (Nat.cast_nonneg _)
  have hiob : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
        (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
    split_ifs with hc
    · have := hSig p (cand_of_mem hc)
      have := dropI_nonneg X K a b p
      have := lp_nonneg p
      positivity
    · simp
  have k1 := mul_le_mul_of_nonneg_left hsd (by positivity : (0 : ℝ) ≤ 3 * (D.R.m : ℝ) * L.sc.a)
  have k2 := mul_le_mul_of_nonneg_left hlo (mul_nonneg hm hN)
  have k3 := mul_le_mul_of_nonneg_left hfl hm
  have k4 := mul_le_mul_of_nonneg_left hd hl
  have k10 : 0 ≤ 3 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ)) :=
    mul_nonneg (by positivity) hsd0
  have k20 : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (Real.log p * lo K L C bo p) :=
    mul_nonneg (mul_nonneg hm hN) (mul_nonneg hl hlo0)
  have k30 : 0 ≤ (D.R.m : ℝ) * (Real.log p * fl D L.sc C p) := mul_nonneg hm (mul_nonneg hl hfl0)
  have e : Real.log p * ((D.R.m : ℝ) * (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)) +
      (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * lo K L C bo p) + (D.R.m : ℝ) * fl D L.sc C p + ioP X K a b p) =
      3 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ)) +
      (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (Real.log p * lo K L C bo p) +
      (D.R.m : ℝ) * (Real.log p * fl D L.sc C p) + Real.log p * ioP X K a b p := by ring
  rw [e] at k4
  rw [mul_max_of_nonneg _ _ hl, mul_zero]
  unfold E1
  rw [if_pos m1]
  apply max_le <;> linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end
