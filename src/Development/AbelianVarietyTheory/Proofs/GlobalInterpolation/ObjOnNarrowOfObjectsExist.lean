import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.FewBadPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill

noncomputable section

namespace GlobalTheory.ObjExCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

variable {R : Ranks}

theorem one_lt_condE (H : Host R) : 1 < condE H := by
  unfold condE
  exact lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

private theorem one_lt_lcm (H : Host R) : 1 < Nat.lcm 15 (condE H) :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (one_lt_condE H).le) (Nat.dvd_lcm_left 15 _))

private theorem four_dvd_cond (H : Host R) : 4 ∣ H.QS * H.q * H.d :=
  ((Dvd.dvd.trans ⟨2 ^ R.e, by ring⟩ H.tower_dvd : 4 ∣ H.QS).mul_right _).mul_right _

theorem norm_modEq (H : Host R) (π : 𝓞 H.E) {T N : ℕ} (hN : N ≠ 0)
    (hn : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h1 : π - 1 ∈ Ideal.span {((N : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD N] := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hyi : IsIntegral ℤ (a : H.E) := RingOfIntegers.isIntegral_coe a
  have hπ : (π : H.E) = 1 + N * (a : H.E) := by
    have := congrArg (fun z : 𝓞 H.E => (z : H.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    linear_combination -this
  have hci : IsIntegral ℤ (H.conj (a : H.E)) := hyi.map ((H.conj : H.E →+* H.E).toIntAlgHom)
  rw [hπ, map_add, map_mul, map_one, map_natCast] at hn
  set z : H.E := a + H.conj (a : H.E) + N * (a * H.conj (a : H.E)) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := H.E) N).mul (hyi.mul hci))
  have hM0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have h4 : z = algebraMap ℚ H.E (((T : ℚ) - 1) / N) := by
    have hM0' : (N : H.E) ≠ 0 := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((T : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℚ) = ((N * n : ℤ) : ℚ) := by
    have : (n : ℚ) = ((T : ℚ) - 1) / N := by simpa using hn'
    push_cast
    rw [this]
    field_simp
  exact (Nat.modEq_iff_dvd.2 ⟨n, by exact_mod_cast h5⟩).symm

theorem modEq_one_iff {a N : ℕ} (hN : 1 < N) : a ≡ 1 [MOD N] ↔ a % N = 1 := by
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt hN]

theorem hostArith_of (H : Host R)
    (hg : ∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E))
    (hl : ∀ p ∈ H.levelPrimes, p.Prime ∧ p ≡ 1 [MOD condE H]) : HostArith H := by
  have hm : ∀ p ∈ H.levelPrimes, p % (H.QS * H.q * H.d) = 1 := fun p hp =>
    (modEq_one_iff (one_lt_condE H)).1 (hl p hp).2
  refine ⟨hg, fun i => hm _ (H.g_level i), ⟨?_, ?_⟩, fun p hp => (GlobalTheory.HostSplit.split_of_one_mod R H p (hl p hp).1 (hm p hp)).2⟩
  · rw [← GlobalTheory.HostSplit.ncard_placesOver H.E H.pde_prime]
    exact (GlobalTheory.HostSplit.split_of_one_mod R H _ H.pde_prime (hm _ H.pde_level.1)).1
  · rw [← GlobalTheory.HostSplit.ncard_placesOver H.E H.pde'_prime]
    exact (GlobalTheory.HostSplit.split_of_one_mod R H _ H.pde'_prime (hm _ H.pde_level.2)).1

theorem T_modEq (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD condE D.host] := by
  obtain ⟨π, -, h2, h3⟩ := D.T_norm u
  have h0 : condE D.host * (D.host.g 0 * D.host.g 1) ^ 2 ≠ 0 :=
    Nat.mul_ne_zero (by have := one_lt_condE D.host; omega)
      (pow_ne_zero _ (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact (norm_modEq D.host π h0 h2 h3).of_mul_right _


theorem isOrigins_bsH (φ : Formalism.HC.Frame) : IsOrigins (φ := φ) Arith.bsH :=
  ⟨fun h t => GlobalTheory.Refill.bsH_orb h t, fun h t => GlobalTheory.Refill.bsH_step h t⟩

def LeastPrimeCong (H : Host R) (q0 : ℕ) : Prop :=
  ∃ r' : ℕ, IsLeast {l : ℕ | l.Prime ∧ ¬ l ∣ condE H * (H.pde - 1) * (H.pde' - 1)} r' ∧ q0 ≡ 1 [MOD r' * condE H]

theorem LeastPrimeCong.facts {H : Host R} {q0 : ℕ} (h : LeastPrimeCong H q0) :
    q0 ≡ 1 [MOD condE H] ∧ q0 ≠ H.pde ∧ q0 ≠ H.pde' := by
  obtain ⟨r', ⟨⟨-, hr⟩, -⟩, hq⟩ := h
  have h1 : q0 ≡ 1 [MOD r'] := hq.of_mul_right _
  refine ⟨hq.of_mul_left _, fun e => hr ?_, fun e => hr ?_⟩
  · rw [e] at h1
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ((Nat.modEq_iff_dvd' H.pde_prime.one_le).1 h1.symm) _) _
  · rw [e] at h1
    exact Dvd.dvd.mul_left ((Nat.modEq_iff_dvd' H.pde'_prime.one_le).1 h1.symm) _

theorem sum_log_div_le (s : Scale) :
    ∑ n ∈ Finset.range ⌈s.X'⌉₊, Real.log n / n ≤ 2 * (s.x ^ (s.eps / 3)) ^ 2 := by
  have hy : 1 ≤ s.x ^ (s.eps / 3) := Real.one_le_rpow s.one_lt_alt.le (by linarith [s.eps_pos])
  set y := s.x ^ (s.eps / 3) with hyd
  have hX : s.X' = Real.exp y := rfl
  have hX1 : 1 < s.X' := by rw [hX]; exact Real.one_lt_exp_iff.2 (by linarith)
  obtain ⟨N, hN⟩ : ∃ N, ⌈s.X'⌉₊ = N + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ceil_pos.2 (by linarith)).ne'
  have hNX : (N : ℝ) < s.X' := Nat.lt_ceil.1 (by omega)
  have hlog : ∀ n : ℕ, n ≤ N → Real.log n ≤ y := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp; linarith
    · have h0' : (0 : ℝ) < n := by exact_mod_cast h0
      have h1 : (n : ℝ) ≤ N := by exact_mod_cast hn
      rw [Real.log_le_iff_le_exp h0', ← hX]
      linarith
  rw [hN, Finset.sum_range_succ']
  have h1 : ∑ k ∈ Finset.range N, Real.log ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ y * (harmonic N : ℝ) := by
    unfold harmonic
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have := hlog (k + 1) (Finset.mem_range.1 hk)
    push_cast at this
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h2 := harmonic_le_one_add_log N
  have h3 := hlog N le_rfl
  have h4 : y * (harmonic N : ℝ) ≤ y * (y + y) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  simp only [Nat.cast_zero, div_zero, add_zero]
  nlinarith

theorem fewBad_of_badOK (eps Cb : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x →
    s.delta1 * R.n / 2 ≤ (H.TT.card : ℝ) → BadOK s Cb H → FewBad H s Arith.bsH := by
  classical
  refine ⟨(16 * |Cb|) ^ (3 / eps), fun s R H hs hx hT hB => ?_⟩
  subst hs
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have hy : 16 * |Cb| ≤ s.x ^ (s.eps / 3) := by
    have h1 : ((16 * |Cb|) ^ (3 / s.eps)) ^ (s.eps / 3) ≤ s.x ^ (s.eps / 3) :=
      Real.rpow_le_rpow (by positivity) hx (by positivity)
    rwa [← Real.rpow_mul (by positivity), show 3 / s.eps * (s.eps / 3) = 1 by field_simp, Real.rpow_one] at h1
  have hS := sum_log_div_le s
  have hxe : s.x ^ (-2 + s.eps) = s.x ^ (-2 : ℝ) * (s.x ^ (s.eps / 3)) ^ 3 := by
    rw [Real.rpow_add hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 2
    push_cast
    ring
  set y := s.x ^ (s.eps / 3) with hyd
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  unfold FewBad
  unfold BadOK at hB
  simp only at hB
  set PR := (Finset.range ⌈s.X'⌉₊).filter (fun p => p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
      s.x ^ (s.eps / 4) ≤ (addOrderOf (frobH H p) : ℝ)) with hPR
  have hB' : ∑ p ∈ PR, Real.log p / p * ((H.TT.filter (fun t => ¬ GoodH H s p (Arith.bsH (frobH H p) t))).card : ℝ) ≤
      4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * R.n * ∑ p ∈ PR, Real.log p / p := by
    refine le_trans (le_of_eq ?_) hB
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : H.cls p = PrimeClass.inertClass := (Finset.mem_filter.1 hp).2.2.1
    have hst : Arith.Loc.stepP (baseOf s 0 0 H) (hPH H p) p = frobH H p := by
      unfold Arith.Loc.stepP
      rw [if_neg]
      · rfl
      · intro h
        have h' : H.cls p = PrimeClass.signal := h
        rw [hc] at h'
        cases h'
    rw [hst]
    rfl
  have hn : ∀ n : ℕ, 0 ≤ Real.log n / n := fun n => div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
  have hS0 : 0 ≤ ∑ p ∈ PR, Real.log p / p := Finset.sum_nonneg fun n _ => hn n
  have hS1 : ∑ p ∈ PR, Real.log p / p ≤ 2 * y ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n _ _ => hn n).trans hS
  have hz : 0 < s.x ^ (-2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hd : 0 ≤ s.delta1 * R.n := by unfold Scale.delta1; positivity
  refine le_trans (le_of_eq (by congr)) (hB'.trans ?_)
  rw [hxe]
  set S := ∑ p ∈ PR, Real.log p / p
  set z := s.x ^ (-2 : ℝ)
  set τ := (H.TT.card : ℝ)
  calc 4 * (Cb * z) * s.delta1 * R.n * S = 4 * z * (Cb * ((s.delta1 * R.n) * S)) := by ring
    _ ≤ 4 * z * (|Cb| * ((2 * τ) * (2 * y ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (mul_le_mul_of_nonneg_right (le_abs_self Cb) (mul_nonneg hd hS0)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact mul_le_mul (by linarith) hS1 hS0 (by linarith)
    _ = τ * (z * y ^ 2) * (16 * |Cb|) := by ring
    _ ≤ τ * (z * y ^ 2) * y := mul_le_mul_of_nonneg_left hy (mul_nonneg (by linarith) (by positivity))
    _ = τ * (z * y ^ 3) := by ring

theorem level_of_arithData {C : FC} {s : Scale} {H : Host R} {q0 : ℕ}
    {bs : R.A → R.A → R.A} (h : ArithData C s H q0 bs) :
    ∀ p ∈ H.levelPrimes, p.Prime ∧ p ≡ 1 [MOD condE H] := by
  obtain ⟨-, -, -, -, -, -, -, -, hπ, -, ⟨hp, hp'⟩, ⟨hq, -, -, hr⟩, hl⟩ := h
  have hg : ∀ i, (H.g i).Prime ∧ H.g i ≡ 1 [MOD condE H] := fun i => by
    obtain ⟨π, -, h2, h3⟩ := hπ i
    exact ⟨H.g_prime i, norm_modEq H π (by have := one_lt_condE H; omega) h2 h3⟩
  intro p hm
  rw [hl] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact hg 0
  · exact hg 1
  · exact ⟨H.pde_prime, hp.of_dvd (Nat.dvd_lcm_right _ _)⟩
  · exact ⟨H.pde'_prime, hp'.of_dvd (Nat.dvd_lcm_right _ _)⟩
  · exact ⟨hq, (LeastPrimeCong.facts hr).1⟩

theorem hostGood_of_arithData {C : FC} {s : Scale} {H : Host R} {q0 : ℕ} {c6 Cb : ℝ}
    {bs : R.A → R.A → R.A} (h : ArithData C s H q0 bs)
    (h2 : H.secondSet_card_lower_bound) (h6 : ThinOK s c6 H) (hb : BadOK s Cb H) :
    H.CT2 = C.CT2 ∧ HostGood s C.P.Cpde 4 c6 Cb H q0 ∧ LeastPrimeCong H q0 := by
  have hlv := level_of_arithData h
  obtain ⟨hv, hT, hbox, hdl, hqd, hc, -, -, hπ, hdis, ⟨hp, hp'⟩, ⟨hq, -, hq8, hr⟩, hl⟩ := h
  have h1 := one_lt_condE H
  have hf := LeastPrimeCong.facts hr
  refine ⟨hT, ⟨hv, hostArith_of H (fun i => ?_) hlv, h2, hc, hqd, hbox, hdl, h6, hb, hdis, hπ,
    ⟨(modEq_one_iff (one_lt_lcm H)).1 hp, (modEq_one_iff (one_lt_lcm H)).1 hp'⟩,
    ⟨hq, (modEq_one_iff h1).1 hf.1, ?_, hf.2.1, hf.2.2⟩, hl⟩, hr⟩
  · obtain ⟨π, a1, a2, -⟩ := hπ i
    exact ⟨π, a1, a2⟩
  · unfold condE at hq8
    exact_mod_cast hq8

theorem arithData_of_hostGood {C : FC} {s : Scale} {H : Host R} {q0 : ℕ} {c6 Cb : ℝ} (hT : H.CT2 = C.CT2)
    (h : HostGood s C.P.Cpde 4 c6 Cb H q0) (hr : LeastPrimeCong H q0) (hF : FewBad H s Arith.bsH) :
    ArithData C s H q0 Arith.bsH := by
  obtain ⟨hv, -, -, hc, hqd, hbox, hdl, -, -, hdis, hπ, ⟨hp, hp'⟩, ⟨hq, hm, hq8, -, -⟩, hl⟩ := h
  have h1 := one_lt_condE H
  refine ⟨hv, hT, hbox, hdl, hqd, hc, isOrigins_bsH _, hF, hπ, hdis,
    ⟨(modEq_one_iff (one_lt_lcm H)).2 hp, (modEq_one_iff (one_lt_lcm H)).2 hp'⟩,
    ⟨hq, ?_, ?_, hr⟩, hl⟩
  · have h4 : 4 ∣ H.QS * H.q * H.d := four_dvd_cond H
    have h5 : q0 % 4 = 1 := by rw [← Nat.mod_mod_of_dvd q0 h4, hm]
    have := hq.two_le
    omega
  · unfold condE
    exact_mod_cast hq8

theorem hyp_iff (eps c6 Cb : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (C : FC) (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ),
    s.eps = eps → x0 ≤ s.x →
    ((H.CT2 = C.CT2 ∧ HostGood s C.P.Cpde 4 c6 Cb H q0 ∧ LeastPrimeCong H q0) ↔
      (ArithData C s H q0 Arith.bsH ∧ H.secondSet_card_lower_bound ∧ ThinOK s c6 H ∧ BadOK s Cb H)) := by
  obtain ⟨x0, h0⟩ := fewBad_of_badOK eps Cb he
  refine ⟨x0, fun C s R H q0 hs hx => ⟨fun ⟨hT, h, hr⟩ => ?_, fun ⟨h, h2, h6, hb⟩ => hostGood_of_arithData h h2 h6 hb⟩⟩
  have hb := h.2.2.2.2.2.2.2.2.1
  exact ⟨arithData_of_hostGood hT h hr (h0 s R H hs hx h.1.2.1.1 hb), h.2.2.1, h.2.2.2.2.2.2.2.1, hb⟩

theorem win_iff (C : FC) (s : Scale) (H : Host R) (a b : ℕ → ℤ) :
    Win s R.k (H.TT.image Formalism.HC.Frame.A.val) (bTop C s R) a b ↔ WinOK s C.GK H (fun t => a t.val) (fun t => b t.val) := by
  unfold Win WinOK bTop
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem winOK_iff (C : FC) (s : Scale) (H : Host R) (a b : R.A → ℤ) :
    WinOK s C.GK H a b ↔ Win s R.k (H.TT.image Formalism.HC.Frame.A.val) (bTop C s R) (fun n => a (R.ofNat n)) (fun n => b (R.ofNat n)) := by
  rw [win_iff]
  simp only [Formalism.HC.Frame.ofNat_val]


def codeOf {M : ℕ} {W : Type} (c : Fin M → W) (hc : Function.Injective c) : Finset W := Finset.univ.map ⟨c, hc⟩

theorem card_codeOf {M : ℕ} {W : Type} (c : Fin M → W) (hc : Function.Injective c) : (codeOf c hc).card = M := by
  simp [codeOf]

def codeEquiv {M : ℕ} {W : Type} (c : Fin M → W) (hc : Function.Injective c) : Fin M ≃ codeOf c hc :=
  Equiv.ofBijective (fun i => ⟨c i, Finset.mem_map_of_mem _ (Finset.mem_univ i)⟩)
    ⟨fun _ _ h => hc (congrArg Subtype.val h), fun w => by
      obtain ⟨i, -, hi⟩ := Finset.mem_map.1 w.2
      exact ⟨i, Subtype.ext hi⟩⟩

theorem codeEquiv_symm {M : ℕ} {W : Type} (c : Fin M → W) (hc : Function.Injective c) (w : codeOf c hc) :
    c ((codeEquiv c hc).symm w) = w.1 :=
  congrArg Subtype.val ((codeEquiv c hc).apply_symm_apply w)

theorem range_iff {C : FC} (hC : Std C) {D : D7} (L : SizeData₂ D) :
    (L.TuGe ∧ ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ C.CTu * D.R.m * L.sc.L) ↔
      ∀ u, L.sc.b ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ) ∧ ((D.mem u).A.T : ℝ) ≤ L.sc.b ^ (25 * (D.R.m : ℝ)) := by
  have h25 : C.CTu = 25 := hC.2.2.2.2.2.2.2.2.2.2.1
  have key : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ C.CTu * D.R.m * L.sc.L ↔
      ((D.mem u).A.T : ℝ) ≤ L.sc.b ^ (25 * (D.R.m : ℝ)) := fun u => by
    have h0 : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
    rw [Real.log_le_iff_le_exp h0, h25, Scale.b, ← Real.exp_mul, mul_comm L.sc.L]
  exact ⟨fun h u => ⟨h.1 u, (key u).1 (h.2 u)⟩, fun h => ⟨fun u => (h u).1, fun u => (key u).2 (h u).2⟩⟩

def BsCanon {C : FC} (p : Pt C) : Prop := ∀ h t, p.ta.Gx.bs h t = Arith.bsH h t

def OffCanon : PtProp := fun D L _ X _ _ _ _ _ =>
  ∀ j, j ∉ SizeData₂.lifts D → ∀ t : G.HH D,
    X.off j (false, t) = if t ∈ D.host.TT then L.sc.b' / L.sc.x else L.sc.w'' D.R.n




def ObjExNarrow (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ Cdg x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
        (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
        HostGood s C8 4 c6 Cb H q0 → LeastPrimeCong H q0 → WinOK s C.GK H a b →
        M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n →
        ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q ∧
          ChProviso_at p.L 3 ∧ p.L.TuGe ∧ (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧
          FactDGam p.D Cdg

def Common (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ Cdg x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
        (c : Fin M → Fin (R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
        HostGood s C8 4 c6 Cb H q0 → LeastPrimeCong H q0 → WinOK s C.GK H a b →
        M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c →
        ∃ off : ℕ → ℕ → ℝ, ∀ u0 < R.n,
        ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ BsCanon p ∧
          (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧ p.Has Q ∧
          ChProviso_at p.L 3 ∧ p.L.TuGe ∧ (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧
          FactDGam p.D Cdg


theorem Common.imp {Q Q' : PtProp} (h : Common Q) (hQ : ∀ (C : FC) (p : Pt C), p.Has Q → p.Has Q') : Common Q' := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 c6 Cb h1 h2 h3 h4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 c6 Cb h1 h2 h3 h4
  refine ⟨K0, fun C hC h8 hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hC h8 hL
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨Cdg, x0, h⟩ := h ch hch
  refine ⟨Cdg, x0, fun s R H q0 a b M c hs hx hR hT hH hr hw hM hc => ?_⟩
  obtain ⟨off, h⟩ := h s R H q0 a b M c hs hx hR hT hH hr hw hM hc
  refine ⟨off, fun u0 hu => ?_⟩
  obtain ⟨p, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h u0 hu
  exact ⟨p, a1, a2, a3, a4, a5, a6, hQ C p a7, a8⟩





def EpsLe (δ : ℝ) : PtProp := fun _ L _ _ _ _ _ _ _ => L.sc.eps ≤ δ



def HostExNarrow : Prop :=
  HostExP fun _ s _ H q0 => QDq s.x s.eps 4 H.q H.d ∧ LeastPrimeCong H q0



structure Switch where

  allEps : Bool

  absCdg : Bool

  uniformThreshold : Bool

  four : Bool

  leastPrime : Bool

  thick : Bool

  thin : Bool

  meanBad : Bool

  leastOrigins : Bool

  exactHost : Bool

  canonOff : Bool

def first : Switch := ⟨false, false, false, false, false, true, true, true, true, false, true⟩

def second : Switch := ⟨true, true, true, true, true, false, false, false, false, true, false⟩

def Switch.Covers (w w' : Switch) : Prop :=
  (w'.allEps → w.allEps) ∧ (w'.absCdg → w.absCdg) ∧ (w'.uniformThreshold → w.uniformThreshold) ∧ (w.four → w'.four) ∧
  (w.leastPrime → w'.leastPrime) ∧ (w.thick → w'.thick) ∧ (w.thin → w'.thin) ∧ (w.meanBad → w'.meanBad) ∧
  (w'.meanBad → w.meanBad ∨ w'.leastOrigins) ∧ (w.leastOrigins → w'.leastOrigins) ∧ (w'.exactHost → w.exactHost) ∧
  (w'.canonOff → w.canonOff)

def HostCore (s : Scale) (C8 : ℝ) (H : Host R) (q0 : ℕ) : Prop :=
  HostVal s C8 H ∧ HostArith H ∧ 4 * H.Lw * H.T2.card ≤ R.n0 ∧ BoxW s H ∧ |GlobalTheory.EX.dlogH H| ≤ s.x ^ s.eps ∧
  Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E) ∧
    (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d : ℕ) : 𝓞 H.E)}) ∧
  (H.pde % Nat.lcm 15 (H.QS * H.q * H.d) = 1 ∧ H.pde' % Nat.lcm 15 (H.QS * H.q * H.d) = 1) ∧
  (q0.Prime ∧ q0 % (H.QS * H.q * H.d) = 1 ∧ (q0 : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 ∧ q0 ≠ H.pde ∧ q0 ≠ H.pde') ∧
  H.levelPrimes = {H.g 0, H.g 1, H.pde, H.pde', q0}

def Hyp (w : Switch) (C : FC) (C5 c6 Cb : ℝ) (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ)
    (bs : R.A → R.A → R.A) : Prop :=
  H.CT2 = C.CT2 ∧ HostCore s C.P.Cpde H q0 ∧ QDq s.x s.eps (if w.four then 4 else C5) H.q H.d ∧
  (w.leastPrime → LeastPrimeCong H q0) ∧ (w.thick → H.secondSet_card_lower_bound) ∧ (w.thin → ThinOK s c6 H) ∧
  (if w.meanBad then BadOK s Cb H else FewBad H s bs) ∧ IsOrigins bs ∧ (w.leastOrigins → bs = Arith.bsH)

def BsTie {C : FC} (p : Pt C) (bs : R.A → R.A → R.A) : Prop :=
  ∀ (h t : G.HH p.D) (h' t' : R.A), h.val = h'.val → t.val = t'.val → (p.ta.Gx.bs h t).val = (bs h' t').val

def ExactHost {C : FC} (p : Pt C) (H : Host R) (u0 : ℕ) : Prop :=
  ∃ (hK : H.ccK = ⊤) (S : Finset ℕ) (hcp : ∀ l ∈ S, Nat.Coprime l H.QS), (∀ l, l ∈ S ↔ ∃ u, (p.D.mem u).A.T = l) ∧
    (⟨p.D.R, p.D.host⟩ : Σ R' : Ranks, Host R') = ⟨R, hostAt H hK (R.ofNat u0) S hcp⟩

def Body (Hy : ∀ (_ : Scale) (R : Ranks) (_ : Host R) (_ : ℕ), (R.A → R.A → R.A) → Prop)
    (exactHost canonOff : Bool) (Q : PtProp) (C : FC) (eps cD ch Cdg x0 : ℝ) : Prop :=
  ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (bs : R.A → R.A → R.A)
    (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → RankVal s R →
    Hy s R H q0 bs → WinOK s C.GK H a b →
    M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c →
    ∃ off : ℕ → ℕ → ℝ, ∀ u0 < R.n,
      ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ BsTie p bs ∧
        (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧
        (exactHost → ExactHost p H u0) ∧ (canonOff → p.Has OffCanon) ∧ p.Has Q ∧
        ChProviso_at p.L 3 ∧ p.L.TuGe ∧ (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧
        FactDGam p.D Cdg

def Scheme (w : Switch) (Q : PtProp) : Prop :=
  ∃ ε0 Cabs : ℝ, 0 < ε0 ∧ (w.allEps → 1 / 52 ≤ ε0) ∧ 0 < Cabs ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 →
    ∀ C8 : ℝ, 1 ≤ C8 → ∃ Kabs : TransportedAlt, ∀ C5 c6 Cb : ℝ, ∃ K0 : TransportedAlt, (w.uniformThreshold → K0 = Kabs) ∧
      ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ Cdg x0 : ℝ,
        (w.absCdg → Cdg = Cabs) ∧ Body (Hyp w C C5 c6 Cb) w.exactHost w.canonOff Q C eps cD ch Cdg x0

abbrev HostProp : Type 1 := ∀ (_ : Scale) (R : Ranks) (_ : Host R) (_ : ℕ), Prop

def ObjOn (P : HostProp) (Q : PtProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ Cdg x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ)
        (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 →
        HostGood s C8 C5 c6 Cb H q0 → P s R H q0 → WinOK s C.GK H a b →
        M = ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n →
        ∃ p : Pt C, p.L.sc = s ∧ Val C cD ch p.L ∧ HostArith p.D.host ∧ p.From H a b c u0 ∧ CanonInst p.ta.Gx ∧ p.Has Q ∧
          ChProviso_at p.L 3 ∧ p.L.TuGe ∧ (∀ u, Real.log ((p.D.mem u).A.T : ℝ) ≤ C.CTu * p.D.R.m * p.L.sc.L) ∧
          FactDGam p.D Cdg

theorem over_iff {C : FC} {s : Scale} {H : Host R} {q0 : ℕ} {bs : R.A → R.A → R.A}
    (hH : ArithData C s H q0 bs) (a b : ℕ → ℤ) {M : ℕ} (c : Fin M → Fin (R.k - 2) → Bool) (hc : Function.Injective c)
    (off : ℕ → ℕ → ℝ) (u0 : R.A) (p : Pt C) :
    (∃ T : codeOf c hc → ℕ, Over p s H hH.ccK_eq bs a b (codeOf c hc) off u0 T) ↔
      p.L.sc = s ∧ HostArith p.D.host ∧ p.From H (fun t => a t.val) (fun t => b t.val) c u0.val ∧ BsTie p bs ∧
        (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧ ExactHost p H u0.val := by
  constructor
  · rintro ⟨T, ⟨hcp, hh⟩, hs, hbs, hoff, hw, e, he, hT⟩
    have hR : p.D.R = R := congrArg Sigma.fst hh
    subst hR
    have hD : p.D.host = hostAt H hH.ccK_eq u0 (Finset.univ.image T) hcp := eq_of_heq (Sigma.mk.inj hh).2
    have hmod := T_modEq p.D
    refine ⟨hs, ?_, ⟨rfl, by rw [hD]; rfl, by rw [hD]; rfl, by rw [hD]; rfl, by rw [hD]; rfl, by rw [hD]; rfl, by rw [hD]; rfl,
      by rw [hD]; rfl, by rw [hD]; exact Finset.subset_union_left, by rw [hD]; rfl, fun l => ?_, fun t t' ht => ?_,
      ⟨e.trans (codeEquiv c hc).symm, fun u l => ?_⟩, by rw [hD]; rfl⟩, hbs, hoff, hH.ccK_eq, Finset.univ.image T, hcp, fun l => ?_, ?_⟩
    · rw [hD] at hmod ⊢
      refine hostArith_of _ (fun i => ?_) fun l hl => ?_
      · obtain ⟨π, a1, a2, -⟩ := hH.2.2.2.2.2.2.2.2.1 i
        exact ⟨π, a1, a2⟩
      · rcases Finset.mem_union.1 hl with hl | hl
        · exact level_of_arithData hH l hl
        · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hl
          obtain ⟨u, rfl⟩ := e.surjective w
          rw [← hT u]
          exact ⟨(p.D.mem u).A.T_prime, hmod u⟩
    · show (frobH p.D.host l).val = _
      rw [hD]
      rfl
    · have := hw t
      rwa [ht] at this
    · split_ifs with hl
      · rw [Equiv.trans_apply, codeEquiv_symm c hc]
        exact he u ⟨l, hl⟩
      · exact dif_neg hl
    · rw [Finset.mem_image]
      refine ⟨fun ⟨w, _, hw⟩ => ?_, fun ⟨u, hu⟩ => ⟨e u, Finset.mem_univ _, by rw [← hT, hu]⟩⟩
      obtain ⟨u, rfl⟩ := e.surjective w
      exact ⟨u, by rw [hT, hw]⟩
    · rw [Formalism.HC.Frame.ofNat_val]
      exact hh
  · rintro ⟨hs, -, ⟨hR, -, -, -, -, -, -, -, -, -, -, hw, ⟨eW, he⟩, -⟩, hB, hoff, hK, S, hcp, hS, hh⟩
    rw [Formalism.HC.Frame.ofNat_val] at hh
    subst hR
    set e := eW.trans (codeEquiv c hc) with hedef
    refine ⟨fun w => (p.D.mem (e.symm w)).A.T, ?_, hs, hB, hoff, fun t => hw t _ rfl, e, fun u l => ?_,
      fun u => congrArg (fun v => (p.D.mem v).A.T) (e.symm_apply_apply u).symm⟩
    · have : S = Finset.univ.image (fun w => (p.D.mem (e.symm w)).A.T) := by
        ext l
        rw [hS, Finset.mem_image]
        exact ⟨fun ⟨u, hu⟩ => ⟨e u, Finset.mem_univ _, by rw [e.symm_apply_apply, hu]⟩, fun ⟨w, _, hw⟩ => ⟨_, hw⟩⟩
      rw [← this]
      exact ⟨hcp, hh⟩
    · rw [he u l.1, dif_pos l.2]
      rfl

end GlobalTheory.ObjExCompare

end
