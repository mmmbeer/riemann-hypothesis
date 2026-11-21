import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaBounded
import GroundTheory.PAdicHodge.DMTeichBasic
import GroundTheory.PAdicHodge.DMTeichPow
import GroundTheory.PAdicHodge.ExtRobbaPointEval
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem prefixLe_sub_of_coeff_near (n : ℕ) : ∀ {x x' : Γ} {B δ : ℝ}, 0 ≤ δ → δ ≤ B →
    T.PrefixLe x n B → T.PrefixLe x' n B → (∀ m ≤ n, ‖T.coeff x' m - T.coeff x m‖ ≤ δ) →
      T.PrefixLe (x' - x) n (B ^ (1 - coeffHolderExp p n) * δ ^ coeffHolderExp p n) := by
  induction n with
  | zero =>
    intro x x' B δ hδ hδB _ _ hd m hm
    obtain rfl : m = 0 := by omega
    rw [coeff_zero, map_sub]
    have := hd 0 le_rfl
    rw [coeff_zero, coeff_zero] at this
    exact this.trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one 0).2)
  | succ n ih =>
    intro x x' B δ hδ hδB hx hx' hd m hm
    obtain ⟨hs0, hs1⟩ := inv_pow_pos_le_one (p := p) (n + 1)
    set s := ((p ^ (n + 1) : ℕ) : ℝ)⁻¹ with hsdef
    have hB0 : 0 ≤ B := hδ.trans hδB
    have hδ' : 0 ≤ B ^ (1 - s) * δ ^ s :=
      mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _)
    have hδδ' : δ ≤ B ^ (1 - s) * δ ^ s := le_rpow_mix hδ hδB hs1
    have hδ'B : B ^ (1 - s) * δ ^ s ≤ B := rpow_mix_le hδ hδB hs0.le hs1
    have hd0 : ‖T.red (x' - x)‖ ≤ δ := by
      have := hd 0 (Nat.zero_le _)
      rwa [coeff_zero, coeff_zero, ← map_sub] at this
    rcases m with _ | m
    · rw [coeff_zero]
      exact hd0.trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one _).2)
    set d := x' - x with hddef
    set H := T.teich (T.red x) + T.teich (T.red d) - T.teich (T.red x + T.red d) with hHdef
    have hH : T.red H = 0 := by rw [hHdef]; simp [red_teich]
    obtain ⟨h', hh'⟩ := T.red_eq_zero_iff.1 hH
    have htail : T.tail (x + d) = T.tail x + (T.tail d + h') := by
      refine T.tail_eq (a := T.red x + T.red d) ?_
      have ex := T.eq_teich_add_π_mul_tail x
      have ey := T.eq_teich_add_π_mul_tail d
      calc x + d = T.teich (T.red x) + T.π * T.tail x + (T.teich (T.red d) + T.π * T.tail d) := by
            rw [← ex, ← ey]
        _ = T.teich (T.red x + T.red d) + H + T.π * T.tail x + T.π * T.tail d := by
            rw [hHdef]; ring
        _ = _ := by rw [hh']; ring
    have hxd : x + d = x' := by rw [hddef]; ring
    rw [hxd] at htail
    have hHb : T.PrefixLe H (n + 1) (B ^ (1 - s) * δ ^ s) := by
      have := T.prefixLe_teich_add_sub_of_le (hx 0 (Nat.zero_le _)) hd0 hδ hδB (n + 1)
      have e : H = -(T.teich (T.red x + T.red d) - T.teich (T.red x) - T.teich (T.red d)) := by
        rw [hHdef]; ring
      rw [e]; exact T.prefixLe_neg this
    have hh'b : T.PrefixLe h' n (B ^ (1 - s) * δ ^ s) := fun i hi => by
      rw [← T.coeff_π_mul_succ, ← hh']; exact hHb (i + 1) (by omega)
    have hxt : T.PrefixLe (T.tail x) n B := fun i hi => by
      rw [← coeff_succ]; exact hx (i + 1) (by omega)
    have hx't : T.PrefixLe (T.tail x') n B := fun i hi => by
      rw [← coeff_succ]; exact hx' (i + 1) (by omega)
    have hdt : ∀ i ≤ n, ‖T.coeff (T.tail x') i - T.coeff (T.tail x) i‖ ≤ B ^ (1 - s) * δ ^ s :=
      fun i hi => by rw [← coeff_succ, ← coeff_succ]; exact (hd (i + 1) (by omega)).trans hδδ'
    have hI := ih hδ' hδ'B hxt hx't hdt
    have htd : T.tail d = (T.tail x' - T.tail x) - h' := by rw [htail]; ring
    have hmix : B ^ (1 - s) * δ ^ s ≤
        B ^ (1 - coeffHolderExp p n) * (B ^ (1 - s) * δ ^ s) ^ coeffHolderExp p n :=
      le_rpow_mix hδ' hδ'B (coeffHolderExp_pos_le_one n).2
    have hfin := T.prefixLe_sub hI (hh'b.mono hmix)
    rw [coeff_succ, htd]
    refine (hfin m (by omega)).trans (le_of_eq ?_)
    obtain ⟨ht0, ht1⟩ := coeffHolderExp_pos_le_one (p := p) n
    have hne : 1 - coeffHolderExp p n + (1 - s) * coeffHolderExp p n ≠ 0 := by
      have : s * coeffHolderExp p n ≤ s := mul_le_of_le_one_right hs0.le ht1
      have hs2 : s < 1 := by
        rw [hsdef]
        have h2 : (1 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_lt_pow (by omega) hp.out.one_lt
        exact inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _), ← Real.rpow_mul hB0,
      ← Real.rpow_mul hδ, ← mul_assoc, ← Real.rpow_add' hB0 hne, coeffHolderExp_succ]
    congr 2 <;> ring

theorem exists_holder_lt {B t ε : ℝ} (hB : 0 < B) (ht : 0 < t) (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ B ∧ ∀ δ', 0 ≤ δ' → δ' ≤ δ → B ^ (1 - t) * δ' ^ t < ε := by
  have hBt : 0 < B ^ (1 - t) := Real.rpow_pos_of_pos hB _
  set c := ε / (2 * B ^ (1 - t)) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨min B (c ^ t⁻¹), lt_min hB (Real.rpow_pos_of_pos hc0 _), min_le_left _ _,
    fun δ' h0 h1 => ?_⟩
  have h2 : δ' ^ t ≤ c := by
    calc δ' ^ t ≤ (c ^ t⁻¹) ^ t := Real.rpow_le_rpow h0 (h1.trans (min_le_right _ _)) ht.le
      _ = c := Real.rpow_inv_rpow hc0.le ht.ne'
  calc B ^ (1 - t) * δ' ^ t ≤ B ^ (1 - t) * c := mul_le_mul_of_nonneg_left h2 hBt.le
    _ = ε / 2 := by rw [hc]; field_simp
    _ < ε := by linarith

theorem tendsto_coeff_add {ι : Type*} {l : Filter ι} (z : Γ) {w : ι → Γ} (n : ℕ)
    (hw : ∀ δ > 0, ∀ᶠ i in l, T.PrefixLe (w i) n δ) :
    Tendsto (fun i => T.coeff (z + w i) n) l (𝓝 (T.coeff z n)) := by
  obtain ⟨B0, hB0, -⟩ := T.exists_prefix_max z n
  set B : ℝ := ‖B0‖ + 1 with hBdef
  have hB : 0 < B := by positivity
  have hzB : T.PrefixLe z n B := hB0.mono (by rw [hBdef]; linarith)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδB, hδ⟩ := exists_holder_lt hB (coeffHolderExp_pos_le_one (p := p) n).1 hε
  filter_upwards [hw δ hδ0] with i hi
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (T.norm_coeff_add_sub_le n hδ0.le hδB hzB hi n le_rfl) (hδ δ hδ0.le le_rfl)

variable [CompleteSpace L]

def coeffLim (x : ℕ → Γ) : Γ := T.ofCoeff fun m => limUnder atTop fun k => T.coeff (x k) m

theorem tendsto_coeff_coeffLim {x : ℕ → Γ} (h : ∀ m, CauchySeq fun k => T.coeff (x k) m)
    (m : ℕ) : Tendsto (fun k => T.coeff (x k) m) atTop (𝓝 (T.coeff (T.coeffLim x) m)) := by
  rw [coeffLim, coeff_ofCoeff]; exact (h m).tendsto_limUnder

theorem prefixLe_sub_coeffLim {x : ℕ → Γ} (h : ∀ m, CauchySeq fun k => T.coeff (x k) m)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, T.PrefixLe (x k - T.coeffLim x) n ε := by
  set y := T.coeffLim x
  set B := 1 + ∑ m ∈ Finset.range (n + 1), ‖T.coeff y m‖ with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef]; linarith [Finset.sum_nonneg fun m (_ : m ∈ Finset.range (n + 1)) =>
      norm_nonneg (T.coeff y m)]
  have hB : 0 < B := by linarith
  have hyB : ∀ m ≤ n, ‖T.coeff y m‖ + 1 ≤ B := fun m hm => by
    rw [hBdef, add_comm]
    exact add_le_add_right (Finset.single_le_sum (f := fun m => ‖T.coeff y m‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))) 1
  obtain ⟨δ, hδ0, hδB, hδ⟩ := exists_holder_lt hB (coeffHolderExp_pos_le_one (p := p) n).1 hε
  set δ1 := min δ 1 with hδ1
  have hδ10 : 0 < δ1 := lt_min hδ0 one_pos
  have hev : ∀ᶠ k in atTop, ∀ m ∈ Finset.range (n + 1), ‖T.coeff (x k) m - T.coeff y m‖ < δ1 := by
    rw [Filter.eventually_all_finset]
    intro m _
    have := (T.tendsto_coeff_coeffLim h m)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this δ1 hδ10] with k hk
    rwa [dist_eq_norm] at hk
  filter_upwards [hev] with k hk
  have hk' : ∀ m ≤ n, ‖T.coeff (x k) m - T.coeff y m‖ ≤ δ1 := fun m hm =>
    (hk m (Finset.mem_range.2 (by omega))).le
  have hxB : T.PrefixLe (x k) n B := fun m hm => by
    have h1 : ‖T.coeff (x k) m‖ ≤ ‖T.coeff (x k) m - T.coeff y m‖ + ‖T.coeff y m‖ := by
      calc ‖T.coeff (x k) m‖ = ‖(T.coeff (x k) m - T.coeff y m) + T.coeff y m‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 := hk' m hm
    have h3 := hyB m hm
    have h4 : δ1 ≤ 1 := min_le_right _ _
    linarith
  have hyB' : T.PrefixLe y n B := fun m hm => by linarith [hyB m hm]
  have hδ1B : δ1 ≤ B := (min_le_right _ _).trans hB1
  have := T.prefixLe_sub_of_coeff_near n hδ10.le hδ1B hyB' hxB hk'
  exact this.mono (hδ δ1 hδ10.le (min_le_left _ _)).le

omit [CompleteSpace L] in
theorem convergesAt_zcoeff_sub {x y : Γ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) :
    ConvergesAt (T.zcoeff (x - y)) ρ := by
  rw [sub_eq_add_neg]
  exact T.convergesAt_zcoeff_add hρ0 hρ1 hx (T.convergesAt_zcoeff_neg hρ0 hρ1 hy)

omit [CompleteSpace L] in

theorem prefixLe_of_weight {y : Γ} {ρ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : ∀ m : ℕ, ‖T.coeff y m‖ * ρ ^ m ≤ M) (j : ℕ) : T.PrefixLe y j (M / ρ ^ j) := by
  intro m hm
  have := norm_le_div_of_weight (a := T.coeff y m) (m := (m : ℤ)) (n := (j : ℤ)) hρ0 hρ1
    (M := M) (by exact_mod_cast hm) (by rw [zpow_natCast]; exact h m)
  rwa [zpow_natCast] at this

theorem exists_limit_gaussNorm {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : ℕ → Γ}
    (hx : ∀ k, ConvergesAt (T.zcoeff (x k)) ρ)
    (hc : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, gaussNorm (T.zcoeff (x k - x l)) ρ ≤ ε) :
    (∀ m, CauchySeq fun k => T.coeff (x k) m) ∧ ConvergesAt (T.zcoeff (T.coeffLim x)) ρ ∧
      ∀ ε > 0, ∃ N, ∀ k ≥ N, gaussNorm (T.zcoeff (x k - T.coeffLim x)) ρ ≤ ε := by
  have hsub : ∀ k l, ConvergesAt (T.zcoeff (x k - x l)) ρ := fun k l =>
    T.convergesAt_zcoeff_sub hρ0 hρ1 (hx k) (hx l)
  have hw : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ j : ℕ, ‖T.coeff (x k - x l) j‖ * ρ ^ j ≤ ε := by
    intro ε hε; obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun k hk l hl j => ?_⟩
    have := (hsub k l).le_gaussNorm j
    rw [zcoeff_natCast, zpow_natCast] at this
    exact this.trans (hN k hk l hl)
  obtain ⟨N1, hN1⟩ := hw 1 one_pos
  set C := max (gaussNorm (T.zcoeff (x N1)) ρ) 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hbd : ∀ k ≥ N1, ∀ j : ℕ, T.PrefixLe (x k) j (C / ρ ^ j) := by
    intro k hk j m hm
    have e : x k = x N1 + (x k - x N1) := by ring
    have hb : 0 ≤ C / (ρ ^ (j : ℤ)) := div_nonneg (by linarith) (zpow_pos hρ0 _).le
    have := T.norm_zcoeff_add_le (x := x N1) (y := x k - x N1) (n := (m : ℤ)) hb
      (fun i hi => norm_le_div_of_weight hρ0 hρ1.le (hi.trans (by exact_mod_cast hm))
        (((hx N1).le_gaussNorm i).trans (le_max_left _ _)))
      (fun i hi => by
        rcases lt_or_ge i 0 with hi0 | hi0
        · rw [T.zcoeff_of_neg _ hi0, norm_zero]; exact hb
        · lift i to ℕ using hi0
          refine norm_le_div_of_weight hρ0 hρ1.le (hi.trans (by exact_mod_cast hm)) ?_
          rw [zcoeff_natCast, zpow_natCast]
          exact (hN1 k hk N1 le_rfl i).trans hC1)
    rw [← e, zcoeff_natCast] at this
    rwa [zpow_natCast] at this
  have hcoeff : ∀ m, CauchySeq fun k => T.coeff (x k) m := by
    intro m
    rw [Metric.cauchySeq_iff]
    intro ε' hε'
    have hB : 0 < C / ρ ^ m := div_pos (by linarith) (pow_pos hρ0 m)
    obtain ⟨δ, hδ0, hδB, hδ⟩ := exists_holder_lt hB (coeffHolderExp_pos_le_one (p := p) m).1 hε'
    obtain ⟨N, hN⟩ := hw (δ * ρ ^ m) (mul_pos hδ0 (pow_pos hρ0 m))
    refine ⟨max N1 N, fun k hk l hl => ?_⟩
    have hk1 : N1 ≤ k := le_of_max_le_left hk
    have hkN : N ≤ k := le_of_max_le_right hk
    have hl1 : N1 ≤ l := le_of_max_le_left hl
    have hlN : N ≤ l := le_of_max_le_right hl
    have hyδ : T.PrefixLe (x k - x l) m δ := by
      have := T.prefixLe_of_weight hρ0 hρ1.le (hN k hkN l hlN) m
      rwa [mul_div_assoc, div_self (pow_pos hρ0 m).ne', mul_one] at this
    have := T.norm_coeff_add_sub_le m hδ0.le hδB (hbd l hl1 m) hyδ m le_rfl
    rw [show x l + (x k - x l) = x k by ring] at this
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this (hδ δ hδ0.le le_rfl)
  refine ⟨hcoeff, ?_⟩
  set y := T.coeffLim x

  have hwy : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ j : ℕ, ‖T.coeff (x k - y) j‖ * ρ ^ j ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hw ε hε
    refine ⟨N, fun k hk j => ?_⟩
    have ht : Tendsto (fun l => T.coeff ((x k - y) + (y - x l)) j) atTop
        (𝓝 (T.coeff (x k - y) j)) := by
      refine T.tendsto_coeff_add (x k - y) j fun δ hδ => ?_
      filter_upwards [T.prefixLe_sub_coeffLim hcoeff j hδ] with l hl
      rw [← neg_sub]; exact T.prefixLe_neg hl
    have ht' := (ht.norm).mul_const (ρ ^ j)
    refine le_of_tendsto ht' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with l hl
    rw [show x k - y + (y - x l) = x k - x l by ring]
    exact hN k hk l hl j
  have hwy' : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ j : ℤ, ‖T.zcoeff (x k - y) j‖ * ρ ^ j ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hwy ε hε
    refine ⟨N, fun k hk j => ?_⟩
    rcases lt_or_ge j 0 with hj | hj
    · rw [T.zcoeff_of_neg _ hj, norm_zero, zero_mul]; exact hε.le
    · lift j to ℕ using hj
      rw [zcoeff_natCast, zpow_natCast]; exact hN k hk j
  have hyconv : ConvergesAt (T.zcoeff y) ρ := by
    refine convergesAt_of_eventually hρ0 (T.zcoeff_neg_exists _) fun ε hε => ?_
    obtain ⟨N, hN⟩ := hwy' ε hε
    obtain ⟨N', hN'⟩ := exists_prefix_small hρ0 hρ1 (hx N) hε
    refine ⟨N', fun n hn => ?_⟩
    have hb : 0 ≤ ε / ρ ^ n := div_nonneg hε.le (zpow_pos hρ0 n).le
    have := T.norm_zcoeff_add_le (x := x N) (y := -(x N - y)) (n := n) hb
      (fun m hm => by rw [le_div_iff₀ (zpow_pos hρ0 n)]; exact hN' n hn m hm)
      (fun m hm => T.norm_zcoeff_neg_le hb fun i hi =>
        norm_le_div_of_weight hρ0 hρ1.le (hi.trans hm) (hN N le_rfl i))
    rw [show x N + -(x N - y) = y by ring, le_div_iff₀ (zpow_pos hρ0 n)] at this
    exact this
  refine ⟨hyconv, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hwy' ε hε
  exact ⟨N, fun k hk => gaussNorm_le fun j => hN k hk j⟩

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem upperPart_eq_algebraMap (b : T.B) : ∃ w : Γ, T.upperPart b = algebraMap Γ T.B w := by
  obtain ⟨w, hw⟩ := T.mem_span_pow.1 (T.sub_partialSum_mem (T.num b) (T.den b))
  refine ⟨w, ?_⟩
  rw [upperPart, hw, map_mul, map_pow]
  calc algebraMap Γ T.B T.π ^ T.den b * algebraMap Γ T.B w * IsLocalization.Away.invSelf T.π ^ T.den b
      = algebraMap Γ T.B w * (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) ^ T.den b := by
        ring
    _ = algebraMap Γ T.B w := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]

variable {T}

theorem gaussNorm_lowerPart_le_mul {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r')
    (hle : r' ≤ r) (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.lowerPart b)) r ≤ (r' / r) * gaussNorm (T.coeffB b) r' := by
  have hr0 : 0 < r := h0.trans_le hle
  refine gaussNorm_le fun n => ?_
  rw [coeffB_lowerPart]
  split_ifs with hn
  · have hq : 1 ≤ r / r' := (one_le_div h0).2 hle
    have hpow : (r / r') ^ n ≤ (r / r') ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq (by omega)
    rw [zpow_neg_one, inv_div] at hpow
    have h3 : r ^ n ≤ (r' / r) * r' ^ n := by
      calc r ^ n = (r / r') ^ n * r' ^ n := by
            rw [div_zpow, div_mul_cancel₀ _ (zpow_pos h0 n).ne']
        _ ≤ (r' / r) * r' ^ n := mul_le_mul_of_nonneg_right hpow (zpow_pos h0 n).le
    calc ‖T.coeffB b n‖ * r ^ n ≤ ‖T.coeffB b n‖ * ((r' / r) * r' ^ n) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (r' / r) * (‖T.coeffB b n‖ * r' ^ n) := by ring
      _ ≤ (r' / r) * gaussNorm (T.coeffB b) r' :=
          mul_le_mul_of_nonneg_left ((hb r' h0 h1).le_gaussNorm n) (by positivity)
  · rw [norm_zero, zero_mul]; exact mul_nonneg (by positivity) (gaussNorm_nonneg h0)

theorem exists_rpow_small {σ γ C η : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ t, 0 < t ∧ t ≤ σ ∧ C * t ^ γ ≤ η := by
  set a : ℝ := η / (C + 1) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min σ (a ^ γ⁻¹), lt_min hσ (Real.rpow_pos_of_pos ha0 _), min_le_left _ _, ?_⟩
  have ht0 : 0 ≤ min σ (a ^ γ⁻¹) := (lt_min hσ (Real.rpow_pos_of_pos ha0 _)).le
  have h1 : (min σ (a ^ γ⁻¹)) ^ γ ≤ a := by
    calc (min σ (a ^ γ⁻¹)) ^ γ ≤ (a ^ γ⁻¹) ^ γ :=
          Real.rpow_le_rpow ht0 (min_le_right _ _) hγ.le
      _ = a := Real.rpow_inv_rpow ha0.le hγ.ne'
  calc C * (min σ (a ^ γ⁻¹)) ^ γ ≤ C * a := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ (C + 1) * a := by nlinarith
    _ = η := by rw [ha]; field_simp

theorem exists_gamma_of_extNorm_le [CompleteSpace L] {σ : Set.Ioo (0 : ℝ) 1} (x : T.RobbaExt σ) {C β : ℝ} (b : ℕ)
    (hb : β - 1 < b) (hx : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s x ≤ C * (s : ℝ) ^ (-β)) :
    ∃ w : Γ, ∃ hw : algebraMap Γ T.B w ∈ T.Econ σ,
      T.ofAll _ (convAll_π_pow b) σ * x = ((⟨algebraMap Γ T.B w, hw⟩ : T.Econ σ) : T.RobbaExt σ) := by
  have hσ0 : (0 : ℝ) < σ := σ.2.1
  have hσ1 : (σ : ℝ) < 1 := σ.2.2
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set y := T.ofAll _ (convAll_π_pow b) σ * x with hydef

  have hy : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s y ≤ C' * (s : ℝ) ^ ((b : ℝ) - β) := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2.1
    rw [hydef, extNorm_mul, extNorm_ofAll, (gaussNorm_π_pow b hs0).2]
    have hxs : T.extNorm σ s x ≤ C' * (s : ℝ) ^ (-β) :=
      (hx s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0.le _))
    calc (s : ℝ) ^ b * T.extNorm σ s x ≤ (s : ℝ) ^ b * (C' * (s : ℝ) ^ (-β)) :=
          mul_le_mul_of_nonneg_left hxs (pow_nonneg hs0.le _)
      _ = C' * ((s : ℝ) ^ (b : ℝ) * (s : ℝ) ^ (-β)) := by rw [Real.rpow_natCast]; ring
      _ = C' * (s : ℝ) ^ ((b : ℝ) - β) := by rw [← Real.rpow_add hs0, sub_eq_add_neg]

  let r : ℕ → Set.Ioc (0 : ℝ) σ := fun j =>
    ⟨σ / (j + 1), by positivity, div_le_self hσ0.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])⟩
  let ε : ℕ → ℝ := fun j => 1 / (j + 1)
  have hε0 : ∀ j, 0 < ε j := fun j => by positivity
  choose d hd hdx using fun j : ℕ => exists_approx_convAll y (r j) (hε0 j)
  choose w hw using fun j => T.upperPart_eq_algebraMap (d j)
  have hr_anti : ∀ {j k : ℕ}, j ≤ k → ((r k : ℝ)) ≤ r j := fun {j k} hjk => by
    show σ / ((k : ℝ) + 1) ≤ σ / ((j : ℝ) + 1)
    exact div_le_div_of_nonneg_left hσ0.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hε_anti : ∀ {j k : ℕ}, j ≤ k → ε k ≤ ε j := fun {j k} hjk => by
    show 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1)
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hsmall : ∀ η > (0 : ℝ), ∀ t > (0 : ℝ), ∃ J, ∀ j ≥ J, (r j : ℝ) ≤ t ∧ ε j ≤ η := by
    intro η hη t ht
    obtain ⟨J, hJ⟩ := exists_nat_gt (max (σ / t) (1 / η))
    refine ⟨J, fun j hj => ⟨?_, ?_⟩⟩
    · refine (hr_anti hj).trans ?_
      show σ / ((J : ℝ) + 1) ≤ t
      rw [div_le_iff₀ (by positivity)]
      have : σ / t < J := lt_of_le_of_lt (le_max_left _ _) hJ
      rw [div_lt_iff₀ ht] at this
      nlinarith
    · refine (hε_anti hj).trans ?_
      show 1 / ((J : ℝ) + 1) ≤ η
      rw [div_le_iff₀ (by positivity)]
      have : 1 / η < J := lt_of_le_of_lt (le_max_right _ _) hJ
      rw [div_lt_iff₀ hη] at this
      nlinarith

  have hdt : ∀ j (t : Set.Ioc (0 : ℝ) σ), (r j : ℝ) ≤ t →
      gaussNorm (T.coeffB (d j)) t ≤ max (C' * (t : ℝ) ^ ((b : ℝ) - β)) (ε j) := by
    intro j t ht
    rw [← extNorm_ofAll (hd j) t]
    have e : T.ofAll (d j) (hd j) σ = y + -(y - T.ofAll (d j) (hd j) σ) := by ring
    rw [e]
    refine (T.extNorm_add_le t _ _).trans (max_le_max (hy t) ?_)
    rw [extNorm_neg]; exact hdx j t ht

  have hA : ∀ η > (0 : ℝ), ∃ J, ∀ j ≥ J, gaussNorm (T.coeffB (T.lowerPart (d j))) σ ≤ η := by
    intro η hη
    have hγ : 0 < (b : ℝ) - β + 1 := by linarith
    obtain ⟨t, ht0, htσ, htC⟩ := exists_rpow_small hσ0 hγ (div_nonneg hC'0 hσ0.le) hη
    obtain ⟨J, hJ⟩ := hsmall η hη t ht0
    refine ⟨J, fun j hj => ?_⟩
    obtain ⟨hrj, hεj⟩ := hJ j hj
    have h1 := gaussNorm_lowerPart_le_mul (hd j) ht0 htσ (htσ.trans_lt hσ1)
    have h2 := hdt j ⟨t, ht0, htσ⟩ hrj
    refine h1.trans ?_
    have htσ' : t / σ ≤ 1 := (div_le_one hσ0).2 htσ
    calc t / σ * gaussNorm (T.coeffB (d j)) t
        ≤ t / σ * max (C' * t ^ ((b : ℝ) - β)) (ε j) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max (C' / σ * t ^ ((b : ℝ) - β + 1)) (ε j) := by
          rw [mul_max_of_nonneg _ _ (by positivity)]
          refine max_le_max (le_of_eq ?_) ?_
          · rw [Real.rpow_add ht0, Real.rpow_one]; field_simp
          · calc t / σ * ε j ≤ 1 * ε j := mul_le_mul_of_nonneg_right htσ' (hε0 j).le
              _ = ε j := one_mul _
      _ ≤ η := max_le htC hεj

  have hup : ∀ j, T.ConvAll (algebraMap Γ T.B (w j)) := fun j => by
    rw [← hw j]; exact (hd j).upperPart
  have hconv : ∀ j, ConvergesAt (T.zcoeff (w j)) σ := fun j => by
    have := hup j σ hσ0 hσ1
    rwa [coeffB_algebraMap] at this
  have hsplit : ∀ j, T.ofAll (d j) (hd j) σ =
      T.ofAll _ (hd j).lowerPart σ + T.ofAll _ (hup j) σ := by
    intro j
    rw [← ofAll_add]
    exact ofAll_congr _ _ (by rw [← hw j, lowerPart_add_upperPart]) σ
  have hwsub : ∀ j k, gaussNorm (T.zcoeff (w j - w k)) σ =
      T.extNorm σ (topRad σ) (T.ofAll _ (hup j) σ - T.ofAll _ (hup k) σ) := by
    intro j k
    rw [← gaussNorm_ofAll_sub (hup j) (hup k), ← map_sub, coeffB_algebraMap]
    rfl

  have hB : ∀ η > (0 : ℝ), ∃ N, ∀ j ≥ N, ∀ k ≥ N, gaussNorm (T.zcoeff (w j - w k)) σ ≤ η := by
    intro η hη
    obtain ⟨J1, hJ1⟩ := hA η hη
    obtain ⟨J2, hJ2⟩ := hsmall η hη σ hσ0
    refine ⟨max J1 J2, fun j hj k hk => ?_⟩
    rw [hwsub]
    have e : T.ofAll _ (hup j) σ - T.ofAll _ (hup k) σ =
        -(y - T.ofAll (d j) (hd j) σ) + (y - T.ofAll (d k) (hd k) σ) +
          (T.ofAll _ (hd k).lowerPart σ - T.ofAll _ (hd j).lowerPart σ) := by
      rw [hsplit j, hsplit k]; ring
    rw [e]
    have hlow : ∀ i ≥ J1, T.extNorm σ (topRad σ) (T.ofAll _ (hd i).lowerPart σ) ≤ η := fun i hi => by
      rw [extNorm_ofAll]; exact hJ1 i hi
    have happ : ∀ i ≥ J2, T.extNorm σ (topRad σ) (y - T.ofAll (d i) (hd i) σ) ≤ η := fun i hi =>
      (hdx i (topRad σ) (hJ2 i hi).1).trans (hJ2 i hi).2
    refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
    · rw [extNorm_neg]; exact happ j (le_of_max_le_right hj)
    · exact happ k (le_of_max_le_right hk)
    · rw [sub_eq_add_neg]
      refine (T.extNorm_add_le _ _ _).trans (max_le (hlow k (le_of_max_le_left hk)) ?_)
      rw [extNorm_neg]; exact hlow j (le_of_max_le_left hj)

  obtain ⟨-, hWc, hWlim⟩ := T.exists_limit_gaussNorm hσ0 hσ1 hconv hB
  set W := T.coeffLim w with hWdef
  have hWE : algebraMap Γ T.B W ∈ T.Econ σ := by
    rw [mem_Econ, coeffB_algebraMap]; exact hWc
  refine ⟨W, hWE, ?_⟩

  rw [← sub_eq_zero, ← T.extNorm_eq_zero_iff (topRad σ)]
  refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) (T.extNorm_nonneg _ _)
  rw [zero_add]
  obtain ⟨J1, hJ1⟩ := hA η hη
  obtain ⟨J2, hJ2⟩ := hsmall η hη σ hσ0
  obtain ⟨J3, hJ3⟩ := hWlim η hη
  set j := max J1 (max J2 J3)
  have e : y - ((⟨algebraMap Γ T.B W, hWE⟩ : T.Econ σ) : T.RobbaExt σ) =
      (y - T.ofAll (d j) (hd j) σ) + T.ofAll _ (hd j).lowerPart σ +
        (T.ofAll _ (hup j) σ - ((⟨algebraMap Γ T.B W, hWE⟩ : T.Econ σ) : T.RobbaExt σ)) := by
    rw [hsplit j]; ring
  rw [e]
  refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
  · exact (hdx j (topRad σ) (hJ2 j (le_max_of_le_right (le_max_left _ _))).1).trans
      (hJ2 j (le_max_of_le_right (le_max_left _ _))).2
  · rw [extNorm_ofAll]; exact hJ1 j (le_max_left _ _)
  · rw [ofAll, ← Completion.coe_sub, extNorm_coe]
    have := hJ3 j (le_max_of_le_right (le_max_right _ _))
    rw [← coeffB_algebraMap, map_sub] at this
    exact this

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

abbrev πB : T.B := algebraMap Γ T.B T.π

theorem πB_ne_zero : T.πB ≠ 0 := by
  have := T.nontrivial_B
  exact (IsLocalization.Away.algebraMap_isUnit T.π).ne_zero

def DigLe (x : Γ) (Θ : ℝ) : Prop := ∀ n, ‖T.coeff x n‖ ≤ Θ

def IsUnitTerm (P : T.B) (i : ℤ) : Prop :=
  ∃ U ∈ T.int, ‖T.red U‖ = 1 ∧ P = T.πB ^ i * algebraMap Γ T.B U

variable {T}

theorem digLe_iff_prefixLe {x : Γ} {Θ : ℝ} : T.DigLe x Θ ↔ ∀ n, T.PrefixLe x n Θ :=
  ⟨fun h _ m _ => h m, fun h n => h n n le_rfl⟩

theorem DigLe.mono {x : Γ} {Θ Θ' : ℝ} (h : T.DigLe x Θ) (hΘ : Θ ≤ Θ') : T.DigLe x Θ' :=
  fun n => (h n).trans hΘ

theorem DigLe.add {x y : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hy : T.DigLe y Θ) : T.DigLe (x + y) Θ :=
  digLe_iff_prefixLe.2 fun n =>
    T.prefixLe_add (digLe_iff_prefixLe.1 hx n) (digLe_iff_prefixLe.1 hy n)

theorem digLe_teich {a : L} {Θ : ℝ} (h : ‖a‖ ≤ Θ) : T.DigLe (T.teich a) Θ := fun n => by
  rw [T.coeff_teich]
  split_ifs
  · exact h
  · simpa using (norm_nonneg a).trans h

theorem digLe_π_mul_iff {x : Γ} {Θ : ℝ} (hΘ : 0 ≤ Θ) : T.DigLe (T.π * x) Θ ↔ T.DigLe x Θ := by
  constructor
  · intro h n; rw [← T.coeff_π_mul_succ]; exact h (n + 1)
  · intro h n
    cases n with
    | zero => rw [T.coeff_zero, map_mul, T.red_π, zero_mul, norm_zero]; exact hΘ
    | succ n => rw [T.coeff_π_mul_succ]; exact h n

theorem digLe_one_of_mem_int {x : Γ} (hx : x ∈ T.int) : T.DigLe x 1 := T.mem_int_iff.1 hx

theorem DigLe.convergesAt {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ConvergesAt (T.zcoeff x) r :=
  T.convergesAt_of_forall_weight_le (ρ := 1) (Y := Θ) hr0 hr1 fun n => by
    rw [one_pow, mul_one]; exact hx n

theorem DigLe.gaussNorm_le {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) : gaussNorm (T.zcoeff x) r ≤ Θ :=
  ciSup_le fun j => T.zcoeff_weight_le hΘ (fun n =>
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr0.le hr1.le)).trans (hx n)) j

theorem DigLe.convAll {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) : T.ConvAll (algebraMap Γ T.B x) :=
  fun _ hr0 hr1 => by rw [T.coeffB_algebraMap]; exact hx.convergesAt hr0 hr1

theorem convAll_πB_zpow (i : ℤ) : T.ConvAll (T.πB ^ i) := by
  have hinv : (T.πB)⁻¹ = IsLocalization.Away.invSelf T.π :=
    inv_eq_of_mul_eq_one_right (IsLocalization.Away.mul_invSelf T.π)
  have hc : T.ConvAll (IsLocalization.Away.invSelf T.π) := fun ρ _ _ => by
    rw [T.coeffB_invSelf]; exact convergesAt_pi_single _ _ _
  have hpow : ∀ n : ℕ, T.ConvAll ((IsLocalization.Away.invSelf T.π) ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      simpa using (convAll_π_pow (T := T) 0)
    | succ n ih => rw [pow_succ]; exact ih.mul hc
  rcases i with n | n
  · simpa [zpow_natCast] using (convAll_π_pow (T := T) n)
  · rw [zpow_negSucc, ← inv_pow, hinv]; exact hpow _

theorem convAll_algebraMap_of_mem_int {U : Γ} (hU : U ∈ T.int) :
    T.ConvAll (algebraMap Γ T.B U) := (digLe_one_of_mem_int hU).convAll

theorem coeffB_πB_zpow_mul (i : ℤ) (x : Γ) :
    T.coeffB (T.πB ^ i * algebraMap Γ T.B x) = fun k => T.zcoeff x (k - i) := by
  set N := (-i).toNat
  set M := i.toNat
  have hNM : i + (N : ℤ) = M := by have := Int.toNat_sub_toNat_neg i; omega
  have h : T.πB ^ i * algebraMap Γ T.B x * algebraMap Γ T.B T.π ^ N =
      algebraMap Γ T.B (T.π ^ M * x) := by
    rw [map_mul, map_pow, mul_right_comm, ← zpow_natCast, ← zpow_add₀ T.πB_ne_zero, hNM,
      zpow_natCast]
  rw [T.coeffB_eq h]
  funext k
  have := T.zcoeff_π_pow_mul M x (k - i)
  rw [show k - i + (M : ℤ) = k + (N : ℤ) by omega] at this
  exact this

theorem isUnitTerm_one : T.IsUnitTerm 1 0 :=
  ⟨1, T.int.one_mem, by simp, by simp⟩

theorem isUnitTerm_πB_zpow (i : ℤ) : T.IsUnitTerm (T.πB ^ i) i :=
  ⟨1, T.int.one_mem, by simp, by simp⟩

theorem isUnitTerm_algebraMap {U : Γ} (hU : U ∈ T.int) (h1 : ‖T.red U‖ = 1) :
    T.IsUnitTerm (algebraMap Γ T.B U) 0 :=
  ⟨U, hU, h1, by simp⟩

theorem IsUnitTerm.congr_idx {P : T.B} {i j : ℤ} (h : T.IsUnitTerm P i) (hij : i = j) :
    T.IsUnitTerm P j := hij ▸ h

theorem IsUnitTerm.mul {P P' : T.B} {i i' : ℤ} (h : T.IsUnitTerm P i) (h' : T.IsUnitTerm P' i') :
    T.IsUnitTerm (P * P') (i + i') := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  obtain ⟨U', hU', hU1', rfl⟩ := h'
  refine ⟨U * U', T.int.mul_mem hU hU', by rw [map_mul, norm_mul, hU1, hU1', one_mul], ?_⟩
  rw [zpow_add₀ T.πB_ne_zero, map_mul]; ring

theorem IsUnitTerm.inv {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.IsUnitTerm P⁻¹ (-i) := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  obtain ⟨V, hV, hUV⟩ := T.exists_inv_mem_int hU hU1
  have hV1 : ‖T.red V‖ = 1 := by
    have := congrArg (fun y => ‖T.red y‖) hUV
    simpa [map_mul, norm_mul, hU1] using this
  refine ⟨V, hV, hV1, ?_⟩
  have hUVB : algebraMap Γ T.B U * algebraMap Γ T.B V = 1 := by rw [← map_mul, hUV, map_one]
  rw [mul_inv, zpow_neg, inv_eq_of_mul_eq_one_right hUVB]

theorem IsUnitTerm.ne_zero {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : P ≠ 0 := by
  intro h0
  obtain ⟨U, hU, hU1, hP⟩ := h.inv
  rw [h0, inv_zero] at hP
  have hU0 : algebraMap Γ T.B U = 0 := by
    rcases mul_eq_zero.1 hP.symm with h1 | h1
    · exact absurd h1 (zpow_ne_zero _ T.πB_ne_zero)
    · exact h1
  have : U = 0 := T.algebraMap_injective (by rw [hU0, map_zero])
  rw [this, map_zero, norm_zero] at hU1
  exact zero_ne_one hU1

theorem IsUnitTerm.zpow {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) (k : ℤ) :
    T.IsUnitTerm (P ^ k) (k * i) := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero]; exact isUnitTerm_one.congr_idx (by ring)
  | succ k ih => rw [zpow_add_one₀ h.ne_zero]; exact (ih.mul h).congr_idx (by ring)
  | pred k ih =>
    rw [zpow_sub_one₀ h.ne_zero]; exact (ih.mul h.inv).congr_idx (by ring)

theorem IsUnitTerm.convAll {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.ConvAll P := by
  obtain ⟨U, hU, -, rfl⟩ := h
  exact (convAll_πB_zpow i).mul (convAll_algebraMap_of_mem_int hU)

theorem gaussNorm_single_zero (c : L) (r : ℝ) :
    gaussNorm (Pi.single 0 c) r = ‖c‖ := by
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · calc ‖c‖ = ‖(Pi.single (0 : ℤ) c : ℤ → L) 0‖ * r ^ (0 : ℤ) := by simp
      _ ≤ gaussNorm (Pi.single 0 c) r :=
        le_ciSup (f := fun n : ℤ => ‖(Pi.single (0 : ℤ) c : ℤ → L) n‖ * r ^ n)
          (convergesAt_pi_single (0 : ℤ) c r).bddAbove 0

theorem IsUnitTerm.gaussNorm_mul_teich {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) (a : L) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    gaussNorm (T.coeffB (P * algebraMap Γ T.B (T.teich a))) r = r ^ i * ‖a‖ := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  rw [mul_assoc, ← map_mul, coeffB_πB_zpow_mul]
  have e : (fun k => T.zcoeff (U * T.teich a) (k - i)) =
      fun k => T.zcoeff (U * T.teich a) (k + -i) := by funext k; rw [sub_eq_add_neg]
  rw [e, gaussNorm_shift hr0, neg_neg,
    T.gaussNorm_zcoeff_mul hr0 hr1 (T.convergesAt_of_mem_int hU hr0 hr1)
      ((digLe_teich (T := T) (le_refl ‖a‖)).convergesAt hr0 hr1),
    T.gaussNorm_eq_one_of_mem_int hU hU1 hr0 hr1, T.zcoeff_teich, gaussNorm_single_zero a r]
  ring

namespace TeichFrob

variable (F : T.TeichFrob)

theorem IsUnitTerm.toB {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.IsUnitTerm (F.toB P) i := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  have hπt : T.IsUnitTerm (F.toB T.πB) 1 := by
    have h1 := (isUnitTerm_πB_zpow (T := T) 1).mul (isUnitTerm_algebraMap F.u_mem_int F.norm_red_u)
    rw [zpow_one, add_zero] at h1
    rw [F.toB_algebraMap, F.φ_π, map_mul]
    exact h1
  have hUt : T.IsUnitTerm (F.toB (algebraMap Γ T.B U)) 0 := by
    rw [F.toB_algebraMap]
    refine isUnitTerm_algebraMap (F.map_int U hU) ?_
    rw [F.red_φ, norm_pow, hU1, one_pow]
  rw [map_mul, map_zpow₀]
  exact ((hπt.zpow i).mul hUt).congr_idx (by ring)

def twist (t : T.B) (ht : t ≠ 0) : AddAut T.B where
  toFun b := t * F.toB b
  invFun b := F.toB.symm (t⁻¹ * b)
  left_inv b := by simp [ht]
  right_inv b := by simp [ht]
  map_add' b c := by simp [mul_add]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ0 : Set.Ioo (0 : ℝ) 1}

def smallSubgroup (I : Set (Set.Ioc (0 : ℝ) ρ0)) (hI : I.Finite) (ε : Set.Ioc (0 : ℝ) ρ0 → ℝ)
    (hε : ∀ i, 0 < ε i) : OpenAddSubgroup (T.RobbaExt ρ0) where
  carrier := {x | ∀ i ∈ I, T.extNorm ρ0 i x < ε i}
  zero_mem' := fun i _ => by rw [T.extNorm_zero]; exact hε i
  add_mem' := fun {a b} ha hb i hi =>
    (T.extNorm_add_le i a b).trans_lt (max_lt (ha i hi) (hb i hi))
  neg_mem' := fun {a} ha i hi => by rw [T.extNorm_neg]; exact ha i hi
  isOpen' := by
    have : {x : T.RobbaExt ρ0 | ∀ i ∈ I, T.extNorm ρ0 i x < ε i} =
        ⋂ i ∈ I, {x | T.extNorm ρ0 i x < ε i} := by
      ext x; simp
    rw [this]
    exact hI.isOpen_biInter fun i _ => isOpen_lt (T.continuous_extNorm i) continuous_const

theorem exists_radii_of_mem_nhds_zero {U : Set (T.RobbaExt ρ0)} (hU : U ∈ 𝓝 (0 : T.RobbaExt ρ0)) :
    ∃ I : Set (Set.Ioc (0 : ℝ) ρ0), I.Finite ∧ ∃ ε : Set.Ioc (0 : ℝ) ρ0 → ℝ, (∀ i, 0 < ε i) ∧
      ∀ x : T.RobbaExt ρ0, (∀ i ∈ I, T.extNorm ρ0 i x < ε i) → x ∈ U := by
  obtain ⟨V, hV, hVU⟩ := UniformSpace.mem_nhds_iff.1 hU
  obtain ⟨I, hI, ε, hε, h⟩ := T.exists_radii_of_mem_uniformity hV
  refine ⟨I, hI, ε, hε, fun x hx => hVU ?_⟩
  refine h 0 x fun i hi => ?_
  rw [zero_sub, T.extNorm_neg]; exact hx i hi

instance instNonarchimedeanAddGroupRobbaExt : NonarchimedeanAddGroup (T.RobbaExt ρ0) where
  is_nonarchimedean U hU := by
    obtain ⟨I, hI, ε, hε, h⟩ := T.exists_radii_of_mem_nhds_zero hU
    exact ⟨T.smallSubgroup I hI ε hε, fun x hx => h x hx⟩

variable {T}

theorem HasSum.res {ι : Type*} {f : ι → T.RobbaExt ρ0} {s : T.RobbaExt ρ0} (hs : HasSum f s)
    {ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    HasSum (fun i => T.res h (f i)) (T.res h s) :=
  hs.map (T.res h) (T.continuous_res h)

theorem HasSum.extFrob (F : T.TeichFrob) {ι : Type*} {f : ι → T.RobbaExt ρ0} {s : T.RobbaExt ρ0}
    (hs : HasSum f s) : HasSum (fun i => F.extFrob ρ0 (f i)) (F.extFrob ρ0 s) :=
  hs.map (F.extFrob ρ0) (F.continuous_extFrob ρ0)

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def fixRad : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

def tildeOf (b : T.B) (hb : T.ConvAll b) : T.RobbaTilde := T.ofRad fixRad (T.ofAll b hb fixRad)

variable {T}

theorem ofRad_ofAll_eq (b : T.B) (hb : T.ConvAll b) (σ σ' : Set.Ioo (0 : ℝ) 1) :
    T.ofRad σ (T.ofAll b hb σ) = T.ofRad σ' (T.ofAll b hb σ') := by
  let m : Set.Ioo (0 : ℝ) 1 := ⟨min σ σ', lt_min σ.2.1 σ'.2.1, (min_le_left _ _).trans_lt σ.2.2⟩
  have h1 : (m : ℝ) ≤ σ := min_le_left _ _
  have h2 : (m : ℝ) ≤ σ' := min_le_right _ _
  rw [← T.ofRad_res h1, res_ofAll, ← T.ofRad_res h2, res_ofAll]

theorem tildeOf_eq (b : T.B) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.tildeOf b hb = T.ofRad σ (T.ofAll b hb σ) := ofRad_ofAll_eq b hb fixRad σ

theorem tildeOf_congr {b b' : T.B} (hb : T.ConvAll b) (hb' : T.ConvAll b') (h : b = b') :
    T.tildeOf b hb = T.tildeOf b' hb' := by subst h; rfl

theorem tildeOf_mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) :
    T.tildeOf (a * b) (ha.mul hb) = T.tildeOf a ha * T.tildeOf b hb := by
  rw [tildeOf, tildeOf, tildeOf, ofAll_mul, map_mul]

theorem convAll_πB : T.ConvAll T.πB := by
  have := convAll_πB_zpow (T := T) 1
  rwa [zpow_one] at this

theorem tildeOf_πB : T.tildeOf T.πB convAll_πB = T.πTilde := by
  rw [tildeOf, ← T.ofRad_πExt fixRad]
  rfl

namespace TeichFrob

variable (F : T.TeichFrob)

theorem tildeFrob_tildeOf {b : T.B} (hb : T.ConvAll b) :
    F.tildeFrob (T.tildeOf b hb) = T.tildeOf (F.toB b) (F.convAll_toB hb) := by
  rw [tildeOf, tildeOf, F.tildeFrob_ofRad, F.extFrob_ofAll]
  exact ofRad_ofAll_eq _ _ _ _

end TeichFrob

namespace TeichFrob

variable (F : T.TeichFrob)

end TeichFrob

theorem DigLe.π_pow_mul {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) (N : ℕ) :
    T.DigLe (T.π ^ N * x) Θ := by
  induction N with
  | zero => simpa using hx
  | succ N ih => rw [pow_succ', mul_assoc]; exact (digLe_π_mul_iff hΘ).2 ih

theorem exists_eq_π_pow_mul_digLe {x : Γ} {M : ℕ} (hx : x ∈ Ideal.span {T.π ^ M}) {Θ : ℝ}
    (hd : T.DigLe x Θ) : ∃ x', x = T.π ^ M * x' ∧ T.DigLe x' Θ := by
  obtain ⟨x', rfl⟩ := T.mem_span_pow.1 hx
  refine ⟨x', rfl, fun n => ?_⟩
  have := hd (n + M)
  rwa [T.coeff_π_pow_mul_add] at this

theorem gaussNorm_π_pow_mul_le {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) (M : ℕ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) : gaussNorm (T.zcoeff (T.π ^ M * x)) r ≤ r ^ M * Θ := by
  have hπ : ConvergesAt (T.zcoeff (T.π ^ M)) r := by
    rw [T.zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
  rw [T.gaussNorm_zcoeff_mul hr0 hr1 hπ (hx.convergesAt hr0 hr1), T.zcoeff_π_pow,
    gaussNorm_pi_single _ _ hr0, norm_one, one_mul, zpow_natCast]
  exact mul_le_mul_of_nonneg_left (hx.gaussNorm_le hΘ hr0 hr1) (pow_nonneg hr0.le M)

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem norm_le_one_of_forall_weight_le {a : L} {n : ℕ}
    (h : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ‖a‖ * ρ ^ n ≤ 1) : ‖a‖ ≤ 1 := by
  have ht : Tendsto (fun ρ : ℝ => ‖a‖ * ρ ^ n) (𝓝[<] 1) (𝓝 (‖a‖ * 1 ^ n)) :=
    ((continuous_const.mul (continuous_pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [one_pow, mul_one] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
  exact h ρ hρ.1 hρ.2

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem exists_int_φ_eq_u_mul [IsAlgClosed L] (ha : 0 < F.a) :
    ∃ y ∈ T.int, ‖T.red y‖ = 1 ∧ F.φ y = F.u * y := by
  have hq := F.two_le_q ha
  have hu0 : ∀ n : ℕ, T.red F.u ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero))
  have hw0 : T.red F.u ≠ 0 := by simpa using hu0 1
  choose r hr hr0 using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hu0 n) (T.red F.u) e
  set y := T.ofCoeff (F.approxCoeff F.u r) with hydef

  have hdig : ∀ n, ‖T.coeff y n‖ ≤ 1 := by
    intro n
    rw [hydef, T.coeff_ofCoeff]
    refine norm_le_one_of_forall_weight_le (n := n) fun ρ hρ0 hρ1 => ?_
    have hw := T.convergesAt_of_mem_int F.u_mem_int hρ0 hρ1
    have hW : gaussNorm (T.zcoeff F.u) ρ ≤ (1 : ℝ) ^ (p ^ F.a - 1) := by
      rw [T.gaussNorm_eq_one_of_mem_int F.u_mem_int F.norm_red_u hρ0 hρ1, one_pow]
    exact approxCoeff_weight_le ha hr hρ0 hρ1 hw zero_le_one hW n
  have hyint : y ∈ T.int := T.mem_int_iff.2 hdig

  have hy0 : T.red y = r 0 0 := by
    rw [← T.coeff_zero, hydef, T.coeff_ofCoeff]
    simp [approxCoeff, approx]
  have hr00 : r 0 0 ≠ 0 := hr0 0 0 rfl hw0
  have hroot := hr 0 0
  simp only [pow_zero, one_mul, add_zero] at hroot
  have hnorm : ‖r 0 0‖ = 1 := by
    have hle : ‖r 0 0‖ ≤ 1 := by rw [← hy0, ← T.coeff_zero]; exact hdig 0
    have hq1 : r 0 0 ^ (p ^ F.a - 1) = T.red F.u := by
      have : r 0 0 ^ p ^ F.a = r 0 0 ^ (p ^ F.a - 1) * r 0 0 := by
        rw [← pow_succ]; congr 1; omega
      rw [this] at hroot
      exact mul_right_cancel₀ hr00 (by linear_combination hroot)
    have h1 : ‖r 0 0‖ ^ (p ^ F.a - 1) = 1 := by rw [← norm_pow, hq1, F.norm_red_u]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1
  refine ⟨y, hyint, by rw [hy0, hnorm], ?_⟩

  have hall : ∀ n, F.φ y - F.u * y ∈ Ideal.span {T.π ^ n} := fun n => by
    have h1 : y - F.approx F.u r n ∈ Ideal.span {T.π ^ n} := by
      rw [F.approx_eq_finSum]; exact T.mk_sub_finSum_mem _ n
    have : F.φ y - F.u * y = (F.φ (F.approx F.u r n) - F.u * F.approx F.u r n) +
        (F.φ (y - F.approx F.u r n) - F.u * (y - F.approx F.u r n)) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (approx_mem hr n) (sub_mem (F.φ_mem_span_pow h1) (Ideal.mul_mem_left _ _ h1))
  have h0 : F.φ y - F.u * y = 0 := T.eq_of_coeff_eq (funext fun n => by
    rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
  exact sub_eq_zero.1 h0

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

theorem rpow_interp_eq {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ (1 - t) * b ^ t) ^ c = (a ^ c) ^ (1 - t) * (b ^ c) ^ t := by
  rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _), ← Real.rpow_mul ha,
    ← Real.rpow_mul hb, ← Real.rpow_mul ha, ← Real.rpow_mul hb, mul_comm (1 - t), mul_comm t]

theorem eq_rpow_of_logConvex {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {Q : ℕ} (hQ : 2 ≤ Q)
    (f : ℝ → ℝ) (hpos : ∀ s, 0 < s → s ≤ σ → 0 < f s)
    (hpow : ∀ s, 0 < s → s ≤ σ → f (s ^ Q) = f s ^ Q)
    (hconv : ∀ a r b t : ℝ, 0 < a → a ≤ r → r ≤ b → b ≤ σ → 0 ≤ t → t ≤ 1 →
      r = a ^ (1 - t) * b ^ t → f r ≤ f a ^ (1 - t) * f b ^ t) :
    ∃ c : ℝ, ∀ s, 0 < s → s ≤ σ → f s = s ^ c := by
  have hlogσ : Real.log σ ≠ 0 := (Real.log_neg hσ0 hσ1).ne
  set c := Real.log (f σ) / Real.log σ with hc
  refine ⟨c, ?_⟩
  have hfσ : f σ = σ ^ c := by
    rw [Real.rpow_def_of_pos hσ0, hc, mul_div_cancel₀ _ hlogσ, Real.exp_log (hpos σ hσ0 le_rfl)]
  have hpowQ : ∀ x : ℝ, 0 ≤ x → (x ^ Q) ^ c = (x ^ c) ^ Q := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]
  have hσQ : ∀ J : ℕ, 0 < σ ^ Q ^ J ∧ σ ^ Q ^ J ≤ σ ∧ f (σ ^ Q ^ J) = (σ ^ Q ^ J) ^ c := by
    intro J
    induction J with
    | zero => simp only [pow_zero, pow_one]; exact ⟨hσ0, le_rfl, hfσ⟩
    | succ J ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have e : σ ^ Q ^ (J + 1) = (σ ^ Q ^ J) ^ Q := by rw [← pow_mul, ← pow_succ]
      refine ⟨pow_pos hσ0 _, pow_le_of_le_one hσ0.le hσ1.le (by positivity), ?_⟩
      rw [e, hpow _ h0 h1, h2, hpowQ _ h0.le]

  have hupper : ∀ s, 0 < s → s ≤ σ → f s ≤ s ^ c := by
    intro s hs0 hsσ
    rcases hsσ.lt_or_eq with hlt | heq
    · obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hs0 hσ1
      have hJ' : σ ^ Q ^ J < s := by
        refine lt_of_le_of_lt (pow_le_pow_of_le_one hσ0.le hσ1.le ?_) hJ
        exact (Nat.lt_pow_self (by omega)).le
      obtain ⟨t, ht0, ht1, hst⟩ := TeichLift.exists_interp_exponent (hσQ J).1 hJ' hlt
      have h := hconv _ s σ t (hσQ J).1 hJ'.le hlt.le le_rfl ht0.le ht1.le hst
      rw [(hσQ J).2.2, hfσ, ← rpow_interp_eq (hσQ J).1.le hσ0.le, ← hst] at h
      exact h
    · rw [heq, hfσ]

  have hlower1 : ∀ s, 0 < s → s ≤ σ ^ Q → s ^ c ≤ f s := by
    intro s hs0 hsQ
    have hσQσ : σ ^ Q < σ := pow_lt_self_of_lt_one₀ hσ0 hσ1 (by omega)
    rcases hsQ.lt_or_eq with hlt | heq
    · obtain ⟨t, ht0, ht1, hst⟩ := TeichLift.exists_interp_exponent hs0 hlt hσQσ
      have h := hconv s (σ ^ Q) σ t hs0 hlt.le hσQσ.le le_rfl ht0.le ht1.le hst
      have h1 := (hσQ 1).2.2
      rw [pow_one] at h1
      rw [h1, hfσ, hst, rpow_interp_eq hs0.le hσ0.le] at h
      by_contra hcon
      rw [not_le] at hcon
      have hlt2 : f s ^ (1 - t) < (s ^ c) ^ (1 - t) :=
        Real.rpow_lt_rpow (hpos s hs0 (hsQ.trans hσQσ.le)).le hcon (by linarith)
      have := mul_lt_mul_of_pos_right hlt2 (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hσ0 c) t)
      linarith
    · have h1 := (hσQ 1).2.2
      rw [pow_one] at h1
      rw [heq, h1]
  have hlower : ∀ s, 0 < s → s ≤ σ → s ^ c ≤ f s := by
    intro s hs0 hsσ
    rcases le_or_gt s (σ ^ Q) with h | h
    · exact hlower1 s hs0 h
    · have hsQ : s ^ Q ≤ σ ^ Q := pow_le_pow_left₀ hs0.le hsσ Q
      have h2 := hlower1 (s ^ Q) (pow_pos hs0 Q) hsQ
      rw [hpow s hs0 hsσ, hpowQ s hs0.le] at h2
      exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hs0.le c) (hpos s hs0 hsσ).le
        (by omega)).1 h2
  intro s hs0 hsσ
  exact le_antisymm (hupper s hs0 hsσ) (hlower s hs0 hsσ)

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem tildeOf_one : T.tildeOf 1 (by simpa using (convAll_π_pow (T := T) 0)) = 1 := by
  show T.ofRad fixRad ((1 : T.Econ fixRad) : T.RobbaExt fixRad) = 1
  rw [Completion.coe_one, map_one]

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_ofRad_of_fixed {x : T.RobbaTilde} (hx : F.tildeFrob x = x) :
    ∃ σ : Set.Ioo (0 : ℝ) 1, ∃ x₀ : T.RobbaExt σ, T.ofRad σ x₀ = x ∧
      F.extFrob σ x₀ = T.res (F.powRadius_le_self σ) x₀ := by
  obtain ⟨σ, x₀, rfl⟩ := T.exists_ofRad x
  refine ⟨σ, x₀, rfl, T.ofRad_injective (F.powRadius σ) ?_⟩
  rw [← F.tildeFrob_ofRad, hx, T.ofRad_res]

theorem extNorm_pow_of_fixed {σ : Set.Ioo (0 : ℝ) 1} {x₀ : T.RobbaExt σ}
    (h : F.extFrob σ x₀ = T.res (F.powRadius_le_self σ) x₀) (r : Set.Ioc (0 : ℝ) σ) :
    T.extNorm σ ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _,
      (pow_le_of_le_one r.2.1.le (r.2.2.trans σ.2.2.le) F.q_pos.ne').trans r.2.2⟩ x₀ =
      T.extNorm σ r x₀ ^ p ^ F.a := by
  have h1 := F.extNorm_extFrob σ r x₀
  rw [h, extNorm_res] at h1
  exact h1

theorem tildeFrob_econToTilde (σ : Set.Ioo (0 : ℝ) 1) {b : T.B} (hb : b ∈ T.Econ σ) :
    F.tildeFrob (T.econToTilde σ ⟨b, hb⟩) =
      T.econToTilde (F.powRadius σ) ⟨F.toB b, F.toB_mem_Econ_iff.2 hb⟩ := by
  show F.tildeFrob (T.ofRad σ ((⟨b, hb⟩ : T.Econ σ) : T.RobbaExt σ)) =
    T.ofRad (F.powRadius σ) ((⟨F.toB b, F.toB_mem_Econ_iff.2 hb⟩ : T.Econ (F.powRadius σ)) :
      T.RobbaExt (F.powRadius σ))
  rw [F.tildeFrob_ofRad, F.extFrob_coe]
  rfl

theorem exists_eq_zpow_mul_of_fixed [CompleteSpace L] (ha : 0 < F.a) {z : Γ} (hz : z ∈ T.int)
    (hz1 : ‖T.red z‖ = 1) (hzφ : F.φ (T.π * z) = T.π * z) {x : T.RobbaTilde} (hx0 : x ≠ 0)
    (hx : F.tildeFrob x = x) :
    ∃ (c : ℤ) (u : Γ), u ∈ T.int ∧ ‖T.red u‖ = 1 ∧ F.φ u = u ∧
      ∃ h : T.ConvAll ((T.πB * algebraMap Γ T.B z) ^ c * algebraMap Γ T.B u),
        x = T.tildeOf _ h := by
  obtain ⟨σ, x₀, hxσ, hfix⟩ := F.exists_ofRad_of_fixed hx
  have hσ0 : (0 : ℝ) < σ := σ.2.1
  have hσ1 : (σ : ℝ) < 1 := σ.2.2
  have hx₀ : x₀ ≠ 0 := fun h => hx0 (by rw [← hxσ, h, map_zero])
  set Q : ℕ := p ^ F.a with hQ
  have hQ2 : 2 ≤ Q := by
    have := hp.out.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ F.a := Nat.pow_le_pow_right hp.out.pos ha

  let f : ℝ → ℝ := fun s => if h : 0 < s ∧ s ≤ σ then T.extNorm σ ⟨s, h.1, h.2⟩ x₀ else 0
  have hf : ∀ (s : ℝ) (h0 : 0 < s) (h1 : s ≤ σ), f s = T.extNorm σ ⟨s, h0, h1⟩ x₀ := by
    intro s h0 h1; simp only [f, dif_pos (And.intro h0 h1)]
  obtain ⟨c, hc⟩ := eq_rpow_of_logConvex hσ0 hσ1 hQ2 f
    (fun s h0 h1 => by rw [hf s h0 h1]; exact T.extNorm_pos hx₀ _)
    (fun s h0 h1 => by
      have hs1 : s ^ Q ≤ σ :=
        (pow_le_of_le_one h0.le (h1.trans hσ1.le) (by omega)).trans h1
      rw [hf _ (pow_pos h0 Q) hs1, hf s h0 h1]
      exact F.extNorm_pow_of_fixed hfix ⟨s, h0, h1⟩)
    (fun a r b t ha0 har hrb hbσ ht0 ht1 hr => by
      rw [hf a ha0 (har.trans (hrb.trans hbσ)), hf r (ha0.trans_le har) (hrb.trans hbσ),
        hf b (ha0.trans_le (har.trans hrb)) hbσ]
      exact T.extNorm_interp_le _ _ _ ht0 ht1 hr x₀)
  have hN : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s x₀ = (s : ℝ) ^ c := by
    intro s
    have := hc s s.2.1 s.2.2
    rwa [hf s s.2.1 s.2.2] at this

  set Pu : T.B := T.πB * algebraMap Γ T.B z with hPudef
  have hPu : T.IsUnitTerm Pu 1 := ⟨z, hz, hz1, by rw [zpow_one]⟩
  have hPuφ : F.toB Pu = Pu := by
    rw [hPudef, πB, ← map_mul, F.toB_algebraMap, hzφ]
  set m : ℤ := ⌊c⌋ with hm
  have hP := hPu.zpow (-m)
  have hPc : T.ConvAll (Pu ^ (-m)) := hP.convAll
  have hPnorm : ∀ s : ℝ, 0 < s → s < 1 → gaussNorm (T.coeffB (Pu ^ (-m))) s = s ^ (-m : ℝ) := by
    intro s h0 h1
    have := hP.gaussNorm_mul_teich 1 h0 h1
    rw [T.teich_one, map_one, mul_one, norm_one, mul_one, mul_one] at this
    rw [this, ← Real.rpow_intCast]
    push_cast
    ring_nf
  set d : ℝ := c - m with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith [Int.floor_le c]
  have hd1 : d < 1 := by rw [hd]; linarith [Int.lt_floor_add_one c]
  set y := T.ofAll _ hPc σ * x₀ with hy
  have hyN : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s y = (s : ℝ) ^ d := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2.1
    rw [hy, extNorm_mul, extNorm_ofAll, hPnorm s hs0 (s.2.2.trans_lt hσ1), hN s,
      ← Real.rpow_add hs0, hd]
    ring_nf
  obtain ⟨w, hwE, hw⟩ := exists_gamma_of_extNorm_le y (C := 1) (β := 0) 0 (by norm_num)
    (fun s => by
      rw [hyN s, neg_zero, Real.rpow_zero, one_mul]
      exact Real.rpow_le_one s.2.1.le (s.2.2.trans hσ1.le) hd0)
  rw [← πExt_pow_eq_ofAll, _root_.pow_zero, one_mul] at hw
  set bw : T.B := algebraMap Γ T.B w with hbw
  have hwc : ConvergesAt (T.zcoeff w) σ := by
    have := (T.mem_Econ).1 hwE
    rwa [coeffB_algebraMap] at this
  have hwN : ∀ s : Set.Ioc (0 : ℝ) σ, gaussNorm (T.zcoeff w) s = (s : ℝ) ^ d := by
    intro s
    rw [← hyN s, hw, extNorm_coe, coeffB_algebraMap]

  have hd_eq : d = 0 := by
    by_contra hdne
    have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdne)
    have hw0 : T.coeff w 0 = 0 := by
      by_contra h0
      have hpos : 0 < ‖T.coeff w 0‖ := norm_pos_iff.2 h0
      obtain ⟨t, ht0, htσ, htC⟩ := exists_rpow_small hσ0 hdpos zero_le_one (half_pos hpos)
      have h1 := T.weight_natCast_le (convergesAt_of_le (T.zcoeff_neg_exists w) hwc ht0 htσ) 0
      rw [hwN ⟨t, ht0, htσ⟩] at h1
      simp only [Nat.cast_zero, zpow_zero, mul_one] at h1
      linarith
    have hs2 : (0 : ℝ) < σ / 2 := by positivity
    have hs2σ : (σ : ℝ) / 2 ≤ σ := by linarith
    have hbound : gaussNorm (T.zcoeff w) (σ / 2) ≤ (1 / 2) * gaussNorm (T.zcoeff w) σ := by
      refine gaussNorm_le fun n => ?_
      have hG : 0 ≤ gaussNorm (T.zcoeff w) σ := gaussNorm_nonneg hσ0
      rcases lt_or_ge n 1 with hn | hn
      · rcases lt_or_ge n 0 with hn0 | hn0
        · rw [T.zcoeff_of_neg _ hn0, norm_zero, zero_mul]; positivity
        · have : n = ((0 : ℕ) : ℤ) := by omega
          rw [this, T.zcoeff_natCast, hw0, norm_zero, zero_mul]; positivity
      · have h1 := hwc.le_gaussNorm n
        have h2 : ((σ : ℝ) / 2) ^ n ≤ (1 / 2) * (σ : ℝ) ^ n := by
          rw [div_eq_mul_one_div, mul_zpow, mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (zpow_pos hσ0 n).le
          calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (1 : ℤ) :=
                zpow_le_zpow_right_of_le_one₀ (by norm_num) (by norm_num) hn
            _ = 1 / 2 := zpow_one _
        calc ‖T.zcoeff w n‖ * ((σ : ℝ) / 2) ^ n ≤ ‖T.zcoeff w n‖ * ((1 / 2) * (σ : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = (1 / 2) * (‖T.zcoeff w n‖ * (σ : ℝ) ^ n) := by ring
          _ ≤ (1 / 2) * gaussNorm (T.zcoeff w) σ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hσN : gaussNorm (T.zcoeff w) σ = (σ : ℝ) ^ d := hwN (topRad σ)
    have h2N : gaussNorm (T.zcoeff w) ((σ : ℝ) / 2) = ((σ : ℝ) / 2) ^ d :=
      hwN ⟨σ / 2, Set.mem_Ioc.2 ⟨hs2, hs2σ⟩⟩
    rw [h2N, hσN] at hbound
    rw [Real.div_rpow hσ0.le (by norm_num)] at hbound
    have h2d : (2 : ℝ) ^ d < 2 := by
      calc (2 : ℝ) ^ d < 2 ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hd1
        _ = 2 := Real.rpow_one 2
    have hσd : 0 < (σ : ℝ) ^ d := Real.rpow_pos_of_pos hσ0 d
    have h2pos : 0 < (2 : ℝ) ^ d := Real.rpow_pos_of_pos (by norm_num) d
    rw [div_le_iff₀ h2pos] at hbound
    nlinarith
  have hcm : c = m := by linarith
  have hwN1 : ∀ s : Set.Ioc (0 : ℝ) σ, gaussNorm (T.zcoeff w) s = 1 := fun s => by
    rw [hwN s, hd_eq, Real.rpow_zero]

  have hxR : T.tildeOf _ hPc * x = T.econToTilde σ ⟨bw, hwE⟩ := by
    rw [T.tildeOf_eq _ hPc σ, ← hxσ, ← map_mul, ← hy, hw]
    rfl
  have hwφ : F.φ w = w := by
    have h1 : F.tildeFrob (T.tildeOf _ hPc * x) = T.tildeOf _ hPc * x := by
      rw [map_mul, hx, F.tildeFrob_tildeOf]
      congr 1
      exact T.tildeOf_congr _ _ (by rw [map_zpow₀, hPuφ])
    rw [hxR, F.tildeFrob_econToTilde,
      T.econToTilde_eq _ (T.Econ_anti (F.powRadius_le_self σ) hwE)] at h1
    have h2 := congrArg Subtype.val (T.econToTilde_injective _ h1)
    simp only [hbw, F.toB_algebraMap] at h2
    exact T.algebraMap_injective h2
  have htoB : F.toB bw = bw := by rw [hbw, F.toB_algebraMap, hwφ]

  have hall : ∀ k : ℕ, ∀ ρ : Set.Ioo (0 : ℝ) 1, (ρ : ℝ) ^ Q ^ k ≤ σ →
      bw ∈ T.Econ ρ ∧ gaussNorm (T.coeffB bw) ρ = 1 := by
    intro k
    induction k with
    | zero =>
      intro ρ hρ
      rw [_root_.pow_zero, pow_one] at hρ
      refine ⟨T.Econ_anti hρ hwE, ?_⟩
      rw [hbw, coeffB_algebraMap]; exact hwN1 ⟨ρ, ρ.2.1, hρ⟩
    | succ k ih =>
      intro ρ hρ
      have h1 : ((F.powRadius ρ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ Q ^ k ≤ σ := by
        show ((ρ : ℝ) ^ p ^ F.a) ^ Q ^ k ≤ σ
        rw [← pow_mul, ← _root_.pow_succ']; exact hρ
      obtain ⟨hE, hn⟩ := ih _ h1
      refine ⟨F.toB_mem_Econ_iff.1 (by rw [htoB]; exact hE), ?_⟩
      have h2 := F.gaussNorm_toB_pow ρ.2.1 ρ.2.2 (F.toB_mem_Econ_iff.1 (by rw [htoB]; exact hE))
      rw [htoB] at h2
      change gaussNorm (T.coeffB bw) ((ρ : ℝ) ^ p ^ F.a) = _ at hn
      rw [hn] at h2
      exact ((pow_eq_one_iff_of_nonneg (gaussNorm_nonneg ρ.2.1) (by positivity)).1 h2.symm)
  have hall' : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.zcoeff w) ρ ∧ gaussNorm (T.zcoeff w) ρ = 1 := by
    intro ρ h0 h1
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hσ0 h1
    have hk' : ρ ^ Q ^ k ≤ σ :=
      (pow_le_pow_of_le_one h0.le h1.le (Nat.lt_pow_self (by omega)).le).trans hk.le
    obtain ⟨hE, hn⟩ := hall k ⟨ρ, h0, h1⟩ hk'
    rw [hbw, coeffB_algebraMap] at hn
    refine ⟨?_, hn⟩
    have := (T.mem_Econ).1 hE
    rwa [hbw, coeffB_algebraMap] at this

  have hwint : w ∈ T.int := by
    refine T.mem_int_iff.2 fun n => norm_le_one_of_forall_weight_le (n := n) fun ρ h0 h1 => ?_
    have h := T.weight_natCast_le (hall' ρ h0 h1).1 n
    rwa [(hall' ρ h0 h1).2, zpow_natCast] at h
  have hwred : ‖T.red w‖ = 1 := by
    refine le_antisymm (T.norm_red_le_one w hwint) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hG : gaussNorm (T.zcoeff w) (1 / 2) ≤ max ‖T.red w‖ (1 / 2) := by
      refine gaussNorm_le fun n => ?_
      rcases lt_or_ge n 0 with hn0 | hn0
      · rw [T.zcoeff_of_neg _ hn0, norm_zero, zero_mul]; positivity
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
        rw [T.zcoeff_natCast, zpow_natCast]
        rcases k with _ | k
        · rw [_root_.pow_zero, mul_one, T.coeff_zero]; exact le_max_left _ _
        · refine le_max_of_le_right ?_
          calc ‖T.coeff w (k + 1)‖ * (1 / 2 : ℝ) ^ (k + 1) ≤ 1 * (1 / 2 : ℝ) ^ (k + 1) :=
                mul_le_mul_of_nonneg_right (T.mem_int_iff.1 hwint _) (by positivity)
            _ ≤ 1 / 2 := by
                rw [one_mul]
                exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega) |>.trans
                  (by norm_num)
    rw [(hall' (1 / 2) (by norm_num) (by norm_num)).2] at hG
    have : max ‖T.red w‖ (1 / 2) < 1 := max_lt hlt (by norm_num)
    linarith

  have hbwc : T.ConvAll bw := fun ρ h0 h1 => by
    rw [hbw, coeffB_algebraMap]; exact (hall' ρ h0 h1).1
  refine ⟨m, w, hwint, hwred, hwφ, ((hPu.zpow m).convAll).mul hbwc, ?_⟩
  have hbwT : T.econToTilde σ ⟨bw, hwE⟩ = T.tildeOf bw hbwc := by
    rw [T.tildeOf_eq _ hbwc σ]; rfl
  rw [hbwT] at hxR
  have hone : T.tildeOf (Pu ^ m) (hPu.zpow m).convAll * T.tildeOf _ hPc = 1 := by
    rw [← tildeOf_mul, ← tildeOf_one]
    exact T.tildeOf_congr _ _ (by rw [← zpow_add₀ hPu.ne_zero, add_neg_cancel, zpow_zero])
  rw [tildeOf_mul (hPu.zpow m).convAll hbwc, ← hxR, ← mul_assoc, hone, one_mul]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end
