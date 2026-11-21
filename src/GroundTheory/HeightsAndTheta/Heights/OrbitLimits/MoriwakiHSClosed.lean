import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpper
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem tendsto_div_of_bounds {h c : ℕ → ℝ} {T : ℝ} (hc : ∀ᶠ n in atTop, 0 < c n)
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (T - ε) * c n ≤ h n)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, h n ≤ (T + ε) * c n) :
    Tendsto (fun n => h n / c n) atTop (𝓝 T) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hc, hlo ((T - a) / 2) (by linarith)] with n hcn hn
    rw [lt_div_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show a < T - (T - a) / 2 by linarith) hcn
    linarith
  · filter_upwards [hc, hup ((a - T) / 2) (by linarith)] with n hcn hn
    rw [div_lt_iff₀ hcn]
    have := mul_lt_mul_of_pos_right (show T + (a - T) / 2 < a by linarith) hcn
    linarith

theorem eventually_pos_normaliser (D : ℕ) :
    ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem MoriwakiHS.of_found (hL : NefCountLower.Statement) (hU : NefCountUpper.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht
  exact tendsto_div_of_bounds (h := smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a))
    (c := fun n : ℕ => (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) (eventually_pos_normaliser D)
    (hL K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)
    (hU K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht)

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefSmallSectionEventually.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => A) →
    ∀ᶠ n : ℕ in atTop, ∃ t ∈ chartLat y A.a n, t ≠ 0 ∧ IsSmallH (mCoordIdeal y) y A n t

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem smallSectionCount_le_shift {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m d : ℕ} {t : Ω}
    (ht : t ∈ chartLat y A.a d) (ht0 : t ≠ 0) (hts : IsSmallH (mCoordIdeal y) y A d t)
    (hfin : {s : chartLat y A.a (m + d) | IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) m ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (m + d) := by
  unfold smallSectionCount
  have : Finite {s : chartLat y A.a (m + d) // IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)} :=
    hfin.to_subtype
  have hmap : ∀ s : {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)},
      (s.1 : Ω) * t ∈ chartLat y A.a (m + d) ∧ IsSmallH (mCoordIdeal y) y A (m + d) ((s.1 : Ω) * t) := by
    intro s
    refine ⟨chartLat_mul s.1.2 ht, fun dg dh g h z hg hh hdeg he hz => ?_⟩
    have := SectionBoundedMul.proof K ι Ω y A m d 1 1 _ t s.1.2 ht (isBoundedH_one_of_isSmallH s.2)
      (isBoundedH_one_of_isSmallH hts) dg dh g h z hg hh hdeg he hz
    simpa only [one_mul] using this
  have hcard : Nat.card {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (m + d) // IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * t, (hmap s).1⟩, (hmap s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ ht0 h))
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Shift

theorem eventually_mul_pow_le_shift (D L : ℕ) {b c : ℝ} (hc : 0 < c) (hbc : b < c) :
    ∀ᶠ n : ℕ in atTop, b * (n : ℝ) ^ (D + 1) ≤ c * ((n : ℝ) - L) ^ (D + 1) := by
  have h1 : Tendsto (fun n : ℕ => (1 - (L : ℝ) / n) ^ (D + 1)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (L : ℝ)).const_sub 1).pow (D + 1)
  filter_upwards [h1.eventually (lt_mem_nhds ((div_lt_one hc).2 hbc)), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : (n : ℝ) - L = n * (1 - L / n) := by field_simp
  have hp : 0 < (n : ℝ) ^ (D + 1) := by positivity
  rw [e, mul_pow]
  have := (div_lt_iff₀ hc).1 hn
  nlinarith

theorem NefCountLower.proof (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hPk : PackingStatement) : NefCountLower.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  by_cases hT : T - ε ≤ 0
  · exact Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)
  rw [not_le] at hT
  obtain ⟨a, ha, hak⟩ := hM K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht (ε / 2) (by linarith)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hak
  obtain ⟨n₀, hn₀⟩ :=
    eventually_atTop.1 (hS K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht (by linarith))
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hs.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  filter_upwards [eventually_mul_pow_le_shift D (n₀ + a) (b := T - ε) (c := T - ε / 2) (by linarith)
    (by linarith), eventually_ge_atTop (n₀ + a + a * k₀)] with n hn hge
  obtain ⟨k, r, hr, hnk⟩ : ∃ k r, r < a ∧ n = a * k + (n₀ + r) :=
    ⟨(n - n₀) / a, (n - n₀) % a, Nat.mod_lt _ ha, by have := Nat.div_add_mod (n - n₀) a; omega⟩
  have hkk : k₀ ≤ k := by
    by_contra hlt
    have : a * k + a ≤ a * k₀ := by nlinarith
    omega
  obtain ⟨t, ht, ht0, hts⟩ := hn₀ (n₀ + r) (by omega)
  have hL : (n : ℝ) - ((n₀ + a : ℕ) : ℝ) ≤ ((a * k : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ ((a * k : ℕ) : ℝ) + ((n₀ + a : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ a * k + (n₀ + a))
    linarith
  have hL0 : (0 : ℝ) ≤ (n : ℝ) - ((n₀ + a : ℕ) : ℝ) := by
    have : ((n₀ + a : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n₀ + a ≤ n)
    linarith
  have hpow := pow_le_pow_left₀ hL0 hL (D + 1)
  calc (T - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (n : ℝ) ^ (D + 1)) / ((D + 1).factorial : ℝ) := by ring
    _ ≤ ((T - ε / 2) * ((n : ℝ) - ((n₀ + a : ℕ) : ℝ)) ^ (D + 1)) / ((D + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right hn hfac.le
    _ ≤ ((T - ε / 2) * ((a * k : ℕ) : ℝ) ^ (D + 1)) / ((D + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith)) hfac.le
    _ = (T - ε / 2) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by ring
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := hk₀ k hkk
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k + (n₀ + r)) :=
        smallSectionCount_le_shift ht ht0 hts (hfin _)
    _ = smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n := by rw [← hnk]

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefSmallApprox.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    ∀ δ : ℝ, 0 < δ → ∃ (q : ℕ) (B : HermLine ι) (P1 : Ideal (MRing ι)), 1 ≤ q ∧
      IsSmallGeneratedDatum P1 y D B ∧ IsConjInvariantH B ∧
      II K ι (mCoordIdeal y) (D + 1) (fun _ => B) ≤
        (q : ℝ) ^ (D + 1) * (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + δ) ∧
      ∀ᶠ n : ℕ in atTop, ∃ t : Ω, t ≠ 0 ∧ ∀ s ∈ chartLat y A.a n, IsSmallH (mCoordIdeal y) y A n s →
        s * t ∈ chartLat y B.a (n / q + 1) ∧ IsSmallH (mCoordIdeal y) y B (n / q + 1) (s * t)

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefCountUpperCurve.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
        (II K ι (mCoordIdeal y) 1 (fun _ => A) + ε) * (n : ℝ)

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem NefCountUpper.proof (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement)
    (h7 : G7.Statement) (hPack : PackingStatement) : NefCountUpper.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · filter_upwards [hCurve K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε] with n hn
    simpa using hn
  have : CharZero Ω := UpperNormalisation.charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  set IA := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hIA
  obtain ⟨q, B, P1, hq, hsg, hBc, htop, hev⟩ :=
    hApx K ι Ω y D A P0 II hD hII har hb hP0 hs hc hnef hgen hht (ε / 4) (by linarith)
  set IB := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIB
  set T : ℝ := IA + ε / 2 with hT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
  have hBT : IB + ε / 4 ≤ (q : ℝ) ^ (D + 1) * T := by
    have : ε / 4 ≤ (q : ℝ) ^ (D + 1) * (ε / 4) := le_mul_of_one_le_left (by linarith) hq1
    rw [hT]; nlinarith
  obtain ⟨hfin, Cp, hCp⟩ := hPack K ι Ω y D B (chartLat y B.a) har hb hsg.semipos.1
    (fun τ => Mono.chartLat_le_nm y B.a τ)
  have hG7 := h7 K ι Ω y D B P1 II hD hII har hb hsg hBc

  set v : ℕ → ℝ := fun N => smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N /
    ((N : ℝ) ^ (D + 1) / F) with hv
  have hv_bdd : ∀ N, v N ≤ |Cp| * F * 2 ^ (D + 1) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [hv, Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, div_zero]
      positivity
    · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) / F := by positivity
      simp only [hv]
      rw [div_le_iff₀ hNpos]
      have h1 := (hCp N).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))
      have h2 : ((N : ℝ) + 1) ^ (D + 1) ≤ (2 * N) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ |Cp| * ((N : ℝ) + 1) ^ (D + 1) := h1
        _ ≤ |Cp| * (2 * N) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cp)
        _ = |Cp| * F * 2 ^ (D + 1) * ((N : ℝ) ^ (D + 1) / F) := by rw [mul_pow]; field_simp
  have hev1 : ∀ᶠ N in atTop, v N < IB + ε / 4 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hG7 (by linarith)) (isBoundedUnder_of ⟨_, hv_bdd⟩)
  have hNq : Tendsto (fun n : ℕ => n / q + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ _) (Nat.tendsto_div_const_atTop (Nat.one_le_iff_ne_zero.mp hq))
  have hlim : Tendsto (fun n : ℕ => T * (1 + (q : ℝ) / n) ^ (D + 1)) atTop (𝓝 T) := by
    have h0 : Tendsto (fun n : ℕ => (q : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul T
  filter_upwards [hNq.eventually hev1, hlim.eventually (gt_mem_nhds (show T < IA + ε by linarith)), hev,
    eventually_ge_atTop 1] with n h2 h3 ⟨t, ht0, hts⟩ hn1
  set N := n / q + 1 with hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.succ_pos _
    positivity

  have hcmp : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N :=
    Mono.smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B (m / q + 1))
      (La' := fun m => chartLat y B.a (m / q + 1)) (fun s => s * t)
      (fun s _ u _ hsu => mul_right_cancel₀ ht0 hsu) (fun s hs hsm => hts s hs hsm) (hfin N)
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N ≤
      (IB + ε / 4) * ((N : ℝ) ^ (D + 1) / F) := by
    have := h2
    simp only [hv] at this
    rw [div_lt_iff₀ hNpos] at this
    exact this.le

  have hlo : (n : ℝ) ≤ q * N := by
    have := Nat.lt_mul_div_succ n (show 0 < q by omega)
    exact_mod_cast this.le
  have hhi : (q : ℝ) * N ≤ n + q := by
    have : q * (n / q) ≤ n := Nat.mul_div_le n q
    have : q * N ≤ n + q := by rw [hN, mul_add, mul_one]; omega
    exact_mod_cast this
  set X : ℝ := ((q : ℝ) * N) ^ (D + 1) with hX
  have hX1 : (n : ℝ) ^ (D + 1) ≤ X := pow_le_pow_left₀ hnpos.le hlo _
  have hX2 : X ≤ ((n : ℝ) + q) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hhi _
  have hratio : ((n : ℝ) + q) ^ (D + 1) = (1 + (q : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have hTX : T * X ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := by
    rcases le_or_gt 0 T with hT0 | hT0
    · calc T * X ≤ T * ((n : ℝ) + q) ^ (D + 1) := mul_le_mul_of_nonneg_left hX2 hT0
        _ = (T * (1 + (q : ℝ) / n) ^ (D + 1)) * (n : ℝ) ^ (D + 1) := by rw [hratio]; ring
        _ ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonneg_right h3.le (by positivity)
    · calc T * X ≤ T * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonpos_left hX1 hT0.le
        _ ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n
      ≤ (IB + ε / 4) * ((N : ℝ) ^ (D + 1) / F) := hcmp.trans hcount
    _ ≤ ((q : ℝ) ^ (D + 1) * T) * ((N : ℝ) ^ (D + 1) / F) := mul_le_mul_of_nonneg_right hBT hNpos.le
    _ = (T * X) / F := by rw [hX, mul_pow]; ring
    _ ≤ ((IA + ε) * (n : ℝ) ^ (D + 1)) / F := div_le_div_of_nonneg_right hTX hFpos.le
    _ = (IA + ε) * ((n : ℝ) ^ (D + 1) / F) := by ring

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SecMRankBound.full : SecMRankBound.Statement :=
  SecMRankBound.proof GenericFibreVar.proof

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem PackingStatement.of_leaves (hC : KH.CondStatement) (hG : GridSeparation.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.PackingStatement :=
  SmallPacking.proof (NmSectionsRankBound.proof (NmSectionsFinite.proof hC) SecMRankBound.full)
    (SmallSectionsSeparated.proof hG)

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

theorem G7.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) : G7.Statement :=
  G7.proof (SuccessiveMinimaSpan.of_leaves hC hR)
    (EuclideanSections.proof (EuclideanSectionsPower.proof hL2 hP) SmallSectionsNonzero.proof
      SublatticeDegree.full (SuccessiveMinimaSpan.of_leaves hC hR))

theorem NefCountLower.of_leaves (hM : NefCountAlongMultiples.Statement)
    (hS : NefSmallSectionEventually.Statement) (hC : KH.CondStatement) (hG : GridSeparation.Statement) :
    NefCountLower.Statement :=
  NefCountLower.proof hM hS (PackingStatement.of_leaves hC hG)

theorem NefCountUpper.of_leaves (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement)
    (hC : KH.CondStatement) (hG : GridSeparation.Statement) (hR : RelSectionsLarge.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) : NefCountUpper.Statement :=
  NefCountUpper.proof hApx hCurve (G7.of_leaves hC hR hL2 hP) (PackingStatement.of_leaves hC hG)

theorem MoriwakiHS.of_leaves (hC : KH.CondStatement) (hG : GridSeparation.Statement)
    (hR : RelSectionsLarge.Statement) (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement)
    (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement :=
  MoriwakiHS.of_found (NefCountLower.of_leaves hM hS hC hG)
    (NefCountUpper.of_leaves hApx hCurve hC hG hR hL2 hP)

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

theorem MoriwakiHS.of_open (hC : KH.CondStatement) (hG : GridSeparation.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement)
    (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement :=
  MoriwakiHS.of_leaves hC hG RelSectionsLarge.full hL2 hP hM hS hApx hCurve

end GroundTheory.Heights₂.Heights.Targets
end
