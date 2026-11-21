import Formalism.LocalToGlobal.ExponentGrids.ExplicitSizeInequalityIndexed
import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
import Formalism.PairingDivisors.PairingDivisorProofs.Height
import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
import Lemmata.PlaneOverMembership.PlOverOfMem
import Formalism.TowerValuationBounds.TowerValuationProofs.ValuationRatioIndex

section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)

noncomputable section

namespace Formalism.AtG

theorem grid_ell_bound : FinitePlaceLiesOverPrime := by
  first | exact Bl.PlaneOverMembership.goal1 .. | (apply Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> first | assumption | infer_instance)

theorem sum_le_finsum' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hs : (Function.support f).Finite)
    (F : Finset α) : ∑ a ∈ F, f a ≤ ∑ᶠ a, f a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := hs.toFinset ∪ F) (by
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Or.inl hx)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun a _ _ => hf a)

theorem partial_nat (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ)
    (F : Finset (Pl K)) : ∑ w ∈ F, lw w * (vw w (n : K) : ℝ) ≤ Real.log n := by
  obtain ⟨h1, h2⟩ := Formalism.PairingDivisionLocalBalance.sum_valuation_nat K n
  rw [← h2]
  exact sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w)
    (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w n)) h1 F

theorem partial_ht {K : Type} [Field K] [NumberField K] [StarRing K] {g : Pl K → ℤ} {z : K} {B : ℝ}
    (h : HtLe g z B) (F : Finset (Pl K)) :
    ∑ w ∈ F, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B :=
  (sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (abs_nonneg _)) h.1 F).trans h.2

theorem j3Wt : NormalisedPrimeUnitWeight := by
  intro K _ _ _ ell hell S c hS w
  classical
  have hz : ∀ l ∈ S, l ≠ ell w → (vw w (l : K) : ℝ) = 0 := by
    intro l hl hne
    have hco : Nat.Coprime l (ell w) := (Nat.coprime_primes (hS l hl) (hell w).1).2 hne
    have h1 := Formalism.DivisionValues.places_over_coprime K l (ell w) hco w
    have h2 : ¬ PlOver l w := fun h => h1 ⟨h, (hell w).2⟩
    have h3 := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
    unfold Formalism.DivisionValues.PlOver at h2
    have : vw w (l : K) = 0 := by omega
    exact_mod_cast this
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : ell w ∈ S
  · rw [if_pos h, Finset.sum_eq_single_of_mem (ell w) h]
    intro l hl hne
    rw [hz l hl hne, mul_zero]
  · rw [if_neg h, zero_mul]
    apply Finset.sum_eq_zero
    intro l hl
    rw [hz l hl (fun e => h (e ▸ hl)), mul_zero]

theorem norm_height_bound : DisjointUnionFactorProduct := by
  intro K _ _ _ _ x dl Bδ hx hdl hden hB
  classical
  obtain ⟨hfin, hpf⟩ := Formalism.DivisionValues.prod_formula' K x hx
  have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
    have h3 := IsTotallyComplex.finrank K
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
    rw [h3, h4, h5]; push_cast; ring
  have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc; linarith
  have hmean : ∀ φ : InfinitePlace K → ℝ,
      (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v = (∑ v, φ v) / Fintype.card (InfinitePlace K) := by
    intro φ
    rw [← hc]
    field_simp
  have hsupp : ∀ w, w ∉ hfin.toFinset → ((vw w x : ℤ) : ℝ) = 0 := by
    intro w hw
    have h0 : lw w * (vw w x : ℝ) = 0 := by
      by_contra hne
      exact hw (hfin.mem_toFinset.2 hne)
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (Formalism.DivisionValues.PlaceSumConjugation.lw_pos w).ne'
    · exact h
  have hsum : ∑ w ∈ hfin.toFinset, lw w * (vw w x : ℝ) =
      (∑ v : InfinitePlace K, Real.log ‖v.embedding x‖) / Fintype.card (InfinitePlace K) := by
    rw [← hmean, hpf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  obtain ⟨_, _, h3⟩ := Formalism.ValuationGridEstimates.height_bound_alt (Pl K) (InfinitePlace K) (fun w => lw w)
    (fun w => (vw w x : ℝ)) dl (fun v => ‖v.embedding x‖) hfin.toFinset Bδ
    (fun w => Formalism.PairingDivisionLocalBalance.lw_nonneg w) hsupp hsum
  have h4 := h3 hdl hden hB hfin.toFinset
  have hsub : (Function.support fun w : Pl K => lw w * |((vw w x + 0 : ℤ) : ℝ)|) ⊆
      (hfin.toFinset : Set (Pl K)) := by
    intro w hw
    by_contra hne
    apply hw
    have := hsupp w hne
    simp only [add_zero]
    rw [this, abs_zero, mul_zero]
  refine ⟨(hfin.toFinset.finite_toSet).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [hmean]
  simpa only [add_zero] using h4


theorem wt_nonneg' {K : Type} [Field K] [NumberField K] [StarRing K] (S : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ l ∈ S, 0 ≤ c l) (w : Pl K) : 0 ≤ wt S c w := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  refine Finset.sum_nonneg fun l hl => mul_nonneg (hc l hl) ?_
  have := (Formalism.DivisionValues.valuation_basic_properties K w).2.2.2.2.2.2 (l : 𝓞 K)
  have h2 : (((l : 𝓞 K)) : K) = (l : K) := by simp
  rw [h2] at this
  exact_mod_cast this


theorem denIdeal_ne_zero {K : Type} [Field K] [NumberField K] (T : Finset (Pl K)) (a : Pl K → ℤ) :
    denIdeal T a ≠ 0 := by
  unfold denIdeal
  rw [Finset.prod_ne_zero_iff]
  intro w _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

theorem absNorm_pl_ne_zero {K : Type} [Field K] [NumberField K] (w : Pl K) :
    (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
  have h : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  exact_mod_cast h

theorem log_absNorm_denIdeal {K : Type} [Field K] [NumberField K] (T : Finset (Pl K))
    (a : Pl K → ℤ) :
    Real.log ((FractionalIdeal.absNorm (denIdeal T a) : ℚ) : ℝ) =
      -∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ) := by
  unfold denIdeal
  rw [map_prod, Rat.cast_prod, Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Real.log_zpow]
    push_cast
    ring
  · intro w _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow]
    apply zpow_ne_zero
    have := absNorm_pl_ne_zero w
    exact_mod_cast this

theorem lw_nonneg' {K : Type} [Field K] [NumberField K] (w : Pl K) : 0 ≤ lw w := by
  unfold Formalism.DivisionValues.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem grid_lemma_A : SlopeInequalityDenominators := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B T a hA hA0 hB hB0 hφ hincl
  have hI : denIdeal T a ≠ 0 := denIdeal_ne_zero T a
  obtain ⟨hfg, -, hmax, -⟩ :=
    Formalism.LFunctionChainParameters.LLcv.ideal_scaling_holds K W κ b' X' hX' (denIdeal T a) hI B hB hB0
  have hmap : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h
    apply hA0
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : (φ.restrictScalars (𝓞 K)) x ∈ A.map (φ.restrictScalars (𝓞 K)) :=
      Submodule.mem_map_of_mem hx
    rw [h, Submodule.mem_bot] at h1
    apply hφ
    rw [map_zero]
    exact h1
  obtain ⟨-, h2⟩ := Formalism.HN.slope_inequality_mean K V ι W κ b X b' X' hX hX' φ A hA hmap
  have h3 := (h2 _ hfg hincl).2 hφ.injOn
  rw [hmax, log_absNorm_denIdeal] at h3
  have e : ∑ w ∈ T, lw w * (a w : ℝ) =
      (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold Formalism.DivisionValues.lw
    ring
  rw [e]
  generalize (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) = sm at h3 ⊢
  have e2 : (2 * -sm) / (finrank ℚ K : ℝ) = -(2 * (sm / (finrank ℚ K : ℝ))) := by ring
  rw [e2] at h3
  linarith


theorem grid_function_of_lemma_A (hA : SlopeInequalityDenominators) : LargestSlopeLatticeFrames := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a r dF EM hInf Gr BF
    hR hM hM0 hΨ hincl ha hEM hh hGr hBF
  obtain ⟨hfg, hne⟩ := Formalism.DivisionValues.lattice_fg_ne_bot hD R hR
  obtain ⟨hu, -, -, -, h5⟩ := Formalism.DivisionValues.kappa_normalise K D hD XE hXE kap hkap
  obtain ⟨-, e2, -⟩ := h5 R hR
  have h := hA K (Fin D → K) (Fin D) W κ (Pi.basisFun K (Fin D))
    (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' hu hX' Ψ R M T a hfg hne hM hM0 hΨ hincl
  have hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF := by
    calc ∑ w ∈ T, lw w * (a w : ℝ)
        ≤ ∑ w ∈ T, (lw w * (vw w (r w) : ℝ) + lw w * dF w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have h1 := ha w hw
          have hl : 0 ≤ lw w := lw_nonneg' w
          nlinarith
      _ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib
      _ ≤ Gr + BF := add_le_add hGr hBF
  rw [e2]
  linarith

theorem grid_function_bound : LargestSlopeLatticeFrames := grid_function_of_lemma_A grid_lemma_A


















open Classical in

def fR {K : Type} [Field K] [NumberField K] (w : Pl K) (a : K) : WithTop ℝ :=
  if a = 0 then ⊤ else (((vw w a : ℤ) : ℝ) : WithTop ℝ)

theorem fR_ne {K : Type} [Field K] [NumberField K] (w : Pl K) (a : K) (ha : a ≠ 0) :
    fR w a = (((vw w a : ℤ) : ℝ) : WithTop ℝ) := by
  unfold fR
  exact if_neg ha

theorem fR_zero {K : Type} [Field K] [NumberField K] (w : Pl K) : fR w (0 : K) = ⊤ := by
  unfold fR
  exact if_pos rfl

def valR {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) : AddValuation K (WithTop ℝ) :=
  AddValuation.of (fR w) (fR_zero w)
    (by rw [fR_ne w 1 one_ne_zero, Formalism.DivisionValues.ValuationRepresentative.vw_one]; simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · rw [hxy]; simp [fR]
      rw [fR_ne w x hx, fR_ne w y hy, fR_ne w _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
      have h := Formalism.PairingDivisionLocalBalance.valuation_add K w x y hx hy hxy
      rcases min_le_iff.mp h with h | h
      · exact le_trans (min_le_left _ _) (by exact_mod_cast h)
      · exact le_trans (min_le_right _ _) (by exact_mod_cast h))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp [fR]
      by_cases hy : y = 0
      · subst hy; simp [fR]
      rw [fR_ne w x hx, fR_ne w y hy, fR_ne w _ (mul_ne_zero hx hy), Formalism.DivisionValues.ValuationRepresentative.vw_mul w x y hx hy,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring)




end Formalism.AtG
end
end

section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)

noncomputable section

namespace Formalism.AtG

theorem grid_squares_index_estimate (W S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (vr vA vA' : W → Fin m × Fin m → ℝ) (vT : W → Fin m × Fin m → ℤ → ℝ)
    (vTd : W → Fin m × Fin m → Bool → ℤ → ℝ)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (B BN Bδ : ℝ) (W0 : Finset W)
    (hlam : ∀ w, 0 ≤ lam w) (hδ : ∀ w, 0 ≤ δ w) (hN0 : ∀ ij s l, 0 ≤ N0 ij s l)
    (hvq : ∀ w s, 0 ≤ vq w s) (hprime : ∀ w, (ell w).Prime)
    (hfib : ∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l)
    (hdh : ∀ ij, dd ij = 2 * hh ij) (hdd : ∀ ij, dd ij ≤ 2 * N) (hyy : ∀ ij, yy ij ≤ m)
    (hcc : ∀ s ∈ S0, cc s ≤ ee s)
    (hsq : ∀ w ∈ W0, ∀ ij, vr w ij ≤ |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij (ch w) s|)) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ + 6 * δ w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * vq w s))
    (hA : ∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA w ij| ≤ B)
    (hA' : ∀ ij (F : Finset W), ∑ w ∈ F, lam w * |vA' w ij| ≤ B)
    (hT : ∀ ij s (F : Finset W), ∑ w ∈ F, lam w * |vT w ij s| ≤ B)
    (hTd : ∀ ij b s (F : Finset W), ∑ w ∈ F, lam w * |vTd w ij b s| ≤ B)
    (hBN : ∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 ij s l * Real.log l ≤ BN)
    (hBδ : ∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ)
    (hq : ∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) :
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 10 * N * BN + 2 * N + 6 * Bδ +
        4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) := by
  classical
  by_cases hm : m = 0
  · subst hm
    simp
  let vx : W → ((Fin m × Fin m) × Bool) × (Bool ⊕ (Fin 4 × ℤ × Bool)) → ℝ := fun w x =>
    match x.2 with
    | Sum.inl false => vA w x.1.1
    | Sum.inl true => vA' w x.1.1
    | Sum.inr (_, s, false) => vT w x.1.1 s
    | Sum.inr (_, s, true) => vTd w x.1.1 x.1.2 s
  let XX : Fin m × Fin m → Bool → Finset (((Fin m × Fin m) × Bool) × (Bool ⊕ (Fin 4 × ℤ × Bool))) := fun ij b =>
    ({(ij, b)} : Finset ((Fin m × Fin m) × Bool)) ×ˢ
      ((Finset.univ : Finset Bool).disjSum
        ((Finset.univ : Finset (Fin 4)) ×ˢ (Icc (1 : ℤ) (hh ij) ×ˢ (Finset.univ : Finset Bool))))
  have hB0 : 0 ≤ B := by
    have ij : Fin m × Fin m := (⟨0, by omega⟩, ⟨0, by omega⟩)
    simpa using hA ij ∅
  have hsumXX : ∀ w ij b, ∑ x ∈ XX ij b, |vx w x| = |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij b s|)) := by
    intro w ij b
    simp only [XX, sum_product, sum_singleton, sum_disjSum, Fintype.sum_bool, vx, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have : ∑ s ∈ Icc (1 : ℤ) (hh ij), (|vTd w ij b s| + |vT w ij s|) =
        ∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij b s|) :=
      sum_congr rfl (fun s _ => add_comm _ _)
    rw [this]; ring
  have hcardXX : ∀ ij b, (XX ij b).card ≤ 2 + 8 * N := by
    intro ij b
    simp only [XX, card_product, card_singleton, card_disjSum, card_univ, Fintype.card_bool,
      Fintype.card_fin, Int.card_Icc]
    have h1 := hdh ij
    have h2 := hdd ij
    have : ((hh ij : ℤ) + 1 - 1).toNat = hh ij := by omega
    rw [this]; omega
  have key := Formalism.ValuationGridEstimates.grid_index_bound W _ S m N lam δ ell N0 vr vx XX ch dd hh yy S0 cc ee qq vq
    (fun _ => B) BN Bδ W0 hlam hδ hN0 hvq hprime hfib hdh hdd hyy hcc
    (by
      intro w hw ij
      rw [hsumXX]
      have := hsq w hw ij
      linarith)
    (by
      rintro ⟨⟨ij, b⟩, (t | ⟨k, s, t⟩)⟩ F
      · cases t
        · exact hA ij F
        · exact hA' ij F
      · cases t
        · exact hT ij s F
        · exact hTd ij b s F)
    hBN hBδ hq
  have hX : ∑ ij : Fin m × Fin m, ∑ b : Bool, ∑ _x ∈ XX ij b, B ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B) := by
    calc ∑ ij : Fin m × Fin m, ∑ b : Bool, ∑ _x ∈ XX ij b, B
        ≤ ∑ _ij : Fin m × Fin m, ∑ _b : Bool, (2 + 8 * (N : ℝ)) * B := by
          apply sum_le_sum; intro ij _
          apply sum_le_sum; intro b _
          rw [sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hB0
          exact_mod_cast hcardXX ij b
      _ = _ := by
          simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
            nsmul_eq_mul]
          push_cast; ring
  linarith

theorem gridHeightBoundIndexed : GridHeightBoundIndexed := by
  intro K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh yy S0 cc ee qq B BN0 Bδ W0
    hdl hS hN0 hSe hrr hdd hddN hyy hcc hsq hA hT hTd hBN00 hBN0 hBδ
  obtain ⟨ell, hell⟩ := grid_ell_bound K
  classical
  have he : ∀ w : Pl K, (0 : ℝ) < (vw w (ell w : K) : ℝ) := by
    intro w
    have := (hell w).2
    unfold Formalism.DivisionValues.PlOver at this
    exact_mod_cast this
  have hlam : ∀ (w : Pl K) (t : ℝ),
      lw w * (vw w (ell w : K) : ℝ) * (t / (vw w (ell w : K) : ℝ)) = lw w * t := by
    intro w t
    have := (he w).ne'
    field_simp
  have habs : ∀ (w : Pl K) (t : ℝ),
      |t / (vw w (ell w : K) : ℝ)| = |t| / (vw w (ell w : K) : ℝ) := by
    intro w t
    rw [abs_div, abs_of_pos (he w)]
  obtain ⟨N1, hN1⟩ : ∃ f : Fin m × Fin m → ℤ → ℕ → ℝ, ∀ ij s l,
      f ij s l = if 1 ≤ s ∧ s ≤ (hh ij : ℤ) ∧ l ∈ S then N0 ij s l else 0 :=
    ⟨_, fun _ _ _ => rfl⟩
  have hN1in : ∀ ij (s : ℤ) l, 1 ≤ s → s ≤ (hh ij : ℤ) → l ∈ S → N1 ij s l = N0 ij s l := by
    intro ij s l a1 a2 a3
    rw [hN1, if_pos ⟨a1, a2, a3⟩]
  have hN1S : ∀ ij (s : ℤ) l, l ∉ S → N1 ij s l = 0 := by
    intro ij s l a3
    rw [hN1, if_neg (fun h => a3 h.2.2)]
  have hN1s : ∀ ij (s : ℤ) l, ¬ (1 ≤ s ∧ s ≤ (hh ij : ℤ)) → N1 ij s l = 0 := by
    intro ij s l a3
    rw [hN1, if_neg (fun h => a3 ⟨h.1, h.2.1⟩)]
  have hN1nn : ∀ ij s l, 0 ≤ N1 ij s l := by
    intro ij s l
    rw [hN1]
    split_ifs with h
    · exact hN0 ij s h.1 h.2.1 l h.2.2
    · exact le_rfl
  have hbud : ∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, N1 ij s l * Real.log l ≤ BN0 := by
    intro ij s P _
    by_cases hs : 1 ≤ s ∧ s ≤ (hh ij : ℤ)
    · refine le_trans ?_ (hBN0 ij s hs.1 hs.2)
      have h1 : ∑ l ∈ P, N1 ij s l * Real.log l =
          ∑ l ∈ P.filter (· ∈ S), N0 ij s l * Real.log l := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : l ∈ S
        · rw [if_pos hl, hN1in ij s l hs.1 hs.2 hl]
        · rw [if_neg hl, hN1S ij s l hl, zero_mul]
      rw [h1]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        exact (Finset.mem_filter.1 hl).2
      · intro l hl _
        exact mul_nonneg (hN0 ij s hs.1 hs.2 l hl) (Real.log_natCast_nonneg l)
    · refine le_trans (le_of_eq ?_) hBN00
      apply Finset.sum_eq_zero
      intro l _
      rw [hN1s ij s l hs, zero_mul]
  have key := grid_squares_index_estimate (Pl K) Sq m N
    (fun w => lw w * (vw w (ell w : K) : ℝ)) (fun w => dl w / (vw w (ell w : K) : ℝ)) ell
    N1
    (fun w ij => (vw w (rr w ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA' ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij s => ((vw w (zT ij s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij b s => ((vw w (zTd ij b s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    ch dd hh yy S0 cc ee qq
    (fun w s => (vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) B BN0 Bδ W0
    (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (he w).le)
    (fun w => div_nonneg (hdl w) (he w).le)
    hN1nn
    (fun w s => div_nonneg (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w (qq s)) (he w).le)
    (fun w => (hell w).1)
    (fun l F hF => by
      refine le_trans (le_of_eq ?_) (partial_nat K l F)
      apply Finset.sum_congr rfl
      intro w hw
      rw [hF w hw])
    hdd hddN hyy hcc
    (fun w hw ij => by
      have hE := he w
      have h0 := hsq w hw ij
      have hs3 : ∑ s ∈ Icc (1 : ℤ) (hh ij), wt S (N0 ij s) w =
          (∑ s ∈ Icc (1 : ℤ) (hh ij), N1 ij s (ell w)) * (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_Icc] at hs
        rw [j3Wt K ell hell S (N0 ij s) hS w]
        by_cases hl : ell w ∈ S
        · rw [if_pos hl, hN1in ij s _ hs.1 hs.2 hl]
        · rw [if_neg hl, hN1S ij s _ hl]
      rw [hs3, j3Wt K ell hell Se (fun l => 1 / (l : ℝ) ^ 2) hSe w] at h0
      simp only [habs]
      have hs1 : ∑ s ∈ Icc (1 : ℤ) (hh ij),
          (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ) +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      have hs2 : ∑ s ∈ S0, (cc s : ℝ) * ((vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hs1, hs2, div_le_iff₀ hE]
      refine le_trans h0 ?_
      generalize (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) = T1
      generalize (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) = T2
      generalize (∑ s ∈ Icc (1 : ℤ) (hh ij), N1 ij s (ell w)) = T3
      generalize (vw w (ell w : K) : ℝ) = E at hE ⊢
      have hε : (if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) ≤ (((ell w : ℕ) : ℝ) ^ 2)⁻¹ := by
        split_ifs
        · rw [one_div]
        · positivity
      have hdd0 : (0 : ℝ) ≤ (dd ij : ℝ) := Nat.cast_nonneg _
      have h5 : (dd ij : ℝ) * ((if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) * E) ≤
          (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε hE.le) hdd0
      have h6 : (|(vw w (zA ij) : ℝ)| / E + |(vw w (zA' ij) : ℝ)| / E + 4 * (T1 / E) +
          5 * T3 + (dd ij : ℝ) * (((ell w : ℕ) : ℝ) ^ 2)⁻¹ +
          6 * (dl w / E) + (yy ij : ℝ) * (2 * (T2 / E))) * E =
          |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| + 4 * T1 +
          5 * (T3 * E) + (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) +
          6 * dl w + (yy ij : ℝ) * (2 * T2) := by
        have := hE.ne'
        field_simp
      rw [h6]
      linarith)
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).1 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).2 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hT ij s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    (fun ij b s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hTd ij b s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    hbud
    (fun F => by
      refine le_trans (le_of_eq ?_) (hBδ F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
    (fun s _ F => by
      refine le_trans (le_of_eq ?_) (partial_nat K (qq s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
  unfold gridBudgetIdx
  refine le_trans (le_of_eq ?_) key
  apply Finset.sum_congr rfl
  intro w _
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w Finset.univ (fun ij => rr w ij) (fun ij _ => hrr w ij), ← Finset.sum_div, hlam]
  push_cast
  rfl

theorem height_h0_index_bound : PassageSizeIndexed := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a dF EM hInf BF p2 bb
    hR hM hM0 hΨ hincl hEM hh hBF Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq
    B BN0 Bδ ha hdl hS hN0 hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN00 hBN0 hBδ hsize
  have hg := gridHeightBoundIndexed K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq B BN0 Bδ T
    hdl hS hN0 hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN00 hBN0 hBδ
  have h := grid_function_bound K W κ D hD XE kap b' X' hXE hkap hX' R M Ψ T a (fun w => ∏ ij, rr w ij) dF EM hInf
    (gridBudgetIdx m N B BN0 Bδ S0 ee qq) BF hR hM hM0 hΨ hincl ha hEM hh hg hBF
  linarith

example (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (W0 : Finset (Pl K)) :
    ∑ w ∈ W0, lw w * (vw w (∏ _ij : Fin 1 × Fin 1, (32 : K)) : ℝ) ≤
      gridBudgetIdx 1 1 0 (Real.log 2) 0 (∅ : Finset Empty) (fun _ => 0) (fun _ => 0) := by
  have hone : ∀ w : Pl K, vw w (1 : K) = 0 := fun w => (Formalism.DivisionValues.valuation_basic_properties K w).2.2.2.2.1
  have hHt : HtLe (K := K) (fun _ => 0) 1 0 := by
    unfold Formalism.PairingDivisionLocalBalance.HtLe
    simp [hone]
  refine gridHeightBoundIndexed K Empty 1 1 (fun _ => 0) {2} ∅ (fun _ _ _ => 1) (fun _ _ => 32) (fun _ => 1)
    (fun _ => 1) (fun _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 0) (fun _ => false) (fun _ => 2)
    (fun _ => 1) (fun _ => 0) ∅ (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 (Real.log 2) 0 W0
    (fun _ => le_rfl) (by simp [Nat.prime_two]) (fun _ _ _ _ _ _ => zero_le_one) (by simp)
    (fun _ _ => by norm_num) (fun _ => rfl) (fun _ => le_rfl) (fun _ => Nat.zero_le _) (by simp)
    ?_ (fun _ => ⟨hHt, hHt⟩) (fun _ _ => hHt) (fun _ _ _ => hHt) (Real.log_nonneg (by norm_num))
    (fun _ _ _ _ => by simp) (fun _ => by simp)
  intro w _ ij
  have vmul := (Formalism.DivisionValues.valuation_basic_properties K w).1
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h32 : vw w (32 : K) = 5 * vw w (2 : K) := by
    have e : (32 : K) = 2 * (2 * (2 * (2 * 2))) := by norm_num
    rw [e, vmul _ _ h2 (by norm_num), vmul _ _ h2 (by norm_num), vmul _ _ h2 (by norm_num),
      vmul _ _ h2 h2]
    ring
  simp [hone, h32, Formalism.PairingDivisionLocalBalance.wt]

end Formalism.AtG
end
end
