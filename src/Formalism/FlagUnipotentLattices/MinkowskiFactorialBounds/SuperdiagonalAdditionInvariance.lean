import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement
import Formalism.SobolevGaussianKernels.KernelBoundRel

namespace Formalism.HermitianLatticeCounting.P.S4aux

open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset

theorem maximal_sum_bound : MaxSum := by
  intro D _ w μ amp ε Mx hw hμ hε ha hM
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have h1 : ‖amp d‖ ^ 2 ≤ (ε * μ d) ^ 2 := by gcongr; exact ha d
  have h2 : (ε * μ d) ^ 2 ≤ ε ^ 2 * Mx * μ d := by
    have : μ d * μ d ≤ Mx * μ d := mul_le_mul_of_nonneg_right (hM d) (hμ d)
    nlinarith [sq_nonneg ε]
  calc w d * ‖amp d‖ ^ 2 ≤ w d * (ε ^ 2 * Mx * μ d) := mul_le_mul_of_nonneg_left (h1.trans h2) (hw d)
    _ = _ := by ring


theorem involution_well_defined : TauWell := by
  intro E _ _ V _ _ h O abelian₂ th r f f' g c c' hL hI hg hd hf hc' ⟨w, hw, he⟩ j
  choose t ht hte using hf
  have key : ∑ i, (c' i - c i) • f i = th • (w - ∑ i, c' i • t i) := by
    have : ∑ i, (c' i - c i) • f i = (∑ i, c' i • f' i - ∑ i, c i • f i) - ∑ i, c' i • (f' i - f i) := by
      simp only [sub_smul, smul_sub, Finset.sum_sub_distrib]; abel
    rw [this, he, smul_sub, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hte i, smul_comm]
  have hm : w - ∑ i, c' i • t i ∈ abelian₂ := abelian₂.sub_mem hw (abelian₂.sum_mem fun i _ => hL _ (hc' i) _ (ht i))
  refine ⟨h (w - ∑ i, c' i • t i) (g j), hI _ hm _ (hg j), ?_⟩
  have := congrArg (fun z => h z (g j)) key
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul] at this
  simpa using this

theorem orbit_count_formula : OmCount := by
  intro P Om H hH
  calc (2:ℝ)^Om.card = ∏ p ∈ Om, (2:ℝ) := by simp
    _ ≤ ∏ p ∈ Om, H p := Finset.prod_le_prod (fun _ _ => by norm_num) hH


theorem weighted_cauchy_schwarz : WeightedCS := by
  intro ι _ V _ v W hW
  calc ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (inv_pos.2 (hW i)).le)
        (fun i _ => mul_nonneg (hW i).le (sq_nonneg _)) (fun i _ => ?_)
      have := (hW i).ne'
      apply le_of_eq
      field_simp

theorem type_cauchy_schwarz : TypeCS := by
  intro D Ty _ _ w amp hw
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [← Finset.mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hw d)
  calc ‖∑ t, amp t d‖ ^ 2 ≤ (∑ t, ‖amp t d‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset Ty)) (f := fun t => ‖amp t d‖)
      simpa using this


theorem hermitian_count_assembly : AssemblyNG := by
  intro c C₀
  obtain ⟨C', hC'⟩ : ∃ n : ℕ, max 1 (C₀ ^ 2) ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max 1 (C₀ ^ 2)) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  refine ⟨4 * c + C', ?_⟩
  intro k r q e H nn D Ty _ _ w amp μ be I isBe he hk hq hH hqH hnn hw hTy hbe hI hIbe hIal hμ hμM hsum hamp hampbe
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5 := ⟨k - 2 * r - 5, by omega⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e1]; rw [e2] at hampbe
  have e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4) := by omega
  rw [e3] at hμM hsum
  set B : ℝ := max 1 (C₀ ^ 2) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hHc : 0 < H ^ (c * e) := by positivity
  by_cases hne : Nonempty Ty
  swap
  · have : IsEmpty Ty := not_nonempty_iff.1 hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    positivity
  have hqH' := hqH hne
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    obtain ⟨ε, hε0, hε, hεb⟩ : ∃ ε : ℝ, 0 ≤ ε ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧
        ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹) ≤ B * ((q : ℝ) ^ K)⁻¹ := by
      by_cases hb : isBe t
      · refine ⟨|C₀| * ((q : ℝ) ^ (K + 1))⁻¹, by positivity, fun d => ?_, ?_⟩
        · refine (hampbe t d hb).trans ?_
          gcongr
          · exact hμ t d
          · exact le_abs_self _
        · have h1 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]
            exact pow_le_pow_left₀ (hI t) (hIbe t) _
          have h2 : (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ B * ((q : ℝ) ^ K)⁻¹ := by
            rw [mul_pow, sq_abs]
            have h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹ := by
              rw [inv_pow, ← pow_mul]
              apply inv_anti₀ (by positivity)
              exact pow_le_pow_right₀ hq1 (by omega)
            exact mul_le_mul (le_max_right _ _) h3 (by positivity) (by positivity)
          calc _ ≤ (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 * 1 := by gcongr
            _ ≤ _ := by rw [mul_one]; exact h2
      · refine ⟨1, zero_le_one, fun d => by rw [one_mul]; exact hamp t d, ?_⟩
        have h1 : I t ^ (K + (2 * r + 4)) ≤ be t ^ (K + (2 * r + 4)) * ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ := by
          rw [← div_eq_mul_inv, ← div_pow]
          exact pow_le_pow_left₀ (hI t) (hIal t hb) _
        have h2 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [h1]
        have h3 : ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ K)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        calc _ = I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ := by ring
          _ ≤ 1 * ((q : ℝ) ^ K)⁻¹ := by rw [one_mul]; exact h2.trans h3
          _ ≤ _ := by gcongr
    have hms := maximal_sum_bound D w (μ t) (amp t) ε (H ^ (c * e) * I t ^ (K + (2 * r + 4))) hw (hμ t) hε0 hε (hμM t)
    have hI' : 0 ≤ I t ^ (K + (2 * r + 4)) := pow_nonneg (hI t) _
    calc _ ≤ _ := hms
      _ ≤ ε ^ 2 * (H ^ (c * e) * I t ^ (K + (2 * r + 4))) * (H ^ (c * e) * (be t ^ (K + (2 * r + 4)))⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹)) * (H ^ (c * e) * H ^ (c * e) * nn) := by ring
      _ ≤ (B * ((q : ℝ) ^ K)⁻¹) * (H ^ (c * e) * H ^ (c * e) * nn) := by gcongr
      _ = _ := by ring
  have hBH : B ≤ H ^ (C' * e) := by
    calc B ≤ (2 : ℝ) ^ C' := hC'
      _ ≤ H ^ C' := by
          gcongr
          refine le_trans ?_ hqH'
          exact_mod_cast hq
      _ ≤ H ^ (C' * e) := pow_le_pow_right₀ hH (Nat.le_mul_of_pos_right _ he)
  calc _ ≤ _ := type_cauchy_schwarz D Ty w amp hw
    _ ≤ H ^ (c * e) * ∑ t : Ty, B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H ^ (c * e) * (B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H ^ (c * e) * (H ^ (c * e) * (H ^ (C' * e) * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        gcongr
    _ = _ := by
        have : H ^ ((4 * c + C') * e) = H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (C' * e) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
        rw [this]; ring

theorem fourth_reduction_identity : Step4 := by
  intro P _ _ Om D _ w aN aZ H nn ngen q c κ hw hH hq hnn hN hZ hgen
  set 𝒜 := Om.powerset.filter (fun A => A.Nonempty) with h𝒜
  have hcard : (𝒜.card : ℝ) ≤ (2 : ℝ) ^ Om.card := by
    have : 𝒜.card ≤ 2 ^ Om.card := by
      rw [← Finset.card_powerset]; exact Finset.card_filter_le _ _
    exact_mod_cast this
  have hHc : ∀ p, 0 < H p ^ c := fun p => pow_pos (lt_of_lt_of_le one_pos (hH p)) _

  have one : ∀ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
      ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    intro A hA
    obtain ⟨hAO, p0, hp0⟩ : A ⊆ Om ∧ A.Nonempty := by
      simpa [h𝒜, Finset.mem_filter, Finset.mem_powerset] using hA
    set g : P → ℝ := fun p => if p ∈ A then ((q p : ℝ) ^ κ)⁻¹ else 1 with hg
    have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
    have hq2 : ∀ p, ((q p : ℝ) ^ κ)⁻¹ ≤ ((2 : ℝ) ^ κ)⁻¹ := fun p => by
      apply inv_anti₀ (by positivity)
      gcongr
      exact_mod_cast hq p
    have h21 : ((2 : ℝ) ^ κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hg1 : ∀ p, g p ≤ 1 := fun p => by
      simp only [hg]; split_ifs
      · exact (hq2 p).trans h21
      · exact le_rfl
    have hgp : ∏ p, g p ≤ ((2 : ℝ) ^ κ)⁻¹ := by
      rw [← Finset.mul_prod_erase univ g (Finset.mem_univ p0)]
      calc g p0 * ∏ p ∈ univ.erase p0, g p ≤ ((2 : ℝ) ^ κ)⁻¹ * 1 := by
            apply mul_le_mul
            · simp only [hg, if_pos hp0]; exact hq2 p0
            · exact Finset.prod_le_one (fun p _ => hg0 p) (fun p _ => hg1 p)
            · exact Finset.prod_nonneg fun p _ => hg0 p
            · positivity
        _ = _ := mul_one _
    calc ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
        ≤ ∏ p, (H p ^ c * (H p ^ c * ngen p)) * g p := by
          refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _))
            fun p _ => ?_
          have hb : H p ^ c * nn p ≤ H p ^ c * (H p ^ c * ngen p) :=
            mul_le_mul_of_nonneg_left (hgen p) (hHc p).le
          by_cases hp : p ∈ A
          · simp only [hg, if_pos hp]
            calc _ ≤ _ := hN p (hAO hp)
              _ = (H p ^ c * nn p) * ((q p : ℝ) ^ κ)⁻¹ := by ring
              _ ≤ _ := by gcongr
          · simp only [hg, if_neg hp, mul_one]
            exact (hZ p).trans hb
      _ = ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ∏ p, g p := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow, two_mul, pow_add]; ring
      _ ≤ ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ((2 : ℝ) ^ κ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left hgp ?_
          refine mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _)
            (Finset.prod_nonneg fun p _ => ?_)
          have := (hnn p).trans (hgen p)
          exact nonneg_of_mul_nonneg_right this (hHc p)
      _ = _ := by ring
  have hR0 : 0 ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    refine mul_nonneg (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _) (by positivity))
      (Finset.prod_nonneg fun p _ => ?_)
    have := (hnn p).trans (hgen p)
    exact nonneg_of_mul_nonneg_right this (hHc p)
  calc ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
          ((𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ‖(if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2) := by
        refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun p _ => hw p _)
        calc ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
            ≤ (∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖) ^ 2 := by
              gcongr; exact norm_sum_le _ _
          _ ≤ (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = _ := by
              congr 1
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [norm_prod, Finset.prod_pow]
    _ = (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2 := by
        simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ (2 : ℝ) ^ Om.card * ∑ A ∈ 𝒜, (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
        apply mul_le_mul hcard (Finset.sum_le_sum one) _ (by positivity)
        exact Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun p _ => Finset.sum_nonneg fun x _ =>
          mul_nonneg (hw p x) (sq_nonneg _)
    _ = (2 : ℝ) ^ Om.card * ((𝒜.card : ℝ) * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Om.card * ((2 : ℝ) ^ Om.card * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        gcongr
    _ = _ := by
        have : (4 : ℝ) ^ Om.card = (2 : ℝ) ^ Om.card * (2 : ℝ) ^ Om.card := by
          rw [← mul_pow]; norm_num
        rw [this]; ring

lemma geo_half (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (N : ℕ) : ∑ l ∈ range N, y ^ l ≤ 2 - 2 * y ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ y ^ N := pow_nonneg hy0 _
    nlinarith

lemma sum_cond_le {Ψ : Type*} [Fintype Ψ] (cond : Ψ → ℕ) (g B : ℕ → ℝ)
    (hb : ∀ i, ((univ.filter fun ψ => cond ψ = i).card : ℝ) * g i ≤ B i) :
    ∃ N, ∀ N' ≥ N, ∑ ψ, g (cond ψ) ≤ ∑ i ∈ range N', B i := by
  refine ⟨(univ.sup cond) + 1, fun N' hN' => ?_⟩
  have hmaps : ∀ ψ ∈ (univ : Finset Ψ), cond ψ ∈ range N' := fun ψ _ => by
    have := Finset.le_sup (f := cond) (Finset.mem_univ ψ)
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_trans (le_of_eq ?_) (hb i)
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [(Finset.mem_filter.1 hψ).2] : ∀ ψ ∈ univ.filter (fun ψ => cond ψ = i), g (cond ψ) = g i),
    Finset.sum_const, nsmul_eq_mul]

lemma orth_sum {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) :
    (∑ u ∈ univ.filter (fun u => Q u = 0), f u) * (Fintype.card T : ℂ)
      = ∑ ψ : AddChar T ℂ, ∑ u, ψ (Q u) * f u := by
  rw [Finset.sum_comm, Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  split_ifs <;> ring

lemma y_facts (q ρ : ℕ) (hq : 2 ≤ q) (hρ : 4 ≤ ρ) :
    (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ ∧ 0 ≤ (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
      (q : ℝ) ^ (1 - (ρ : ℤ)) ≤ 1 / 8 := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ := by
    rw [zpow_sub₀ hq0.ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  refine ⟨h1, by positivity, ?_⟩
  obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = ρ' + 4 := ⟨ρ - 4, by omega⟩
  have h2 : (q : ℝ) * ((q : ℝ) ^ (ρ' + 4))⁻¹ = ((q : ℝ) ^ (ρ' + 3))⁻¹ := by
    rw [pow_succ (q : ℝ) (ρ' + 3)]; field_simp
  rw [h1, h2, one_div]
  apply inv_anti₀ (by norm_num)
  calc (8 : ℝ) = 2 ^ 3 := by norm_num
    _ ≤ (q : ℝ) ^ 3 := by gcongr
    _ ≤ (q : ℝ) ^ (ρ' + 3) := pow_le_pow_right₀ (by linarith) (by omega)

lemma gauss_core {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ)
    (hq : 2 ≤ q) (hρ : 4 ≤ ρ) (hT : Fintype.card T = q ^ a)
    (hc0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0)
    (hcnt : ∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i)
    (hS : ∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * f u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) :
    ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)‖
      ≤ 2 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) := by
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  have hq0 : (0 : ℝ) < q := by positivity
  set g : ℕ → ℝ := fun i => if i = 0 then 0 else ((q : ℝ) ^ (i * ρ))⁻¹ with hg
  set B : ℕ → ℝ := fun i => if i = 0 then 0 else y ^ i with hB
  have hgB : ∀ i, ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) * g i ≤ B i := by
    intro i
    by_cases hi : i = 0
    · simp [hg, hB, hi]
    · simp only [hg, hB, if_neg hi]
      have : y ^ i = (q : ℝ) ^ i * ((q : ℝ) ^ (i * ρ))⁻¹ := by
        rw [hy, mul_pow, inv_pow, ← pow_mul, mul_comm ρ i]
      rw [this]
      gcongr
      exact hcnt i (Nat.one_le_iff_ne_zero.2 hi)
  obtain ⟨N, hN⟩ := sum_cond_le cond g B hgB
  have hsumB : ∑ i ∈ range (N + 1), B i ≤ 2 * y := by
    rw [Finset.sum_range_succ']
    simp only [hB, if_true, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    have := geo_half y hy0 (by linarith) N
    have h2 : ∑ k ∈ range N, y ^ (k + 1) = y * ∑ k ∈ range N, y ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [h2]
    have h3 : 0 ≤ y ^ N := pow_nonneg hy0 _
    nlinarith
  have hmain : ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u‖
      ≤ 2 * y * (Fintype.card U : ℝ) := by
    have h0 := orth_sum Q f
    rw [hT, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar T ℂ))] at h0
    simp only [AddChar.zero_apply, one_mul] at h0
    push_cast at h0
    rw [h0, add_sub_cancel_left]
    calc _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar T ℂ), ‖∑ u, ψ (Q u) * f u‖ := norm_sum_le _ _
      _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar T ℂ), g (cond ψ) * (Fintype.card U : ℝ) := by
          refine Finset.sum_le_sum fun ψ hψ => ?_
          have hψ0 : ψ ≠ 0 := (Finset.mem_erase.1 hψ).1
          have : cond ψ ≠ 0 := fun h => hψ0 ((hc0 ψ).1 h)
          simp only [hg, if_neg this]
          exact hS ψ hψ0
      _ ≤ ∑ ψ, g (cond ψ) * (Fintype.card U : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun ψ _ _ => ?_
          simp only [hg]; split_ifs <;> positivity
      _ = (∑ ψ, g (cond ψ)) * (Fintype.card U : ℝ) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          exact (hN (N + 1) (by omega)).trans hsumB
  have hqa : ((q : ℂ) ^ a) ≠ 0 := by
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    exact pow_ne_zero _ this
  have hnq : ‖((q : ℂ) ^ a)‖ = (q : ℝ) ^ a := by simp
  have : (∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)
      = ((∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u) / ((q : ℂ) ^ a) := by
    field_simp
  rw [this, norm_div, hnq, ← mul_div_assoc]
  gcongr






lemma adj_mem {E : Type} [CommRing E] (O : Subring E) (m : ℕ) (G : Matrix (Fin m) (Fin m) E)
    (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let M : Matrix (Fin m) (Fin m) O := Matrix.of fun a b => ⟨G a b, hG a b⟩
  have : G = M.map O.subtype := by ext a b; rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2

lemma gram_pair {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (m : ℕ) (f : Fin m → V) (c : Fin m → E) (j : Fin m) :
    h (∑ i, c i • f i) (f j) = ∑ i, c i * h (f i) (f j) := by
  simp [map_sum, LinearMap.sum_apply]








theorem hermitian_gauss_sum_ring : HermGaussRing := by
  intro S _ _ _ n Gm ψ φ hdet hφ hadd
  classical
  set yv : (Fin n → S) → Fin n → S := fun d => Gm.mulVec (fun j => star (d j)) with hyv
  have hB : ∀ u d : Fin n → S, ∑ i, ∑ j, u i * Gm i j * star (d j) = ∑ i, u i * yv d i := by
    intro u d
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hyv, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp only [hB] at hadd
  set T : (Fin n → S) → ℂ := fun d => ∑ v : Fin n → S, ψ (∑ i, v i * yv d i) with hT
  have h1 : ((‖∑ u, φ u‖ ^ 2 : ℝ) : ℂ) = ∑ d, φ d * T d := by
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    have : ∀ v : Fin n → S, ∑ u, φ u * (starRingEnd ℂ) (φ v) = ∑ d, φ d * ψ (∑ i, v i * yv d i) := by
      intro v
      rw [← Fintype.sum_equiv (Equiv.addLeft v) (fun d => φ (v + d) * (starRingEnd ℂ) (φ v)) _ (fun d => rfl)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hadd]
      have : φ v * (starRingEnd ℂ) (φ v) = 1 := by rw [Complex.mul_conj', hφ]; simp
      linear_combination (φ d * ψ (∑ i, v i * yv d i)) * this
    simp_rw [this, hT, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hTle : ∀ d, ‖T d‖ ≤ (Fintype.card S : ℝ) ^ n := by
    intro d
    calc ‖T d‖ ≤ ∑ v : Fin n → S, ‖ψ (∑ i, v i * yv d i)‖ := norm_sum_le _ _
      _ = _ := by simp [AddChar.norm_apply]
  have hT0 : ∀ d, (¬ ∀ i c, ψ (c * yv d i) = 1) → T d = 0 := by
    intro d hd
    push Not at hd
    obtain ⟨i, c, hc⟩ := hd
    have : T d = ψ (c * yv d i) * T d := by
      conv_lhs => rw [hT]
      simp only
      rw [← Fintype.sum_equiv (Equiv.addRight (Pi.single i c : Fin n → S))
        (fun v : Fin n → S => ψ (∑ k, (v + (Pi.single i c : Fin n → S)) k * yv d k)) _ (fun v => rfl), hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · simp
    have h2 : (1 - ψ (c * yv d i)) * T d = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm hc
    · exact h3
  have hinj : Function.Injective yv := by
    intro d d' hdd
    have h3 : ∀ x : Fin n → S, Gm⁻¹.mulVec (Gm.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Gm hdet, Matrix.one_mulVec]
    have h4 : (fun j => star (d j)) = fun j => star (d' j) := by
      rw [← h3 (fun j => star (d j)), ← h3 (fun j => star (d' j))]
      exact congrArg _ hdd
    ext j
    exact star_injective (congrFun h4 j)
  have hcount : ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ)
      ≤ (Nat.card {y : S // ∀ c, ψ (c * y) = 1} : ℝ) ^ n := by
    have : (univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card
        ≤ Nat.card (Fin n → {y : S // ∀ c, ψ (c * y) = 1}) := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective
        (fun d : {d // ∀ i c, ψ (c * yv d i) = 1} => fun i => (⟨yv d.1 i, d.2 i⟩ : {y : S // ∀ c, ψ (c * y) = 1})) ?_
      intro d d' hdd
      apply Subtype.ext
      apply hinj
      ext i
      exact congrArg Subtype.val (congrFun hdd i)
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact_mod_cast this
  have h2 : ‖∑ u, φ u‖ ^ 2 = ‖∑ d, φ d * T d‖ := by
    rw [← h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h2]
  calc ‖∑ d, φ d * T d‖ ≤ ∑ d, ‖φ d * T d‖ := norm_sum_le _ _
    _ = ∑ d, ‖T d‖ := by simp [hφ]
    _ ≤ ∑ d, if (∀ i c, ψ (c * yv d i) = 1) then (Fintype.card S : ℝ) ^ n else 0 := by
        refine Finset.sum_le_sum fun d _ => ?_
        split_ifs with hd
        · exact hTle d
        · rw [hT0 d hd, norm_zero]
    _ = ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ) * (Fintype.card S : ℝ) ^ n := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        rw [mul_comm]
        gcongr



section unfold
variable {G X : Type} [Group G] [MulAction G X]
open MulAction


lemma mem_orbit_sub (K : Subgroup G) (z w : X) : w ∈ orbit K z ↔ ∃ k ∈ K, k • z = w := by
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩


end unfold

lemma fiber_sum {X : Type} (A B : Finset X) (R : X → X → Prop) [∀ z, DecidablePred (R z)] (F : X → ℝ)
    (nb : X → ℕ) (h1 : ∀ z ∈ A, ∃ z' ∈ B, R z z')
    (h2 : ∀ z ∈ A, ∀ z' ∈ B, R z z' → (B.filter (R z)).card = nb z') :
    ∑ z ∈ A, F z = ∑ z ∈ A, ∑ z' ∈ B.filter (R z), F z / nb z' := by
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨z0, hz0, hR0⟩ := h1 z hz
  have hpos : 0 < (B.filter (R z)).card := Finset.card_pos.2 ⟨z0, Finset.mem_filter.2 ⟨hz0, hR0⟩⟩
  rw [Finset.sum_congr rfl (fun z' hz' => by
    rw [← h2 z hz z' (Finset.mem_filter.1 hz').1 (Finset.mem_filter.1 hz').2] :
      ∀ z' ∈ B.filter (R z), F z / nb z' = F z / ((B.filter (R z)).card : ℝ)),
    Finset.sum_const, nsmul_eq_mul]
  have : ((B.filter (R z)).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp


section dualcap
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]


lemma unram_one (hU : Unram o O) : ∃ l : O →ₗ[o] o, l 1 = 1 := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  have hne : Nonempty (Module.Free.ChooseBasisIndex o O) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := Module.finrank_eq_card_basis b
    rw [hU.rank2, Fintype.card_eq_zero] at this
    omega
  obtain ⟨i0⟩ := hne
  by_cases hex : ∃ i, IsUnit (b.repr 1 i)
  · obtain ⟨i, u, hu⟩ := hex
    refine ⟨((u⁻¹ : oˣ) : o) • b.coord i, ?_⟩
    rw [LinearMap.smul_apply, Module.Basis.coord_apply, ← hu, smul_eq_mul, Units.inv_mul]
  · exfalso
    push Not at hex
    have h1 : b i0 = ∑ j, b.repr 1 j • (b j * b i0) := by
      conv_lhs => rw [← one_mul (b i0), ← b.sum_repr 1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc]
    have h2 : (1 : o) = ∑ j, b.repr 1 j * b.repr (b j * b i0) i0 := by
      have := congrArg (fun z => b.repr z i0) h1
      simpa [map_sum, Finsupp.finsetSum_apply] using this
    have h3 : (1 : o) ∈ IsLocalRing.maximalIdeal o := by
      rw [h2]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hex j))
    exact (IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 h3)

lemma unram_trace (hU : Unram o O) : ∃ T : O →ₗ[o] o, ∀ a, algebraMap o O (T a) = a + star a := by
  obtain ⟨l, hl⟩ := unram_one hU
  obtain ⟨b0, hb0⟩ := hU.tr_perfect l
  let sl : O →ₗ[o] O :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun c a => by
        simp only [Algebra.smul_def, star_mul', hU.star_o, RingHom.id_apply] }
  have h1 : star b0 + b0 = 1 := by
    have := hb0 1
    rw [hl, map_one, one_mul, star_star] at this
    exact this.symm
  refine ⟨l + l ∘ₗ sl, fun a => ?_⟩
  rw [LinearMap.add_apply, LinearMap.comp_apply, map_add, hb0, hb0]
  change a * star b0 + star (a * star b0) + (star a * star b0 + star (star a * star b0)) = _
  simp only [star_mul', star_star]
  linear_combination (a + star a) * h1

end dualcap


lemma herm_split {E : Type} [CommRing E] [StarRing E] (O : Subring E)
    (htr : ∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c) (r : ℕ) (γ : Fin r → Fin r → E)
    (hO : ∀ j k, γ j k ∈ O) (hγ : ∀ j k, star (γ j k) = γ k j) :
    ∃ c : Fin r → Fin r → E, (∀ j k, c j k ∈ O) ∧ ∀ j k, c j k + star (c k j) = γ j k := by
  have hdiag : ∀ j, ∃ s ∈ O, s + star s = γ j j := fun j => htr _ (hO j j) (hγ j j)
  choose s hs hss using hdiag
  refine ⟨fun j l => if j < l then γ j l else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩
  · dsimp only
    split_ifs
    exacts [hO j l, hs j, O.zero_mem]
  · rcases lt_trichotomy j k with hjk | hjk | hjk
    · simp [hjk, hjk.not_gt, hjk.ne']
    · subst hjk; simp [hss]
    · simp [hjk, hjk.not_gt, hjk.ne', hγ]

section sametrace
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)

def shear (t : Fin r → V) : V →ₗ[E] V where
  toFun v := v + ∑ j, h v (e j) • t j
  map_add' v w := by
    simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add,
      Finset.smul_sum]

lemma shear_apply (t : Fin r → V) (v : V) : shear h e t v = v + ∑ j, h v (e j) • t j := rfl

lemma shear_pair (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) (i : Fin r) :
    h (shear h e t v) (e i) = h v (e i) := by
  simp [shear_apply, map_sum, LinearMap.sum_apply, ht]

lemma shear_inv (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) :
    shear h e (fun j => - t j) (shear h e t v) = v := by
  rw [shear_apply]
  simp only [shear_pair h e t ht]
  rw [shear_apply]
  simp

end sametrace


namespace Part2



theorem inTh_add {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {th : E} {abelian₂ : AddSubgroup V} {a b : V}
    (ha : InTh th abelian₂ a) (hb : InTh th abelian₂ b) : InTh th abelian₂ (a + b) := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ⟨x + y, abelian₂.add_mem hx hy, (smul_add _ _ _).symm⟩

theorem assemblyNG2 (H1 : TypeCS) : AssemblyNG2 := by
  intro c
  refine ⟨4 * c, ?_⟩
  intro k e H nn D Ty _ _ w amp μ be I hH hnn hw hcard hbe hI hIbe hμ hμI hsum hamp
  set A : ℝ := H ^ (c * e) with hA
  have hA0 : 0 ≤ A := by positivity
  have step : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ A * A * nn := by
    intro t
    have hb : 0 < be t ^ (k - 1) := by have := hbe t; positivity
    calc ∑ d, w d * ‖amp t d‖ ^ 2 ≤ ∑ d, (A * I t ^ (k - 1)) * (w d * μ t d) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have h1 : ‖amp t d‖ ^ 2 ≤ (A * I t ^ (k - 1)) * μ t d := by
            calc ‖amp t d‖ ^ 2 ≤ μ t d ^ 2 := by
                  exact pow_le_pow_left₀ (norm_nonneg _) (hamp t d) 2
              _ = μ t d * μ t d := by ring
              _ ≤ (A * I t ^ (k - 1)) * μ t d := mul_le_mul_of_nonneg_right (hμI t d) (hμ t d)
          calc w d * ‖amp t d‖ ^ 2 ≤ w d * ((A * I t ^ (k - 1)) * μ t d) :=
                mul_le_mul_of_nonneg_left h1 (hw d)
            _ = _ := by ring
      _ = (A * I t ^ (k - 1)) * ∑ d, w d * μ t d := by rw [Finset.mul_sum]
      _ ≤ (A * I t ^ (k - 1)) * (A * (be t ^ (k - 1))⁻¹ * nn) :=
          mul_le_mul_of_nonneg_left (hsum t) (mul_nonneg hA0 (pow_nonneg (hI t) _))
      _ = A * A * nn * (I t ^ (k - 1) * (be t ^ (k - 1))⁻¹) := by ring
      _ ≤ A * A * nn * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← div_eq_mul_inv, div_le_one hb]
          exact pow_le_pow_left₀ (hI t) (hIbe t) _
      _ = A * A * nn := by ring
  calc ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ (Fintype.card Ty : ℝ) * ∑ t, ∑ d, w d * ‖amp t d‖ ^ 2 :=
        H1 D Ty w amp hw
    _ ≤ (Fintype.card Ty : ℝ) * ∑ _t : Ty, A * A * nn :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => step t) (Nat.cast_nonneg _)
    _ = (Fintype.card Ty : ℝ) * (Fintype.card Ty : ℝ) * (A * A * nn) := by simp; ring
    _ ≤ A * A * (A * A * nn) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hcard hcard (Nat.cast_nonneg _) hA0
    _ = H ^ (4 * c * e) * nn := by
        rw [hA, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; ring





end Part2

theorem hermitian_count_assembly_of_type : AssemblyNG2 := Part2.assemblyNG2 type_cauchy_schwarz

section dvrcard
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

lemma index_span_pow (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) :
    (Ideal.span {ϖ ^ i}).toAddSubgroup.index = q ^ i := by
  have h1 := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal o)
    (IsDiscreteValuationRing.not_a_field o) (i := i)
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h1
  have h2 : Submodule.cardQuot (Ideal.span {ϖ}) = q := by
    rw [← hq, ← hϖ.maximalIdeal_eq]; rfl
  rw [h2] at h1
  exact h1


end dvrcard


section count
variable {F : Type} [Field F] [Fintype F]

lemma mulVec_surj {j n : ℕ} (M : Matrix (Fin j) (Fin n) F) (hM : LinearIndependent F M.row) :
    Function.Surjective M.mulVec := by
  have h1 : M.rank = j := by simpa using hM.rank_matrix
  have h2 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h1]; simp
  intro y
  have : y ∈ LinearMap.range M.mulVecLin := by rw [h2]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, hx⟩

lemma fiber_card [DecidableEq F] {j n : ℕ} (M : Matrix (Fin j) (Fin n) F)
    (hM : LinearIndependent F M.row) (g : Fin j → F) :
    (univ.filter fun y : Fin n → F => M.mulVec y = g).card * Fintype.card F ^ j
      = Fintype.card F ^ n := by
  have hs := mulVec_surj M hM
  have heq : ∀ g', (univ.filter fun y : Fin n → F => M.mulVec y = g').card
      = (univ.filter fun y : Fin n → F => M.mulVec y = g).card := fun g' =>
    AddMonoidHom.card_fiber_eq_of_mem_range M.mulVecLin.toAddMonoidHom (hs g') (hs g)
  have h1 := Finset.card_eq_sum_card_fiberwise (f := M.mulVec) (s := (univ : Finset (Fin n → F)))
    (t := (univ : Finset (Fin j → F))) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_fin] at h1
  rw [h1, mul_comm]

lemma dep_one [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) (lam : Fin m → F) (j0 : Fin m) (hj0 : lam j0 ≠ 0) :
    ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card * c ≤ c ^ m := by
  have h1 : ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card
      ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card := by
    refine Finset.card_le_card_of_injOn (fun Y => Function.update Y j0 0) ?_ ?_
    · intro Y hY
      have hY' := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).1
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro j
      by_cases hj : j = j0
      · subst hj; simp
      · simp only [Function.update_of_ne hj]; exact hY' j
    · intro Y hY Y' hY' hYY
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).2
      have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY')).2
      have hne : ∀ j, j ≠ j0 → Y j = Y' j := by
        intro j hj
        have := congrFun hYY j
        simpa only [Function.update_of_ne hj] using this
      have e3 : ∑ j, lam j • (Y j - Y' j) = 0 := by
        simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
      rw [Finset.sum_eq_single j0 (fun j _ hj => by rw [hne j hj, sub_self, smul_zero])
        (fun h => absurd (Finset.mem_univ _) h)] at e3
      have e4 : Y j0 = Y' j0 := by
        rcases smul_eq_zero.1 e3 with h | h
        · exact absurd h hj0
        · exact sub_eq_zero.1 h
      funext j
      by_cases hj : j = j0
      · rw [hj]; exact e4
      · exact hne j hj
  have h2 : (Fintype.piFinset (Function.update Fs j0 {0})).card * c = c ^ m := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j0)]
    have h3 : ∏ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c ^ (m - 1) := by
      rw [Finset.prod_congr rfl (fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), hc] :
          ∀ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c)]
      simp
    rw [h3]
    simp only [Function.update_self, Finset.card_singleton, one_mul]
    have : 1 ≤ m := by have := j0.2; omega
    rw [← pow_succ]; congr 1; omega
  calc _ ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card * c := Nat.mul_le_mul_right _ h1
    _ = _ := h2



end count

lemma density_arith (Q : ℝ) (hQ : 2 ≤ Q) (n m : ℕ) (hn : 2 * m + 3 ≤ n) (c NX tot : ℝ)
    (hc : c * Q ^ m = Q ^ n)
    (hX1 : NX ≤ (Q ^ n) ^ m) (hX2 : (Q ^ n) ^ m - Q ^ m * (Q ^ n) ^ m / Q ^ n ≤ NX)
    (ht1 : tot ≤ NX * c ^ m) (ht2 : NX * (c ^ m - Q ^ m * c ^ m / c) ≤ tot) :
    Q ^ (2 * n * m) / Q ^ (m ^ 2) / 2 ≤ tot ∧ tot ≤ 2 * (Q ^ (2 * n * m) / Q ^ (m ^ 2)) := by
  have hQ0 : 0 < Q := by linarith
  have hQm : 0 < Q ^ m := by positivity
  have hQn : 0 < Q ^ n := by positivity
  have hc0 : 0 < c := by
    by_contra h
    push Not at h
    have : c * Q ^ m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hQm.le
    linarith
  have hcm : 0 < c ^ m := by positivity
  have hA : 0 < (Q ^ n) ^ m := by positivity
  have hmain : Q ^ (2 * n * m) / Q ^ (m ^ 2) = (Q ^ n) ^ m * c ^ m := by
    rw [div_eq_iff (by positivity)]
    have : c ^ m * Q ^ (m ^ 2) = (Q ^ n) ^ m := by
      rw [← hc, mul_pow, ← pow_mul, sq]
    calc Q ^ (2 * n * m) = (Q ^ n) ^ m * (Q ^ n) ^ m := by
          rw [← pow_mul, ← pow_add]; congr 1; ring
      _ = _ := by rw [← this]; ring
  have h8 : (8 : ℝ) ≤ Q ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := by gcongr
  have e1 : Q ^ m / Q ^ n ≤ 1 / 8 := by
    rw [div_le_iff₀ hQn]
    have : Q ^ n = Q ^ m * Q ^ (n - m) := by rw [← pow_add]; congr 1; omega
    have h3 : Q ^ 3 ≤ Q ^ (n - m) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [this]
    nlinarith
  have e2 : Q ^ m / c ≤ 1 / 8 := by
    rw [div_le_iff₀ hc0]
    have h4 : Q ^ n = Q ^ m * Q ^ m * Q ^ (n - 2 * m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h3 : Q ^ 3 ≤ Q ^ (n - 2 * m) := pow_le_pow_right₀ (by linarith) (by omega)
    have h5 : c = Q ^ m * Q ^ (n - 2 * m) := by
      have : c * Q ^ m = (Q ^ m * Q ^ (n - 2 * m)) * Q ^ m := by rw [hc, h4]; ring
      exact mul_right_cancel₀ hQm.ne' this
    rw [h5]
    nlinarith
  rw [hmain]
  have hX2' : (Q ^ n) ^ m * (7 / 8) ≤ NX := by
    have : Q ^ m * (Q ^ n) ^ m / Q ^ n = (Q ^ n) ^ m * (Q ^ m / Q ^ n) := by ring
    rw [this] at hX2
    nlinarith
  have hY2 : c ^ m * (7 / 8) ≤ c ^ m - Q ^ m * c ^ m / c := by
    have : Q ^ m * c ^ m / c = c ^ m * (Q ^ m / c) := by ring
    rw [this]
    nlinarith
  have hNX0 : 0 ≤ NX := by nlinarith
  constructor
  · calc (Q ^ n) ^ m * c ^ m / 2 ≤ ((Q ^ n) ^ m * (7 / 8)) * (c ^ m * (7 / 8)) := by nlinarith [mul_pos hA hcm]
      _ ≤ NX * (c ^ m - Q ^ m * c ^ m / c) := by
          apply mul_le_mul hX2' hY2 (by positivity) hNX0
      _ ≤ tot := ht2
  · calc tot ≤ NX * c ^ m := ht1
      _ ≤ (Q ^ n) ^ m * c ^ m := by gcongr
      _ ≤ _ := by nlinarith [mul_pos hA hcm]



section inert
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

lemma frob_add (x y : L) :
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K :=
  map_add (FiniteField.frobeniusAlgHom K L) x y

lemma frob_sum {ι : Type} (s : Finset ι) (f : ι → L) :
    (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K :=
  map_sum (FiniteField.frobeniusAlgHom K L) f s

lemma card_L (h2 : Module.finrank K L = 2) : Fintype.card L = Fintype.card K ^ 2 := by
  rw [← h2]; exact Module.card_eq_pow_finrank

lemma frob_frob (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ Fintype.card K) ^ Fintype.card K = x := by
  rw [← pow_mul, ← sq, ← card_L h2, FiniteField.pow_card]

@[reducible] def frobStar (h2 : Module.finrank K L = 2) : StarRing L where
  star x := x ^ Fintype.card K
  star_involutive := frob_frob h2
  star_mul x y := by rw [mul_pow, mul_comm]
  star_add := frob_add

lemma trace_eq (h2 : Module.finrank K L = 2) (z : L) :
    algebraMap K L (Algebra.trace K L z) = z + z ^ Fintype.card K := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, h2, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.card_eq_fintype_card]
  simp

lemma trace_surj : Function.Surjective (Algebra.trace K L) := by
  have : FiniteDimensional K L := Module.Finite.of_finite
  exact Algebra.trace_surjective K L

lemma gauss_inert (h2 : Module.finrank K L = 2) (n : ℕ) (Ph : Matrix (Fin n) (Fin n) L)
    (hPh : IsUnit Ph.det) (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (φ : (Fin n → L) → ℂ)
    (hφ : ∀ u, ‖φ u‖ = 1)
    (hadd : ∀ u d, φ (u + d) = φ u * φ d *
      ψ (Algebra.trace K L (∑ i, ∑ j, u i * Ph i j * d j ^ Fintype.card K))) :
    ‖∑ u, φ u‖ ≤ (Fintype.card K : ℝ) ^ n := by
  let ψ' : AddChar L ℂ := ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom
  have h := @hermitian_gauss_sum_ring L _ _ (frobStar h2) n Ph ψ' φ hPh hφ hadd
  have hY : Nat.card {y : L // ∀ c, ψ' (c * y) = 1} ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    have h0 : ∀ y : {y : L // ∀ c, ψ' (c * y) = 1}, y.1 = 0 := by
      intro y
      by_contra hy
      apply hψ
      ext k
      obtain ⟨z, rfl⟩ := trace_surj (K := K) (L := L) k
      have := y.2 (z / y.1)
      rw [div_mul_cancel₀ _ hy] at this
      rw [AddChar.zero_apply]
      exact this
    exact ⟨fun y y' => Subtype.ext (by rw [h0 y, h0 y'])⟩
  have hY' : (Nat.card {y : L // ∀ c, ψ' (c * y) = 1} : ℝ) ^ n ≤ 1 := by
    apply pow_le_one₀ (Nat.cast_nonneg _)
    exact_mod_cast hY
  have h3 : ‖∑ u, φ u‖ ^ 2 ≤ ((Fintype.card K : ℝ) ^ n) ^ 2 := by
    calc _ ≤ _ := h
      _ ≤ (Fintype.card L : ℝ) ^ n * 1 := by gcongr
      _ = _ := by rw [card_L h2]; push_cast; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

end inert

section inert2
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

def hB {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  ∑ k, ∑ l, x k * Ph k l * y l ^ Fintype.card K

def hMat {n j : ℕ} (Ph : Matrix (Fin n) (Fin n) L) (X : Fin j → Fin n → L) :
    Matrix (Fin j) (Fin n) L :=
  Matrix.of fun b k => ∑ l, Ph k l * X b l ^ Fintype.card K

variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

lemma hB_add_left (x d y : Fin n → L) : hB K Ph (x + d) y = hB K Ph x y + hB K Ph d y := by
  simp only [hB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hB_add_right (x y d : Fin n → L) : hB K Ph x (y + d) = hB K Ph x y + hB K Ph x d := by
  simp only [hB, Pi.add_apply, frob_add, mul_add, Finset.sum_add_distrib]

lemma hB_conj (h2 : Module.finrank K L = 2) (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K)
    (x y : Fin n → L) : hB K Ph x y ^ Fintype.card K = hB K Ph y x := by
  simp only [hB, frob_sum, mul_pow, frob_frob h2, ← hherm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

lemma hB_mulVec {j : ℕ} (X : Fin j → Fin n → L) (x : Fin n → L) (b : Fin j) :
    hB K Ph x (X b) = (hMat K Ph X).mulVec x b := by
  simp only [hB, hMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma hMat_li (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) : LinearIndependent L (hMat K Ph X).row := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set w : Fin n → L := fun l => ∑ b, g b * X b l ^ Fintype.card K with hw
  have h1 : Ph.mulVec w = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, hMat, Matrix.of_apply, smul_eq_mul,
      Pi.zero_apply, Finset.mul_sum] at this
    simp only [Matrix.mulVec, dotProduct, hw, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm, ← this]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
  have h3 : w = 0 := by
    have : Ph⁻¹.mulVec (Ph.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Ph hPh, Matrix.one_mulVec]
    rw [← this, h1, Matrix.mulVec_zero]
  have h4 : ∑ b, (g b ^ Fintype.card K) • X b = 0 := by
    funext l
    have := congrArg (fun z => z ^ Fintype.card K) (congrFun h3 l)
    simp only [hw, frob_sum, mul_pow, frob_frob h2, Pi.zero_apply] at this
    rw [zero_pow Fintype.card_pos.ne'] at this
    simpa [Finset.sum_apply] using this
  intro b
  have := (Fintype.linearIndependent_iff.1 hX) _ h4 b
  exact pow_eq_zero_iff (Fintype.card_pos.ne') |>.1 this

end inert2

section inert3
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

open scoped Classical in
lemma sumA_bound (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (g : Fin j → L) (bq : (Fin n → L) → K) (hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) :
    ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      ≤ (Fintype.card K : ℝ) ^ n := by
  let ℓ : (Fin n → L) → (Fin j → L) := fun x b => hB K Ph x (X b)
  have hℓ : ∀ u d, ℓ (u + d) = ℓ u + ℓ d := fun u d => by
    funext b; exact hB_add_left Ph u d (X b)
  have hbqadd : ∀ u d, bq (u + d) = bq u + bq d + Algebra.trace K L (hB K Ph u d) := by
    intro u d
    apply (algebraMap K L).injective
    rw [map_add, map_add, hbq, hbq, hbq, trace_eq h2, hB_conj Ph h2 hherm, hB_add_left,
      hB_add_right, hB_add_right]
    ring
  have hfil : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b))
      = univ.filter (fun x : Fin n → L => ℓ x + (-g) = 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ℓ]
    rw [← sub_eq_add_neg, sub_eq_zero, funext_iff]
  have h0 := orth_sum (fun x : Fin n → L => ℓ x + (-g)) (fun x => ψ (bq x))
  rw [← hfil] at h0
  have hχ : ∀ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ ≤ (Fintype.card K : ℝ) ^ n := by
    intro χ
    have e1 : ∑ x, χ (ℓ x + (-g)) * ψ (bq x) = χ (-g) * ∑ x, χ (ℓ x) * ψ (bq x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.map_add_eq_mul]; ring
    rw [e1, norm_mul, AddChar.norm_apply, one_mul]
    refine gauss_inert h2 n Ph hPh ψ hψ (fun x => χ (ℓ x) * ψ (bq x)) (fun u => ?_) (fun u d => ?_)
    · rw [norm_mul, AddChar.norm_apply, AddChar.norm_apply, one_mul]
    · change χ (ℓ (u + d)) * ψ (bq (u + d)) = χ (ℓ u) * ψ (bq u) * (χ (ℓ d) * ψ (bq d)) *
        ψ (Algebra.trace K L (hB K Ph u d))
      rw [hℓ, hbqadd, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
  have hT : (0 : ℝ) < (Fintype.card (Fin j → L) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      * (Fintype.card (Fin j → L) : ℝ) ≤ (Fintype.card K : ℝ) ^ n * (Fintype.card (Fin j → L) : ℝ) := by
    calc _ = ‖(∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x))
          * (Fintype.card (Fin j → L) : ℂ)‖ := by rw [norm_mul]; simp
      _ ≤ ∑ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ := by
          rw [h0]; exact norm_sum_le _ _
      _ ≤ ∑ χ : AddChar (Fin j → L) ℂ, (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum fun χ _ => hχ χ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, AddChar.card_eq, nsmul_eq_mul, mul_comm]
  exact le_of_mul_le_mul_right h1 hT

open scoped Classical in
lemma step_Z (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    |(Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c|
      ≤ (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n := by
  obtain ⟨θ, hθ⟩ := trace_surj (K := K) (L := L) 1
  have hθ' : θ + θ ^ Fintype.card K = 1 := by
    rw [← trace_eq h2, hθ, map_one]
  have hfix : ∀ z : L, z ^ Fintype.card K = z → algebraMap K L (Algebra.trace K L (θ * z)) = z := by
    intro z hz
    rw [trace_eq h2, mul_pow, hz]
    linear_combination z * hθ'
  let bq : (Fin n → L) → K := fun x => Algebra.trace K L (θ * hB K Ph x x)
  have hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x := fun x => hfix _ (hB_conj Ph h2 hherm x x)
  let a0 : K := Algebra.trace K L (θ * a)
  have ha0 : algebraMap K L a0 = a := hfix a ha
  have hQ : ∀ x, bq x + (-a0) = 0 ↔ hB K Ph x x = a := by
    intro x
    rw [← sub_eq_add_neg, sub_eq_zero, ← hbq, ← ha0]
    exact (algebraMap K L).injective.eq_iff.symm
  have hA : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b)).card = c := by
    have h1 := fiber_card (hMat K Ph X) (hMat_li Ph h2 hPh X hX) g
    rw [card_L h2, ← hc] at h1
    have h3 := Nat.eq_of_mul_eq_mul_right (by positivity) h1
    rw [← h3]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hB_mulVec, funext_iff]
  have h0 := orth_sum (fun x : Fin n → L => bq x + (-a0))
    (fun x => if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
  have hL : ∑ x ∈ univ.filter (fun x : Fin n → L => bq x + (-a0) = 0),
      (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
      = ((univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℂ) := by
    rw [Finset.sum_boole, Finset.filter_filter]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
    exact and_comm
  rw [hL, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar K ℂ))] at h0
  simp only [AddChar.zero_apply, one_mul] at h0
  rw [Finset.sum_boole, hA] at h0
  have hψb : ∀ ψ ∈ univ.erase (0 : AddChar K ℂ),
      ‖∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)‖
        ≤ (Fintype.card K : ℝ) ^ n := by
    intro ψ hψ
    have e1 : ∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
        = ψ (-a0) * ∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.map_add_eq_mul]
      split_ifs <;> ring
    rw [e1, norm_mul, AddChar.norm_apply, one_mul]
    exact sumA_bound Ph h2 hPh hherm X g bq hbq ψ (Finset.ne_of_mem_erase hψ)
  have e2 : (((Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c : ℝ) : ℂ)
      = ∑ ψ ∈ univ.erase (0 : AddChar K ℂ),
        ∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0) := by
    push_cast
    linear_combination h0
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e2]
  calc _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar K ℂ), _ := norm_sum_le _ _
    _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar K ℂ), (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum hψb
    _ = ((univ.erase (0 : AddChar K ℂ)).card : ℝ) * (Fintype.card K : ℝ) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        have : (univ.erase (0 : AddChar K ℂ)).card ≤ Fintype.card K := by
          calc _ ≤ (univ : Finset (AddChar K ℂ)).card := Finset.card_le_card (Finset.erase_subset _ _)
            _ = _ := by rw [Finset.card_univ, AddChar.card_eq]
        exact_mod_cast this

open scoped Classical in
lemma step_alt (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    (Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ)
      ≤ c + (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n ∧
    (c : ℝ) - (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n
        - (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) ^ 2) ^ j
      ≤ (Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) := by
  have hZ := abs_le.1 (step_Z Ph h2 hPh hherm X hX g a ha c hc)
  set Z := univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) with hZd
  have hsplit := Finset.card_filter_add_card_filter_not (s := Z)
    (fun x => x ∈ Submodule.span L (Set.range X))
  have hs : Z.filter (fun x => ¬ x ∈ Submodule.span L (Set.range X))
      = univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) := by
    ext x
    simp only [hZd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hs] at hsplit
  have hspan : (Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card
      ≤ (Fintype.card K ^ 2) ^ j := by
    calc _ ≤ (univ.image fun cf : Fin j → L => ∑ b, cf b • X b).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (Finset.mem_filter.1 hx).2
          exact Finset.mem_image.2 ⟨cf, Finset.mem_univ _, hcf⟩
      _ ≤ (univ : Finset (Fin j → L)).card := Finset.card_image_le
      _ = _ := by simp [card_L h2]
  have hspanR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)
      ≤ ((Fintype.card K : ℝ) ^ 2) ^ j := by exact_mod_cast hspan
  have hsplitR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)
      + ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) = (Z.card : ℝ) := by
    exact_mod_cast hsplit
  have hq0 : (0 : ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  have h0 : (0 : ℝ) ≤ ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ) :=
    Nat.cast_nonneg _
  constructor
  · nlinarith [hZ.2]
  · nlinarith [hZ.1]

end inert3

lemma step_arith (q N a W Qj Cj C' lo hi : ℝ) (hq : 2 ≤ q) (hN : 0 < N) (ha : 0 < a)
    (hWa : W * a = N ^ 2) (hsmall : q ^ 2 * a * 8 ≤ N) (hQ : 0 ≤ Qj)
    (h1 : (1 - a / N) * Qj ≤ Cj) (h2 : Cj ≤ (1 + a / N) * Qj)
    (hlo : lo = (W - q * N - q * a) / q) (hhi : hi = (W + q * N) / q)
    (hC1 : Cj * lo ≤ C') (hC2 : C' ≤ Cj * hi) :
    (1 - q ^ 2 * a / N) * (Qj * W / q) ≤ C' ∧ C' ≤ (1 + q ^ 2 * a / N) * (Qj * W / q) := by
  obtain ⟨d, hd⟩ : ∃ d, d = a / N := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < d := by rw [hd]; positivity
  have haN : a = N * d := by rw [hd]; field_simp
  have hW0 : 0 < W := by
    by_contra h
    push Not at h
    have : W * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ha.le
    have : 0 < N ^ 2 := by positivity
    linarith
  have hNW : N = W * d := by
    have : W * d * N = N * N := by rw [mul_assoc, mul_comm d N, ← haN, hWa]; ring
    exact (mul_right_cancel₀ hN.ne' this).symm
  have hqd : q ^ 2 * d ≤ 1 / 8 := by
    have : q ^ 2 * (N * d) * 8 ≤ N := by rw [← haN]; exact hsmall
    have h3 : N * (q ^ 2 * d * 8) ≤ N * 1 := by nlinarith
    have := le_of_mul_le_mul_left h3 hN
    linarith
  have hqd1 : q * d ≤ 1 / 8 := by nlinarith
  have hd1 : d ≤ 1 / 8 := by nlinarith
  have e1 : q ^ 2 * a / N = q ^ 2 * d := by rw [hd]; ring
  rw [e1]
  rw [← hd] at h1 h2
  have hlo' : lo = (1 - q * d - q * d ^ 2) * (W / q) := by
    rw [hlo, haN, hNW]; field_simp
  have hhi' : hi = (1 + q * d) * (W / q) := by
    rw [hhi, hNW]; field_simp
  have hWq : 0 < W / q := by positivity
  have hCj0 : 0 ≤ Cj := le_trans (mul_nonneg (by linarith) hQ) h1
  have hA : 0 ≤ q ^ 2 - q - 2 := by nlinarith
  have key1 : (1 + d) * (1 + q * d) ≤ 1 + q ^ 2 * d := by
    nlinarith [mul_nonneg hd0.le hA, mul_nonneg hd0.le (sub_nonneg.2 hqd1)]
  have key2 : 1 - q ^ 2 * d ≤ (1 - d) * (1 - q * d - q * d ^ 2) := by
    nlinarith [mul_nonneg hd0.le hA, mul_pos hq0 (pow_pos hd0 3)]
  have hl0 : 0 ≤ 1 - q * d - q * d ^ 2 := by nlinarith
  have hP : 0 ≤ Qj * (W / q) := mul_nonneg hQ hWq.le
  have eP : Qj * W / q = Qj * (W / q) := by ring
  rw [eP]
  constructor
  · calc (1 - q ^ 2 * d) * (Qj * (W / q)) ≤ ((1 - d) * (1 - q * d - q * d ^ 2)) * (Qj * (W / q)) :=
          mul_le_mul_of_nonneg_right key2 hP
      _ = ((1 - d) * Qj) * lo := by rw [hlo']; ring
      _ ≤ Cj * lo := by
          apply mul_le_mul_of_nonneg_right h1
          rw [hlo']; positivity
      _ ≤ C' := hC1
  · calc C' ≤ Cj * hi := hC2
      _ ≤ ((1 + d) * Qj) * hi := by
          apply mul_le_mul_of_nonneg_right h2
          rw [hhi']; positivity
      _ = ((1 + d) * (1 + q * d)) * (Qj * (W / q)) := by rw [hhi']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key1 hP

section inert4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

open scoped Classical in
lemma cnt_succ (h2 : Module.finrank K L = 2) (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K)
    (j : ℕ) (G : Matrix (Fin (j + 1)) (Fin (j + 1)) L) (hG : ∀ a b, G b a = G a b ^ Fintype.card K) :
    (univ.filter fun X : Fin (j + 1) → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card
      = ∑ X' ∈ univ.filter (fun X' : Fin j → Fin n → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ),
        (univ.filter fun x : Fin n → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card := by
  have key : ∀ (x : Fin n → L) (X' : Fin j → Fin n → L),
      (LinearIndependent L (Fin.cons x X' : Fin (j + 1) → Fin n → L) ∧
        ∀ a b, hB K Ph ((Fin.cons x X' : Fin (j + 1) → Fin n → L) a)
          ((Fin.cons x X' : Fin (j + 1) → Fin n → L) b) = G a b) ↔
      ((LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) ∧
        (x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0)) := by
    intro x X'
    rw [linearIndependent_finCons]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨h1, h3⟩, ⟨h4, h5⟩, h6⟩
      exact ⟨⟨h1, fun a b => (h6 a).2 b⟩, h3, h5, h4⟩
    · rintro ⟨⟨h1, h3⟩, h4, h5, h6⟩
      refine ⟨⟨h1, h4⟩, ⟨h6, h5⟩, fun a => ⟨?_, h3 a⟩⟩
      rw [← hB_conj Ph h2 hherm, h5, ← hG]
  rw [Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin n → L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun X' _ => ?_
  rw [Finset.card_filter]
  by_cases hV : LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ
  · rw [if_pos hV]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact if_congr ((key x X').trans (and_iff_right hV)) rfl rfl
  · rw [if_neg hV]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact if_neg fun h => hV ((key x X').1 h).1

open scoped Classical in
lemma cnt_bounds (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) (j : ℕ) : 2 * j + 3 ≤ n →
    ∀ G : Matrix (Fin j) (Fin j) L, (∀ a b, G b a = G a b ^ Fintype.card K) →
    (1 - ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2))
      ≤ ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ) ∧
    ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ)
      ≤ (1 + ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2)) := by
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < (Fintype.card K : ℝ) := by linarith
  induction j with
  | zero =>
    intro _ G _
    have : (univ.filter fun X : Fin 0 → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b) = univ := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨linearIndependent_empty_type, fun a => a.elim0⟩
    rw [this]
    have hd : 0 ≤ 1 / (Fintype.card K : ℝ) ^ n := by positivity
    simp only [Finset.card_univ, Fintype.card_unique, Nat.cast_one, pow_zero, mul_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_one, mul_one]
    constructor <;> linarith
  | succ j ih =>
    intro hn G hG
    obtain ⟨t, rfl⟩ : ∃ t, n = j + t := ⟨n - j, by omega⟩
    have ih' := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    simp only [Matrix.submatrix_apply] at ih'
    rw [cnt_succ Ph h2 hherm j G hG]
    set valid := univ.filter (fun X' : Fin j → Fin (j + t) → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) with hvalid
    have hc : (Fintype.card K ^ 2) ^ t * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ (j + t) := by
      rw [← pow_add, add_comm]
    have hstep : ∀ X' ∈ valid, _ := fun X' hX' =>
      step_alt Ph h2 hPh hherm X' (Finset.mem_filter.1 hX').2.1 (fun b => G 0 b.succ) (G 0 0)
        (hG 0 0).symm ((Fintype.card K ^ 2) ^ t) hc
    push_cast
    push_cast at hstep
    set q : ℝ := (Fintype.card K : ℝ) with hq
    have hres := step_arith q (q ^ (j + t)) ((q ^ 2) ^ j) ((q ^ 2) ^ t)
      (q ^ (2 * (j + t) * j) / q ^ (j ^ 2)) (valid.card : ℝ)
      (∑ X' ∈ valid, ((univ.filter fun x : Fin (j + t) → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card : ℝ))
      (((q ^ 2) ^ t - q * q ^ (j + t) - q * (q ^ 2) ^ j) / q) (((q ^ 2) ^ t + q * q ^ (j + t)) / q)
      hq2 (by positivity) (by positivity)
      (by rw [← pow_add, ← pow_mul, ← pow_mul]; congr 1; ring)
      (by
        have h8 : (8 : ℝ) ≤ q ^ 3 := by
          calc (8 : ℝ) = 2 ^ 3 := by norm_num
            _ ≤ q ^ 3 := by gcongr
        have e : q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j * q ^ (t - j - 2) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
        have h3 : q ^ 3 ≤ q ^ (t - j - 2) := pow_le_pow_right₀ (by linarith) (by omega)
        rw [e]
        have : 0 < q ^ 2 * (q ^ 2) ^ j := by positivity
        nlinarith)
      (by positivity) ih'.1 ih'.2 rfl rfl
      (by
        rw [← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun X' hX' => ?_
        rw [div_le_iff₀ hq0]
        linarith [(hstep X' hX').2])
      (by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun X' hX' => ?_
        rw [le_div_iff₀ hq0]
        linarith [(hstep X' hX').1])
    have eQ : q ^ (2 * (j + t) * (j + 1)) / q ^ ((j + 1) ^ 2)
        = q ^ (2 * (j + t) * j) / q ^ (j ^ 2) * (q ^ 2) ^ t / q := by
      rw [div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity), ← pow_mul,
        ← pow_succ, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    have ed : (q ^ 2) ^ (j + 1) / q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j / q ^ (j + t) := by
      rw [pow_succ]; ring
    rw [eQ, ed]
    exact hres

end inert4



lemma det_mul_eq_zero_of_card_lt {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hlt : Fintype.card κ < Fintype.card ι) (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).det = 0 := by
  obtain ⟨e⟩ : Nonempty (κ ↪ ι) := Function.Embedding.nonempty_of_card_le hlt.le
  obtain ⟨l0, hl0⟩ : ∃ l0, l0 ∉ Set.range e := by
    by_contra hcon
    push Not at hcon
    have : Function.Surjective e := hcon
    have := Fintype.card_le_of_surjective e this
    omega
  let P : Matrix κ ι R := (1 : Matrix ι ι R).submatrix e id
  have hPP : P * P.transpose = 1 := by
    ext j j'
    simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      e.injective.eq_iff]
  have h1 : A * B = (A * P) * (P.transpose * B) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
  rw [h1, Matrix.det_mul]
  have h2 : (A * P).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro i
    simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => hl0 ⟨j, h⟩), mul_zero]
  rw [h2, zero_mul]

section unram2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

lemma unram_inj (hU : Unram o O) : Function.Injective (algebraMap o O) := by
  obtain ⟨l, hl⟩ := unram_one hU
  intro t t' h
  have e : ∀ t : o, l (algebraMap o O t) = t := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one]
  rw [← e t, ← e t', h]

lemma unram_fixed (hU : Unram o O) (y : O) (hy : star y = y) : ∃ t : o, algebraMap o O t = y := by
  obtain ⟨T, hT⟩ := unram_trace hU
  obtain ⟨s, hs⟩ := hU.tr_onto 1
  refine ⟨T (y * s), ?_⟩
  rw [hT, star_mul', hy, ← mul_add, hs, map_one, mul_one]

def mO (o O : Type) [CommRing o] [IsLocalRing o] [CommRing O] [Algebra o O] : Ideal O :=
  (IsLocalRing.maximalIdeal o).map (algebraMap o O)

lemma mO_ne_top (hU : Unram o O) : (1 : O) ∉ mO o O := by
  obtain ⟨l, hl⟩ := unram_one hU
  let J' : Ideal O :=
    { carrier := {x | ∀ y, l (y * x) ∈ IsLocalRing.maximalIdeal o}
      add_mem' := fun {a b} ha hb y => by
        rw [mul_add, map_add]; exact Ideal.add_mem _ (ha y) (hb y)
      zero_mem' := fun y => by rw [mul_zero, map_zero]; exact Ideal.zero_mem _
      smul_mem' := fun c x hx y => by
        rw [smul_eq_mul, ← mul_assoc]; exact hx (y * c) }
  have hle : mO o O ≤ J' := by
    rw [mO, Ideal.map_le_iff_le_comap]
    intro t ht y
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ht
  intro h1
  have := hle h1 1
  rw [mul_one, hl] at this
  exact (IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 this)

lemma not_unit_of_mem_mO (hU : Unram o O) (x : O) (hx : x ∈ mO o O) : ¬ IsUnit x := by
  rintro ⟨u, rfl⟩
  apply mO_ne_top hU
  have := Ideal.mul_mem_left (mO o O) ((u⁻¹ : Oˣ) : O) hx
  rwa [Units.inv_mul] at this

lemma mem_mO_of_trace (hU : Unram o O) (T : O →ₗ[o] o) (hT : ∀ a, algebraMap o O (T a) = a + star a)
    (z : O) (hz : ∀ s, T (s * z) ∈ IsLocalRing.maximalIdeal o) : z ∈ mO o O := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  rw [← b.sum_repr z]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨bi, hbi⟩ := hU.tr_perfect (b.coord i)
  have h1 := hbi z
  rw [mul_comm z (star bi), ← hT, Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hz _))

lemma polar_mO (hU : Unram o O) {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O) (hH : IsHerm h) (C : Submodule O abelian₂)
    (hC : ∀ c ∈ C, ¬ IsUnit (h c c)) : ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ mO o O := by
  obtain ⟨T, hT⟩ := unram_trace hU
  have hnorm : ∀ c ∈ C, ∃ t ∈ IsLocalRing.maximalIdeal o, algebraMap o O t = h c c := by
    intro c hc
    obtain ⟨t, ht⟩ := unram_fixed hU (h c c) (hH c c).symm
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hC c hc (ht ▸ hu.map (algebraMap o O))
  intro c hc c' hc'
  apply mem_mO_of_trace hU T hT
  intro s
  obtain ⟨t1, ht1, e1⟩ := hnorm (s • c + c') (C.add_mem (C.smul_mem s hc) hc')
  obtain ⟨t2, ht2, e2⟩ := hnorm (s • c) (C.smul_mem s hc)
  obtain ⟨t3, ht3, e3⟩ := hnorm c' hc'
  have : T (s * h c c') = t1 - t2 - t3 := by
    apply unram_inj hU
    rw [hT, map_sub, map_sub, e1, e2, e3]
    have e4 : h c' (s • c) = star (s * h c c') := by
      rw [hH (s • c) c', map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [map_add, LinearMap.add_apply, e4]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ ht1 ht2) ht3

end unram2

section orth
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

lemma orth_pair_right {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (j : κ) (w : κ → O) : h (v j) (∑ i, w i • v i) = star (w j) * h (v j) (v j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
  · intro i _ hi
    rw [LinearMap.map_smulₛₗ, horth j i (Ne.symm hi), smul_zero]
  · intro hj; exact absurd (Finset.mem_univ _) hj

lemma orth_pair_gen {κ : Type} [Fintype κ] (v : κ → abelian₂) (x : abelian₂) (w : κ → O) :
    h x (∑ i, w i • v i) = ∑ i, star (w i) * h x (v i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]

lemma orth_pair_left {κ : Type} [Fintype κ] (v : κ → abelian₂) (x : abelian₂) (w : κ → O) :
    h (∑ i, w i • v i) x = ∑ i, w i * h (v i) x := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

lemma orth_proj {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (u : κ → Oˣ) (hu : ∀ i, (u i : O) = h (v i) (v i)) (x : abelian₂) (j : κ) :
    h (x - ∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i) (v j) = 0 := by
  rw [map_sub, LinearMap.sub_apply, orth_pair_left, Finset.sum_eq_single j]
  · rw [← hu, mul_assoc, Units.inv_mul, mul_one, sub_self]
  · intro i _ hi
    rw [horth i j hi, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ _) hj

lemma orth_li {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hunit : ∀ i, IsUnit (h (v i) (v i))) : LinearIndependent O v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 : h (∑ i, g i • v i) (v j) = 0 := by rw [hg]; simp
  rw [orth_pair_left, Finset.sum_eq_single j (fun i _ hi => by rw [horth i j hi, mul_zero])
    (fun hj => absurd (Finset.mem_univ _) hj)] at h1
  exact (hunit j).mul_left_eq_zero.1 h1

lemma orth_span [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Module.Free O (Submodule.span O (Set.range v)) ∧
    Module.finrank O (Submodule.span O (Set.range v)) = Fintype.card κ ∧
    (∀ x, ∃ t ∈ Submodule.span O (Set.range v), ∀ t' ∈ Submodule.span O (Set.range v),
      h (x - t) t' = 0) ∧
    (∀ φ : Submodule.span O (Set.range v) →ₗ[O] O, ∃ w ∈ Submodule.span O (Set.range v),
      ∀ x : Submodule.span O (Set.range v), φ x = h x w) := by
  have hli := orth_li h v horth hunit
  choose u hu using hunit
  have hmem : ∀ i, v i ∈ Submodule.span O (Set.range v) := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.Free.of_basis (Module.Basis.span hli), ?_, fun x => ?_, fun φ => ?_⟩
  · rw [finrank_span_eq_card hli]
  · refine ⟨∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun t' ht' => ?_⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 ht'
    rw [orth_pair_gen]
    exact Finset.sum_eq_zero fun j _ => by rw [orth_proj h v horth u hu, mul_zero]
  · refine ⟨∑ i, star (φ ⟨v i, hmem i⟩ * ((u i)⁻¹ : Oˣ)) • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun x => ?_⟩
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 x.2
    have hx : x = ∑ j, w j • (⟨v j, hmem j⟩ : Submodule.span O (Set.range v)) := by
      apply Subtype.ext
      rw [← hw]
      simp
    rw [← hw, orth_pair_left]
    conv_lhs => rw [hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, orth_pair_right h v horth, star_star, ← hu, mul_assoc,
      Units.inv_mul, mul_one]

end orth

section unimod
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

lemma gram_unit (hSD : SelfDual h) :
    IsUnit (Matrix.of fun i l : Module.Free.ChooseBasisIndex O abelian₂ =>
      h (Module.Free.chooseBasis O abelian₂ i) (Module.Free.chooseBasis O abelian₂ l)).det := by
  classical
  let b := Module.Free.chooseBasis O abelian₂
  have hw : ∀ i, ∃ w, ∀ x, b.coord i x = h x w := fun i => hSD.2 (b.coord i)
  choose w hw using hw
  let Pst : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun l i => star (b.repr (w i) l)
  have hmul : (Matrix.of fun i l => h (b i) (b l)) * Pst = 1 := by
    ext j i
    rw [Matrix.mul_apply]
    have h1 : h (b j) (w i) = ∑ l, h (b j) (b l) * star (b.repr (w i) l) := by
      conv_lhs => rw [← b.sum_repr (w i), map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, mul_comm]
    have h3 : h (b j) (w i) = if j = i then 1 else 0 := by
      rw [← hw, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [Matrix.of_apply, Pst]
    rw [← h1, h3, Matrix.one_apply]
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

lemma exists_unit_vec_gen [Nontrivial O] (J : Ideal O) (hJ : ∀ x ∈ J, ¬ IsUnit x)
    (hpol : ∀ C : Submodule O abelian₂, (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ J)
    (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by
  classical
  by_contra hcon
  push Not at hcon
  have hH := hSD.1
  let C : Submodule O abelian₂ :=
    { carrier := {c | ∀ i, h c (v i) = 0}
      add_mem' := fun {a b} ha hb i => by rw [map_add, LinearMap.add_apply, ha i, hb i, add_zero]
      zero_mem' := fun i => by simp
      smul_mem' := fun r c hc i => by rw [map_smul, LinearMap.smul_apply, hc i, smul_zero] }
  have hCJ := hpol C (fun c hc => hcon c hc)
  let b := Module.Free.chooseBasis O abelian₂
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O abelian₂) = Module.finrank O abelian₂ :=
    (Module.finrank_eq_card_chooseBasisIndex O abelian₂).symm
  choose u hu using hunit
  let a : Module.Free.ChooseBasisIndex O abelian₂ → κ → O := fun i j => h (b i) (v j) * ((u j)⁻¹ : Oˣ)
  let cc : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂ := fun i => b i - ∑ j, a i j • v j
  have hcc : ∀ i, cc i ∈ C := fun i j => orth_proj h v horth u hu (b i) j
  have hbi : ∀ i, b i = cc i + ∑ j, a i j • v j := fun i => by simp [cc]
  have hG : ∀ i l, h (b i) (b l) = ∑ j, a i j * ((u j : O) * star (a l j)) + h (cc i) (cc l) := by
    intro i l
    have e1 : h (cc i) (∑ j, a l j • v j) = 0 := by
      rw [orth_pair_gen]; exact Finset.sum_eq_zero fun j _ => by rw [hcc i j, mul_zero]
    have e2 : h (∑ j, a i j • v j) (cc l) = 0 := by
      rw [orth_pair_left]
      exact Finset.sum_eq_zero fun j _ => by rw [hH (cc l) (v j), hcc l j, star_zero, mul_zero]
    have e3 : h (∑ j, a i j • v j) (∑ j, a l j • v j) = ∑ j, a i j * ((u j : O) * star (a l j)) := by
      rw [orth_pair_left]
      exact Finset.sum_congr rfl fun j _ => by rw [orth_pair_right h v horth, hu, mul_comm (star _)]
    conv_lhs => rw [hbi i, hbi l]
    rw [map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, e1, e2, e3]
    ring
  have hdet := gram_unit h hSD
  apply hJ _ _ hdet
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
  let A : Matrix (Module.Free.ChooseBasisIndex O abelian₂) κ O := Matrix.of a
  let B : Matrix κ (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun j l => (u j : O) * star (a l j)
  have hmap : (Ideal.Quotient.mk J).mapMatrix (Matrix.of fun i l => h (b i) (b l))
      = (A.map (Ideal.Quotient.mk J)) * (B.map (Ideal.Quotient.mk J)) := by
    rw [← Matrix.map_mul]
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B]
    rw [hG i l, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 (hCJ _ (hcc i) _ (hcc l)), add_zero]
  rw [hmap]
  apply det_mul_eq_zero_of_card_lt
  rw [hcard]
  exact hk

lemma exists_unit_vec (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  exact exists_unit_vec_gen h (mO o O) (not_unit_of_mem_mO hU) (polar_mO hU h hSD.1) hSD v horth hunit hk


end unimod


section unimod2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

lemma extend_family (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (u : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (u i) (u j) = 0) (hunit : ∀ i, IsUnit (h (u i) (u i))) (r : ℕ)
    (hr : Fintype.card κ + r ≤ Module.finrank O abelian₂) :
    ∃ t : Fin r → abelian₂, (∀ i j, h (t i) (u j) = 0) ∧ (∀ i j, i ≠ j → h (t i) (t j) = 0) ∧
      ∀ i, IsUnit (h (t i) (t i)) := by
  induction r with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨t, htu, hto, htn⟩ := ih (by omega)
    obtain ⟨c, hc, hcu⟩ := exists_unit_vec h hU hSD (Sum.elim u t)
      (by
        rintro (i | i) (j | j) hne
        · exact horth i j (fun e => hne (by rw [e]))
        · simp only [Sum.elim_inl, Sum.elim_inr]; rw [hSD.1 (t j) (u i), htu, star_zero]
        · exact htu i j
        · exact hto i j (fun e => hne (by rw [e])))
      (by rintro (i | i); exacts [hunit i, htn i])
      (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
    refine ⟨Fin.cons c t, fun i j => ?_, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hc (Sum.inl j)
      · simpa using htu i j
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simpa using hc (Sum.inr j)
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hSD.1 c (t i)]
        have := hc (Sum.inr i)
        simp only [Sum.elim_inr] at this
        rw [this, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact hto i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using htn i

omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o] in
lemma span_orthogonal_unit_basis_eq_top (v : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Submodule.span O (Set.range v) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis O abelian₂
  let M : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun i l => b.repr (v i) l
  let G : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun l l' => h (b l) (b l')
  have hv : ∀ i, v i = ∑ l, M i l • b l := fun i => (b.sum_repr (v i)).symm
  have hD : M * G * M.conjTranspose = Matrix.diagonal fun i => h (v i) (v i) := by
    ext i i'
    have e1 : h (v i) (v i') = ∑ l', (∑ l, M i l * G l l') * star (M i' l') := by
      conv_lhs => rw [hv i, hv i']
      rw [orth_pair_gen]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [orth_pair_left, mul_comm]
      rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← e1, Matrix.diagonal_apply]
    split_ifs with hii
    · rw [hii]
    · exact horth i i' hii
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (M * G * M.conjTranspose).det := by
      rw [hD, Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 hunit
    rw [Matrix.det_mul, Matrix.det_mul, mul_assoc] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have : b l = ∑ i, M⁻¹ l i • v i := by
    have e2 : ∑ i, M⁻¹ l i • v i = ∑ l', (M⁻¹ * M) l l' • b l' := by
      simp only [Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv i, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l' _ => by rw [smul_smul]
    rw [e2, Matrix.nonsing_inv_mul M hdet]
    simp [Matrix.one_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o] in
lemma full_span [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hcard : Fintype.card κ = Module.finrank O abelian₂) : Submodule.span O (Set.range v) = ⊤ := by
  have e : Module.Free.ChooseBasisIndex O abelian₂ ≃ κ := Fintype.equivOfCardEq (by
    rw [hcard, Module.finrank_eq_card_chooseBasisIndex])
  have := span_orthogonal_unit_basis_eq_top h (v ∘ e) (fun i j hij => horth _ _ (fun hh => hij (e.injective hh)))
    (fun i => hunit _)
  rwa [e.surjective.range_comp] at this

end unimod2


section annih
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

def piO (O : Type) [CommRing O] {o : Type} [CommRing o] [Algebra o O] (ϖ : o) (M : ℕ) : AddSubgroup O where
  carrier := {y | ∃ z, y = algebraMap o O (ϖ ^ M) * z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩; exact ⟨-a, by ring⟩


end annih



section stdform
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

lemma norm_surj (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (ha : a ^ Fintype.card K = a) : ∃ lam : L, lam ^ (Fintype.card K + 1) = a := by
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = Units.mk0 a ha0 :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg _))
  have hord : orderOf g = (Fintype.card K + 1) * (Fintype.card K - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      card_L h2]
    obtain ⟨c, hc⟩ : ∃ c, Fintype.card K = c + 1 := ⟨Fintype.card K - 1, by omega⟩
    rw [hc]
    simp only [Nat.add_sub_cancel]
    have : (c + 1) ^ 2 = (c + 1 + 1) * c + 1 := by ring
    omega
  have h1 : (Units.mk0 a ha0) ^ (Fintype.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have : a ^ (Fintype.card K - 1) * a = 1 * a := by
      rw [← pow_succ, one_mul]
      have : Fintype.card K - 1 + 1 = Fintype.card K := by omega
      rw [this, ha]
    exact mul_right_cancel₀ ha0 this
  rw [← hk, ← pow_mul] at h1
  have h3 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h3
  have h4 : (Fintype.card K + 1) ∣ k := Nat.dvd_of_mul_dvd_mul_right (by omega) h3
  obtain ⟨k', rfl⟩ := h4
  refine ⟨((g ^ k' : Lˣ) : L), ?_⟩
  have := congrArg Units.val hk
  rw [Units.val_mk0] at this
  rw [← this, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]

variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)



end stdform


section hermjac
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

omit [StarRing E] in
lemma hj_exists_omega (h2 : Module.finrank F E = 2) : ∃ ω : E, ∀ c : F, algebraMap F E c ≠ ω := by
  by_contra hcon
  push Not at hcon
  have := finrank_le_one (R := F) (1 : E) (fun w => by
    obtain ⟨c, hc⟩ := hcon w
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩)
  omega

omit [StarRing E] in
lemma hj_basis (h2 : Module.finrank F E = 2) (ω : E) (hω : ∀ c : F, algebraMap F E c ≠ ω) :
    ∃ β : Module.Basis (Fin 2) F E, β 0 = 1 ∧ β 1 = ω := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hω (-s / t)
      have h1 : algebraMap F E t * ω = - algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have h3 : algebraMap F E t * algebraMap F E t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [div_eq_mul_inv, map_mul, map_neg]
      linear_combination (-(algebraMap F E t⁻¹)) * h1 + ω * h3
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h2]; rfl), ?_, ?_⟩ <;> simp

omit [StarRing E] in
lemma hj_repr (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (c0 c1 : F) :
    β.repr (algebraMap F E c0 + algebraMap F E c1 * ω) 0 = c0 ∧
    β.repr (algebraMap F E c0 + algebraMap F E c1 * ω) 1 = c1 := by
  have : algebraMap F E c0 + algebraMap F E c1 * ω = c0 • β 0 + c1 • β 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [this]
  constructor <;> simp

omit [StarRing E] in
lemma hj_decomp (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (e : E) :
    e = algebraMap F E (β.repr e 0) + algebraMap F E (β.repr e 1) * ω := by
  conv_lhs => rw [← β.sum_repr e, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]

omit [StarRing E] in
lemma hj_norm (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (t nn : F)
    (hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn) (a b : F) :
    Algebra.norm F (algebraMap F E a + algebraMap F E b * ω) = a ^ 2 + a * b * t + b ^ 2 * nn := by
  rw [Algebra.norm_eq_matrix_det β, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, h0, h1, mul_one]
  have e1 : (algebraMap F E a + algebraMap F E b * ω) * ω
      = algebraMap F E (-(b * nn)) + algebraMap F E (a + b * t) * ω := by
    simp only [map_neg, map_mul, map_add]
    linear_combination (algebraMap F E b) * hω2
  rw [e1, (hj_repr β ω h0 h1 _ _).1, (hj_repr β ω h0 h1 _ _).2, (hj_repr β ω h0 h1 _ _).1,
    (hj_repr β ω h0 h1 _ _).2]
  ring


end hermjac

section hermjacA
variable {E : Type} [CommRing E]

def rmulE (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E :=
  { toFun := fun X : Matrix (Fin m) (Fin m) E => X * A
    map_add' := fun X Y => Matrix.add_mul X Y A
    map_smul' := fun c X => Matrix.smul_mul c X A }

def lmulE (m : ℕ) (B : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E :=
  { toFun := fun X : Matrix (Fin m) (Fin m) E => B * X
    map_add' := fun X Y => Matrix.mul_add B X Y
    map_smul' := fun c X => Matrix.mul_smul B c X }




end hermjacA

section hermjacA2
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]


end hermjacA2


section hermjacB
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

omit [StarRing E] in

noncomputable def dualNumberReal (β : Module.Basis (Fin 2) F E) (ε : E) (h0 : β 0 = 1) (h1 : β 1 = ε) (hε : ε * ε = 0) :
    E →+* F where
  toFun e := β.repr e 0
  map_one' := by
    have := (hj_repr β ε h0 h1 1 0).1
    simpa using this
  map_mul' x y := by
    have e1 : x * y = algebraMap F E (β.repr x 0 * β.repr y 0)
        + algebraMap F E (β.repr x 0 * β.repr y 1 + β.repr x 1 * β.repr y 0) * ε := by
      conv_lhs => rw [hj_decomp β ε h0 h1 x, hj_decomp β ε h0 h1 y]
      simp only [map_mul, map_add]
      linear_combination (algebraMap F E (β.repr x 1) * algebraMap F E (β.repr y 1)) * hε
    conv_lhs => rw [e1]
    exact (hj_repr β ε h0 h1 _ _).1
  map_zero' := by simp
  map_add' x y := by simp


end hermjacB


end Formalism.HermitianLatticeCounting.P.S4aux

namespace Formalism.HermitianLatticeCounting.P

theorem maximal_sum_bound : Formalism.HermitianLatticeCounting.S4.MaxSum := S4aux.maximal_sum_bound
theorem involution_well_defined : Formalism.HermitianLatticeCounting.S4.TauWell := S4aux.involution_well_defined
theorem orbit_count_formula : Formalism.HermitianLatticeCounting.S4.OmCount := S4aux.orbit_count_formula
theorem weighted_cauchy_schwarz : Formalism.HermitianLatticeCounting.S4.WeightedCS := S4aux.weighted_cauchy_schwarz
theorem type_cauchy_schwarz : Formalism.HermitianLatticeCounting.S4.TypeCS := S4aux.type_cauchy_schwarz
theorem hermitian_count_assembly : Formalism.HermitianLatticeCounting.S4.AssemblyNG := S4aux.hermitian_count_assembly
theorem fourth_reduction_identity : Formalism.HermitianLatticeCounting.S4.Step4 := S4aux.fourth_reduction_identity
theorem hermitian_gauss_sum_ring : Formalism.HermitianLatticeCounting.S4.HermGaussRing := S4aux.hermitian_gauss_sum_ring
theorem hermitian_count_assembly_of_type : Formalism.HermitianLatticeCounting.S4.AssemblyNG2 := S4aux.hermitian_count_assembly_of_type

end Formalism.HermitianLatticeCounting.P
