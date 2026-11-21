import Mathlib
import GroundTheory.PAdicHodge.CyclotomicTower
import GroundTheory.PAdicHodge.TiltValuation
import GroundTheory.PAdicHodge.TiltEquiv
import GroundTheory.PAdicHodge.FWGlue

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial

section Ultra

variable {R : Type*} [NormedField R] [IsUltrametricDist R]

theorem norm_le_norm_sum_of_norm_ne {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) :
    ∀ i ∈ s, ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by
  classical
  intro i hi
  obtain ⟨m, hm, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) ⟨i, hi⟩
  refine (hmax i hi).trans ?_
  rcases eq_or_ne (f m) 0 with h0 | h0
  · rw [h0, norm_zero]; exact norm_nonneg _
  rw [← Finset.add_sum_erase s f hm]
  have hlt : ‖∑ j ∈ s.erase m, f j‖ < ‖f m‖ := by
    rcases (s.erase m).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact norm_pos_iff.2 h0
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      refine hle.trans_lt (lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj)) fun heq => ?_)
      by_cases hj0 : f j = 0
      · rw [hj0, norm_zero] at heq; exact h0 (norm_eq_zero.1 heq.symm)
      · exact (Finset.ne_of_mem_erase hj) (hf j (Finset.mem_of_mem_erase hj) m hm hj0 heq)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
  exact le_max_left _ _

end Ultra

variable {p : ℕ} [Fact p.Prime]

theorem exists_eq_sum_sub_one_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {x : PadicAlgCl p} (hx : x ∈ cycl p n) :
    ∃ a : ℕ → ℚ_[p], x = ∑ i ∈ Finset.range (Nat.totient (p ^ n)),
      algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i := by
  have hint : IsIntegral ℚ_[p] (ζ - 1) := Algebra.IsIntegral.isIntegral _
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = Nat.totient (p ^ n) := by
    rw [IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hint,
      adjoin_sub_one_eq_cycl hζ, finrank_cycl]
  have hx' : x ∈ ℚ_[p]⟮ζ - 1⟯ := by rw [adjoin_sub_one_eq_cycl hζ]; exact hx
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨x, hx'⟩
  refine ⟨fun i => f.coeff i, ?_⟩
  have h1 : x = aeval (ζ - 1) f := by
    have := congrArg (algebraMap (ℚ_[p]⟮ζ - 1⟯) (PadicAlgCl p)) hf
    rw [IntermediateField.adjoin.powerBasis_gen, ← aeval_algebraMap_apply] at this
    exact this
  rw [h1, aeval_eq_sum_range' (hfdeg.trans_eq hdim)]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]

section Ortho

variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ

theorem norm_zpow_mul_pow_sub_one_pow (z : ℤ) (m : ℕ) :
    ((p : ℝ) ^ z * ‖ζ - 1‖ ^ m) ^ Nat.totient (p ^ (k + 1)) =
      (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)) - m) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrd := norm_sub_one_pow_totient hζ
  rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, hrd, inv_pow, ← zpow_natCast ((p : ℝ) ^ z),
    ← zpow_mul, ← zpow_natCast (p : ℝ) m, ← zpow_neg, ← zpow_add₀ hp0]
  ring_nf

theorem norm_coeff_mul_le_norm_sum (a : ℕ → ℚ_[p]) :
    ∀ i ∈ Finset.range (Nat.totient (p ^ (k + 1))),
      ‖a i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ j ∈ Finset.range (Nat.totient (p ^ (k + 1))),
        algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j‖ := by
  set d := Nat.totient (p ^ (k + 1))
  have hterm : ∀ i, ‖algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i‖ = ‖a i‖ * ‖ζ - 1‖ ^ i :=
    fun i => by rw [norm_mul, norm_pow, norm_algebraMap']
  intro i hi
  rw [← hterm]
  refine norm_le_norm_sum_of_norm_ne (R := PadicAlgCl p) (Finset.range d)
    (fun j => algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j) (fun i hi j hj hne heq => ?_) i hi
  rw [hterm, hterm] at heq
  have hai : a i ≠ 0 := fun h => hne (by rw [h, map_zero, zero_mul])
  have hr0 : 0 < ‖ζ - 1‖ := by
    have hrd := norm_sub_one_pow_totient hζ
    by_contra h
    have h0 : ‖ζ - 1‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    have hd : d ≠ 0 := (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
    rw [h0, zero_pow hd] at hrd
    exact (inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℝ) ≠ 0)) hrd.symm
  have haj : a j ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at heq
    exact (mul_pos (norm_pos_iff.2 hai) (pow_pos hr0 i)).ne' heq
  obtain ⟨zi, hzi⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) hai
  obtain ⟨zj, hzj⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) haj
  rw [hzi, hzj] at heq
  have h2 := congrArg (· ^ d) heq
  rw [norm_zpow_mul_pow_sub_one_pow hζ, norm_zpow_mul_pow_sub_one_pow hζ] at h2
  have h3 := zpow_p_injective (p := p) h2
  have hdvd : (d : ℤ) ∣ ((i : ℤ) - j) := ⟨zi - zj, by linarith⟩
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  have habs : |(i : ℤ) - j| < d := by rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

theorem norm_coeff_le_one {c : ℚ_[p]} {i : ℕ} (hi : i < Nat.totient (p ^ (k + 1)))
    (h : ‖c‖ * ‖ζ - 1‖ ^ i ≤ 1) : ‖c‖ ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) hc
  rw [hz] at h ⊢
  have h1 : ((p : ℝ) ^ z * ‖ζ - 1‖ ^ i) ^ Nat.totient (p ^ (k + 1)) ≤ 1 :=
    pow_le_one₀ (mul_nonneg (zpow_nonneg (by positivity) _) (pow_nonneg (norm_nonneg _) _)) h
  rw [norm_zpow_mul_pow_sub_one_pow hζ] at h1
  have h2 := (zpow_le_one_iff_right₀ one_lt_p_real).1 h1
  have hz0 : z ≤ 0 := by
    by_contra hz0
    have hz1 : 1 ≤ z := by omega
    have : (Nat.totient (p ^ (k + 1)) : ℤ) ≤ z * Nat.totient (p ^ (k + 1)) := by
      nlinarith
    omega
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) hz0

end Ortho

theorem norm_pow_sub_self_le {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : ‖c ^ p - c‖ ≤ (p : ℝ)⁻¹ := by
  set b : ℤ_[p] := ⟨c, hc⟩
  have h1 : PadicInt.toZMod (b ^ p - b) = 0 := by rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have h2 : b ^ p - b ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact h1
  have h3 : ‖b ^ p - b‖ < 1 := PadicInt.mem_nonunits.1 h2
  obtain ⟨e, he⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h3
  have h4 : ‖c ^ p - c‖ = ‖b ^ p - b‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h4, he, norm_mul, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one e)

theorem not_isUnit_natCast_normInteger : ¬IsUnit (p : normInteger (PadicAlgCl p)) := by
  rintro ⟨u, hu⟩
  have h1 : ‖((u : normInteger (PadicAlgCl p)) : PadicAlgCl p)‖ *
      ‖((u⁻¹ : (normInteger (PadicAlgCl p))ˣ) : PadicAlgCl p)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, norm_one]
  have hu1 := mem_normInteger.1 (u : normInteger (PadicAlgCl p)).2
  have hv1 := mem_normInteger.1 ((u⁻¹ : (normInteger (PadicAlgCl p))ˣ) : normInteger (PadicAlgCl p)).2
  have hu2 : ‖((u : normInteger (PadicAlgCl p)) : PadicAlgCl p)‖ = 1 := by
    nlinarith [norm_nonneg ((u : normInteger (PadicAlgCl p)) : PadicAlgCl p),
      norm_nonneg (((u⁻¹ : (normInteger (PadicAlgCl p))ˣ) : normInteger (PadicAlgCl p)) : PadicAlgCl p)]
  rw [hu] at hu2
  have : ‖(p : PadicAlgCl p)‖ = 1 := by simpa using hu2
  rw [norm_natCast_prime] at this
  have hp1 : (1 : ℝ) < p := one_lt_p_real
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

theorem exists_pow_approx_cycl {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cycl p n) (hx1 : ‖x‖ ≤ 1) :
    ∃ y ∈ cycl p (n + 2), ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : PadicAlgCl p)‖ := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hx' : x ∈ cycl p (n + 1) := cycl_mono (Nat.le_succ n) hx
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (n + 2)
  have hζ : IsPrimitiveRoot (η ^ p) (p ^ (n + 1)) :=
    hη.pow (pow_pos hp0 _) (by ring)
  set ζ := η ^ p
  set d := Nat.totient (p ^ (n + 1))
  obtain ⟨a, ha⟩ := exists_eq_sum_sub_one_pow hζ hx'
  set b : ℕ → ℚ_[p] := fun i => if i < d then a i else 0
  have hsum : ∀ u : PadicAlgCl p, ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (a i) * u ^ i =
      ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (b i) * u ^ i := fun u =>
    Finset.sum_congr rfl fun i hi => by simp only [b, if_pos (Finset.mem_range.1 hi)]
  have hb1 : ∀ i, ‖b i‖ ≤ 1 := by
    intro i
    by_cases hi : i < d
    · simp only [b, if_pos hi]
      refine norm_coeff_le_one hζ hi ?_
      exact (norm_coeff_mul_le_norm_sum hζ a i (Finset.mem_range.2 hi)).trans (ha ▸ hx1)
    · simp [b, if_neg hi]
  rw [hsum] at ha
  have hηn : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp0.ne') hη.pow_eq_one
  have hη1 : ‖η - 1‖ ≤ 1 := norm_sub_one_le_one (pow_ne_zero _ hp0.ne') hη.pow_eq_one
  have hζn : ‖ζ‖ ≤ 1 := by rw [norm_pow, hηn, one_pow]
  set y := ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (b i) * (η - 1) ^ i
  have hy1 : ‖y‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_algebraMap']
    exact mul_le_one₀ (hb1 i) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hη1)
  have hymem : y ∈ cycl p (n + 2) := by
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem (sub_mem ?_ (one_mem _)) _)
    exact pow_eq_one_mem_cycl hη.pow_eq_one
  refine ⟨y, hymem, hy1, ?_⟩

  set O := normInteger (PadicAlgCl p)
  have : Fact (¬IsUnit (p : O)) := ⟨not_isUnit_natCast_normInteger⟩
  set A : ℕ → O := fun i => ⟨algebraMap ℚ_[p] (PadicAlgCl p) (b i),
    mem_normInteger.2 (by rw [norm_algebraMap']; exact hb1 i)⟩
  set H : O := ⟨η, mem_normInteger.2 hηn.le⟩
  set Z : O := ⟨ζ, mem_normInteger.2 hζn⟩
  set X : O := ∑ i ∈ Finset.range d, A i * (Z - 1) ^ i
  set Y : O := ∑ i ∈ Finset.range d, A i * (H - 1) ^ i
  have hX : (X : PadicAlgCl p) = x := by
    rw [ha]; simp [X, A, Z, ζ]
  have hY : (Y : PadicAlgCl p) = y := by simp [Y, y, A, H]
  set mk := Ideal.Quotient.mk (Ideal.span {(p : O)})
  have hA : ∀ i, mk (A i) ^ p = mk (A i) := by
    intro i
    rw [← map_pow]
    refine (mk_eq_mk_iff_norm_sub_le (K := PadicAlgCl p)).2 ?_
    have : ((A i ^ p : O) : PadicAlgCl p) - (A i : PadicAlgCl p) =
        algebraMap ℚ_[p] (PadicAlgCl p) (b i ^ p - b i) := by simp [A]
    rw [this, norm_algebraMap', norm_natCast_prime]
    exact norm_pow_sub_self_le (hb1 i)
  have hH : (mk H - 1) ^ p = mk Z - 1 := by
    rw [sub_pow_char, one_pow, ← map_pow]
    congr 2
  have hmk : mk (Y ^ p) = mk X := by
    simp only [Y, X, map_pow, map_sum, map_mul, map_sub, map_one]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hA, ← pow_mul, mul_comm i p, pow_mul, hH]
  have := (mk_eq_mk_iff_norm_sub_le (K := PadicAlgCl p)).1 hmk.symm
  rw [hX, Subring.coe_pow, hY] at this
  simpa using this

theorem exists_mem_cycl_norm_mem_Ioo {r : ℝ} (hr : r < 1) :
    ∃ n, ∃ x ∈ cycl p n, r < ‖x‖ ∧ ‖x‖ < 1 := by
  have hp1 : (1 : ℝ) < p := one_lt_p_real
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by linarith)
  have hpinv1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1

  obtain ⟨N, hN⟩ : ∃ N : ℕ, max r 0 ^ N < (p : ℝ)⁻¹ := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right r 0) (max_lt hr one_pos)
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpinv)).exists_forall_of_atTop
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (N + 1)
  set d := Nat.totient (p ^ (N + 1))
  have hrd := norm_sub_one_pow_totient hζ
  have hd : N ≤ d := by
    have h1 : d = p ^ N * (p - 1) := Nat.totient_prime_pow_succ (Fact.out : p.Prime) N
    have h2 : N < p ^ N := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have h3 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    rw [h1]; nlinarith
  refine ⟨N + 1, ζ - 1, sub_mem (pow_eq_one_mem_cycl hζ.pow_eq_one) (one_mem _), ?_, ?_⟩
  · have h1 : max r 0 ^ d < ‖ζ - 1‖ ^ d := by
      rw [hrd]
      exact lt_of_le_of_lt (pow_le_pow_of_le_one (le_max_right _ _) (max_lt hr one_pos).le hd) hN
    have hd0 : d ≠ 0 := (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
    exact lt_of_le_of_lt (le_max_left r 0)
      ((pow_lt_pow_iff_left₀ (le_max_right _ _) (norm_nonneg _) hd0).1 h1)
  · by_contra h
    have h1 : 1 ≤ ‖ζ - 1‖ ^ d := one_le_pow₀ (not_lt.1 h)
    rw [hrd] at h1
    linarith

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p

theorem fontaineTheta_map_inclusion {N N' : IntermediateField K♭ C♭} (h : N ≤ N')
    (u : WittVector p (integerTilt K C p N)) :
    θ (WittVector.map (integerTilt K C p N').subtype
        (WittVector.map (Subring.inclusion (integerTilt_mono h)) u)) =
      θ (WittVector.map (integerTilt K C p N).subtype u) := by
  rw [← wittVector_map_comp]
  rfl

theorem coe_untiltAut_of_le {N N' : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    [FiniteDimensional K♭ N'] (h : N ≤ N') (σ : N ≃ₐ[K♭] N) (σ' : N' ≃ₐ[K♭] N')
    (hσ : ∀ y : N, ((σ' ⟨y, h y.2⟩ : N') : C♭) = ((σ y : N) : C♭)) (x : untiltField K C p N) :
    ((untiltAut N' σ' ⟨x, untiltField_mono h x.2⟩ : untiltField K C p N') : C) =
      ((untiltAut N σ x : untiltField K C p N) : C) := by
  set f : untiltField K C p N →ₐ[K] C := (untiltField K C p N').val.comp
    ((untiltAut N' σ').toAlgHom.comp (IntermediateField.inclusion (untiltField_mono h)))
  set g : untiltField K C p N →ₐ[K] C := (untiltField K C p N).val.comp (untiltAut N σ).toAlgHom
  have hfg : f = g := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    show ((untiltAut N' σ' (IntermediateField.inclusion (untiltField_mono h)
        ⟨y, IntermediateField.subset_adjoin _ _ hy⟩) : untiltField K C p N') : C) =
      ((untiltAut N σ ⟨y, IntermediateField.subset_adjoin _ _ hy⟩ : untiltField K C p N) : C)
    generalize IntermediateField.subset_adjoin K _ hy = hy0
    obtain ⟨z, ⟨u, rfl⟩, rfl⟩ := hy
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono h)) u
    have hz : ((RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype) u : normInteger C) : C) =
        ((θ (WittVector.map (integerTilt K C p N').subtype u') : normInteger C) : C) := by
      rw [fontaineTheta_map_inclusion h]; rfl
    have hcoeff : ∀ n, integerTiltHom N' σ'.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N' σ')
        (u'.coeff n) = Subring.inclusion (integerTilt_mono h)
          (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (u.coeff n)) := by
      intro n
      apply Subtype.ext
      apply IsFractionRing.injective 𝒪C♭ C♭
      rw [algebraMap_integerTiltHom]
      change _ = algebraMap 𝒪C♭ C♭ (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (u.coeff n) : 𝒪C♭)
      rw [algebraMap_integerTiltHom]
      exact hσ ⟨algebraMap 𝒪C♭ C♭ (u.coeff n : 𝒪C♭), (u.coeff n).2⟩
    have hmap : WittVector.map (integerTiltHom N' σ'.toAlgHom
        (norm_tiltAlgEquiv_toAlgHom_apply N' σ')) u' =
        WittVector.map (Subring.inclusion (integerTilt_mono h))
          (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u) :=
      WittVector.ext fun n => by
        simp only [WittVector.map_coeff]; exact hcoeff n
    have hmemN : ((θ (WittVector.map (integerTilt K C p N).subtype u) : normInteger C) : C) ∈
        untiltField K C p N := coe_mem_untiltField ⟨u, rfl⟩
    have hmemN' : ((θ (WittVector.map (integerTilt K C p N').subtype u') : normInteger C) : C) ∈
        untiltField K C p N' := coe_mem_untiltField ⟨u', rfl⟩
    have e1 : IntermediateField.inclusion (untiltField_mono h) ⟨_, hy0⟩ =
        (⟨_, hmemN'⟩ : untiltField K C p N') := Subtype.ext hz
    have e2 : (⟨_, hy0⟩ : untiltField K C p N) = ⟨_, hmemN⟩ := rfl
    rw [e1, e2, coe_untiltAut_fontaineTheta, coe_untiltAut_fontaineTheta, hmap,
      fontaineTheta_map_inclusion h]
  exact congrArg (fun φ : untiltField K C p N →ₐ[K] C => φ x) hfg

theorem untiltAut_apply_of_le {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] (h : M ≤ N)
    (σ : N ≃ₐ[K♭] N) (hσ : ∀ y : N, (y : C♭) ∈ M → σ y = y) (x : untiltField K C p M) :
    untiltAut N σ ⟨x, untiltField_mono h x.2⟩ = ⟨x, untiltField_mono h x.2⟩ := by
  set f : untiltField K C p M →ₐ[K] C := (untiltField K C p N).val.comp
    ((untiltAut N σ).toAlgHom.comp (IntermediateField.inclusion (untiltField_mono h)))
  set g : untiltField K C p M →ₐ[K] C := (untiltField K C p M).val
  have hfg : f = g := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    show ((untiltAut N σ (IntermediateField.inclusion (untiltField_mono h)
        ⟨y, IntermediateField.subset_adjoin _ _ hy⟩) : untiltField K C p N) : C) = y
    generalize IntermediateField.subset_adjoin K _ hy = hy0
    obtain ⟨z, ⟨u, rfl⟩, rfl⟩ := hy
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono h)) u
    have hz : ((RingHom.comp θ (WittVector.map (integerTilt K C p M).subtype) u : normInteger C) : C) =
        ((θ (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) := by
      rw [fontaineTheta_map_inclusion h]; rfl
    have hmemN' : ((θ (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) ∈
        untiltField K C p N := coe_mem_untiltField ⟨u', rfl⟩
    have hcoeff : ∀ n, integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)
        (u'.coeff n) = u'.coeff n := by
      intro n
      apply Subtype.ext
      apply IsFractionRing.injective 𝒪C♭ C♭
      rw [algebraMap_integerTiltHom]
      exact congrArg Subtype.val (hσ ⟨algebraMap 𝒪C♭ C♭ (u'.coeff n : 𝒪C♭), (u'.coeff n).2⟩
        (u.coeff n).2)
    have hmap : WittVector.map (integerTiltHom N σ.toAlgHom
        (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u' = u' :=
      WittVector.ext fun n => by rw [WittVector.map_coeff, hcoeff n]
    have e1 : IntermediateField.inclusion (untiltField_mono h) ⟨_, hy0⟩ =
        (⟨_, hmemN'⟩ : untiltField K C p N) := Subtype.ext hz
    rw [e1, coe_untiltAut_fontaineTheta, hmap]
    exact hz.symm
  exact Subtype.ext (congrArg (fun φ : untiltField K C p M →ₐ[K] C => φ x) hfg)

theorem finiteDimensional_of_le_tilt {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    (h : M ≤ N) : FiniteDimensional K♭ M :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem untiltAut_mem_fixingSubgroup_iff (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] {M : IntermediateField K♭ C♭} (h : M ≤ N) (σ : N ≃ₐ[K♭] N) :
    untiltAut N σ ∈ (IntermediateField.restrict (untiltField_mono (K := K) (p := p) h)).fixingSubgroup ↔
      σ ∈ (IntermediateField.restrict h).fixingSubgroup := by
  classical
  have hMfin : FiniteDimensional K♭ M := finiteDimensional_of_le_tilt h
  obtain ⟨hbij, hgal⟩ := untiltAutHom_bijective (K := K) (C := C) (p := p) N
  set M' := IntermediateField.restrict h
  set L' := IntermediateField.restrict (untiltField_mono (K := K) (p := p) h)
  have hJH : ∀ τ ∈ M'.fixingSubgroup, untiltAut N τ ∈ L'.fixingSubgroup := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
    intro x hx
    have hx' : (x : C) ∈ untiltField K C p M := (IntermediateField.mem_restrict _ x).1 hx
    exact untiltAut_apply_of_le h τ
      (fun y hy => hτ y ((IntermediateField.mem_restrict h y).2 hy)) ⟨x, hx'⟩
  refine ⟨fun hσ => ?_, hJH σ⟩

  have hM'fin : Module.finrank K♭ M' = Module.finrank K♭ M :=
    (IntermediateField.restrictAlgEquiv h).toLinearEquiv.finrank_eq.symm
  have hL'fin : Module.finrank K L' = Module.finrank K (untiltField K C p M) :=
    (IntermediateField.restrictAlgEquiv (untiltField_mono (K := K) (p := p) h)).toLinearEquiv.finrank_eq.symm
  have h1 : Module.finrank K♭ M' * Module.finrank M' N = Module.finrank K♭ N :=
    Module.finrank_mul_finrank K♭ M' N
  have h2 : Module.finrank K L' * Module.finrank L' (untiltField K C p N) =
      Module.finrank K (untiltField K C p N) :=
    Module.finrank_mul_finrank K L' (untiltField K C p N)
  rw [finrank_untiltField, hL'fin, finrank_untiltField, ← hM'fin, ← h1] at h2
  have hpos : 0 < Module.finrank K♭ M' := Module.finrank_pos
  have hdeg : Module.finrank L' (untiltField K C p N) = Module.finrank M' N :=
    Nat.eq_of_mul_eq_mul_left hpos h2
  have hcard : Nat.card L'.fixingSubgroup ≤ Nat.card M'.fixingSubgroup := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank, IsGalois.card_fixingSubgroup_eq_finrank, hdeg]
  set φ : M'.fixingSubgroup → L'.fixingSubgroup := fun τ => ⟨untiltAut N τ, hJH τ τ.2⟩
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (hbij.1 (congrArg Subtype.val hab :))
  obtain ⟨τ, hτ⟩ := (hφ.bijective_of_nat_card_le hcard).2 ⟨untiltAut N σ, hσ⟩
  have : (τ : N ≃ₐ[K♭] N) = σ := hbij.1 (congrArg Subtype.val hτ :)
  exact this ▸ τ.2

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem le_algebraicClosure_of_finiteDimensional {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [FiniteDimensional F L] : L ≤ algebraicClosure F E :=
  le_algebraicClosure F E L

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p

variable (K C p) in

def FiniteGaloisTilt : Type _ :=
  {N : IntermediateField K♭ C♭ // FiniteDimensional K♭ N ∧ IsGalois K♭ N}

namespace FiniteGaloisTilt

instance (N : FiniteGaloisTilt K C p) : FiniteDimensional K♭ N.1 := N.2.1
instance (N : FiniteGaloisTilt K C p) : IsGalois K♭ N.1 := N.2.2
instance (N : FiniteGaloisTilt K C p) : IsGalois K (untiltField K C p N.1) :=
  isGalois_untiltField N.1

omit [IsAlgClosed C] in
theorem le_algebraicClosure (N : FiniteGaloisTilt K C p) : N.1 ≤ algebraicClosure K♭ C♭ :=
  le_algebraicClosure_of_finiteDimensional N.1

omit [IsAlgClosed C] in
theorem untiltField_le_algebraicClosure (N : FiniteGaloisTilt K C p) :
    untiltField K C p N.1 ≤ algebraicClosure K C :=
  le_algebraicClosure_of_finiteDimensional _

theorem exists_le (M : IntermediateField K♭ C♭) [FiniteDimensional K♭ M] :
    ∃ N : FiniteGaloisTilt K C p, M ≤ N.1 := by
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  obtain ⟨N, hMN, hN, hgal⟩ := exists_isGalois_le M
  exact ⟨⟨N, hN, hgal⟩, hMN⟩

theorem directed : Directed (· ≤ ·) (fun N : FiniteGaloisTilt K C p => N.1) := fun N₁ N₂ => by
  obtain ⟨N, hN⟩ := exists_le (K := K) (C := C) (p := p) (N₁.1 ⊔ N₂.1)
  exact ⟨N, le_sup_left.trans hN, le_sup_right.trans hN⟩

theorem directed_untiltField :
    Directed (· ≤ ·) (fun N : FiniteGaloisTilt K C p => untiltField K C p N.1) := fun N₁ N₂ => by
  obtain ⟨N, h1, h2⟩ := directed N₁ N₂
  exact ⟨N, untiltField_mono h1, untiltField_mono h2⟩

theorem exists_mem (y : C♭) (hy : y ∈ algebraicClosure K♭ C♭) :
    ∃ N : FiniteGaloisTilt K C p, y ∈ N.1 := by
  have hint : IsIntegral K♭ y := ((mem_algebraicClosure_iff).1 hy).isIntegral
  have : FiniteDimensional K♭ (IntermediateField.adjoin K♭ {y}) := IntermediateField.adjoin.finiteDimensional hint
  obtain ⟨N, hN⟩ := exists_le (K := K) (C := C) (p := p) (IntermediateField.adjoin K♭ {y})
  exact ⟨N, hN (IntermediateField.mem_adjoin_simple_self K♭ y)⟩

theorem exists_mem_untiltField (x : C) (hx : x ∈ algebraicClosure K C) :
    ∃ N : FiniteGaloisTilt K C p, x ∈ untiltField K C p N.1 := by
  have hint : IsIntegral K x := ((mem_algebraicClosure_iff).1 hx).isIntegral
  have : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hint
  obtain ⟨M, hM, hxM⟩ := exists_le_untiltField (p := p) (IntermediateField.adjoin K {x})
  obtain ⟨N, hN⟩ := exists_le (K := K) (C := C) (p := p) M
  exact ⟨N, untiltField_mono hN (hxM (IntermediateField.mem_adjoin_simple_self K x))⟩

end FiniteGaloisTilt

section Equiv

local notation "Ω" => algebraicClosure K C
local notation "Ω♭" => algebraicClosure K♭ C♭

variable (K C p) in

abbrev resTilt (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) : N.1 ≃ₐ[K♭] N.1 :=
  restrictAut Ω♭ τ N.1 N.le_algebraicClosure

omit [IsAlgClosed C] in
theorem resTilt_mul (τ₁ τ₂ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) :
    resTilt K C p (τ₁ * τ₂) N = resTilt K C p τ₁ N * resTilt K C p τ₂ N :=
  restrictAut_mul _ _ _ _ _

omit [IsAlgClosed C] in
theorem coe_untiltAut_resTilt (τ : Ω♭ ≃ₐ[K♭] Ω♭) {N N' : FiniteGaloisTilt K C p} (h : N.1 ≤ N'.1)
    (x : untiltField K C p N.1) :
    ((untiltAut N'.1 (resTilt K C p τ N') ⟨x, untiltField_mono h x.2⟩ : untiltField K C p N'.1) : C) =
      ((untiltAut N.1 (resTilt K C p τ N) x : untiltField K C p N.1) : C) :=
  coe_untiltAut_of_le h _ _ (fun y => by rw [coe_restrictAut, coe_restrictAut]) x

variable (K C p) in

def untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) : Ω ≃ₐ[K] Ω :=
  glueAut Ω (fun N : FiniteGaloisTilt K C p => untiltField K C p N.1)
    (fun N => N.untiltField_le_algebraicClosure) FiniteGaloisTilt.directed_untiltField
    (fun x hx => FiniteGaloisTilt.exists_mem_untiltField x hx)
    (fun N => (untiltAut N.1 (resTilt K C p τ N)).toAlgHom)
    (fun N N' h x => by
      obtain ⟨N'', h1, h2⟩ := FiniteGaloisTilt.directed N N'
      exact (coe_untiltAut_resTilt τ h2 ⟨x, h x.2⟩).symm.trans (coe_untiltAut_resTilt τ h1 x))

theorem coe_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) (x : Ω)
    (hx : (x : C) ∈ untiltField K C p N.1) :
    ((untiltGalFun K C p τ x : Ω) : C) =
      ((untiltAut N.1 (resTilt K C p τ N) ⟨x, hx⟩ : untiltField K C p N.1) : C) :=
  coe_glueAut _ _ _ _ _ _ _ N x hx

variable (K C p) in

def tiltGalAlt (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) : N.1 ≃ₐ[K♭] N.1 :=
  (MulEquiv.ofBijective (untiltAutHom (K := K) (C := C) (p := p) N.1)
    (untiltAutHom_bijective N.1).1).symm
    (restrictAut Ω ρ (untiltField K C p N.1) N.untiltField_le_algebraicClosure)

omit [IsAlgClosed C] in
theorem untiltAut_tiltGal (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) :
    untiltAut N.1 (tiltGalAlt K C p ρ N) =
      restrictAut Ω ρ (untiltField K C p N.1) N.untiltField_le_algebraicClosure :=
  (MulEquiv.ofBijective (untiltAutHom (K := K) (C := C) (p := p) N.1)
    (untiltAutHom_bijective N.1).1).apply_symm_apply _

omit [IsAlgClosed C] in
theorem coe_tiltGal_of_le (ρ : Ω ≃ₐ[K] Ω) {N N' : FiniteGaloisTilt K C p} (h : N.1 ≤ N'.1)
    (y : N.1) : ((tiltGalAlt K C p ρ N' ⟨y, h y.2⟩ : N'.1) : C♭) = ((tiltGalAlt K C p ρ N y : N.1) : C♭) := by
  set σ'' := restrictAut N'.1 (tiltGalAlt K C p ρ N') N.1 h
  have hσ'' : untiltAut N.1 σ'' = untiltAut N.1 (tiltGalAlt K C p ρ N) := by
    rw [untiltAut_tiltGal]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [← coe_untiltAut_of_le h σ'' (tiltGalAlt K C p ρ N')
      (fun y => (coe_restrictAut _ _ _ h y).symm) x, untiltAut_tiltGal, coe_restrictAut,
      coe_restrictAut]
  have := (untiltAutHom_bijective (K := K) (C := C) (p := p) N.1).1.1 hσ''
  rw [← this, coe_restrictAut]

variable (K C p) in

def tiltGalFun (ρ : Ω ≃ₐ[K] Ω) : Ω♭ ≃ₐ[K♭] Ω♭ :=
  glueAut Ω♭ (fun N : FiniteGaloisTilt K C p => N.1) (fun N => N.le_algebraicClosure)
    FiniteGaloisTilt.directed (fun y hy => FiniteGaloisTilt.exists_mem y hy)
    (fun N => (tiltGalAlt K C p ρ N).toAlgHom) (fun _ _ h y => coe_tiltGal_of_le ρ h y)

theorem coe_tiltGalFun (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) (y : Ω♭) (hy : (y : C♭) ∈ N.1) :
    ((tiltGalFun K C p ρ y : Ω♭) : C♭) = ((tiltGalAlt K C p ρ N ⟨y, hy⟩ : N.1) : C♭) :=
  coe_glueAut _ _ _ _ _ _ _ N y hy

theorem resTilt_tiltGalFun (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) :
    resTilt K C p (tiltGalFun K C p ρ) N = tiltGalAlt K C p ρ N :=
  AlgEquiv.ext fun y => Subtype.ext (by
    rw [coe_restrictAut]
    exact coe_tiltGalFun ρ N _ y.2)

theorem restrictAut_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) :
    restrictAut Ω (untiltGalFun K C p τ) (untiltField K C p N.1) N.untiltField_le_algebraicClosure =
      untiltAut N.1 (resTilt K C p τ N) :=
  AlgEquiv.ext fun x => Subtype.ext (by
    rw [coe_restrictAut]
    exact coe_untiltGalFun τ N _ x.2)

theorem tiltGal_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) :
    tiltGalAlt K C p (untiltGalFun K C p τ) N = resTilt K C p τ N := by
  apply (untiltAutHom_bijective (K := K) (C := C) (p := p) N.1).1.1
  change untiltAut _ _ = untiltAut _ _
  rw [untiltAut_tiltGal, restrictAut_untiltGalFun]

theorem tiltGalFun_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) : tiltGalFun K C p (untiltGalFun K C p τ) = τ := by
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  obtain ⟨N, hN⟩ := FiniteGaloisTilt.exists_mem (K := K) (C := C) (p := p) y y.2
  rw [coe_tiltGalFun _ N y hN, tiltGal_untiltGalFun, coe_restrictAut]

theorem untiltGalFun_tiltGalFun (ρ : Ω ≃ₐ[K] Ω) : untiltGalFun K C p (tiltGalFun K C p ρ) = ρ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨N, hN⟩ := FiniteGaloisTilt.exists_mem_untiltField (K := K) (C := C) (p := p) x x.2
  rw [coe_untiltGalFun _ N x hN, resTilt_tiltGalFun, untiltAut_tiltGal, coe_restrictAut]

theorem untiltGalFun_mul (τ₁ τ₂ : Ω♭ ≃ₐ[K♭] Ω♭) :
    untiltGalFun K C p (τ₁ * τ₂) = untiltGalFun K C p τ₁ * untiltGalFun K C p τ₂ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨N, hN⟩ := FiniteGaloisTilt.exists_mem_untiltField (K := K) (C := C) (p := p) x x.2
  have hmem : ((untiltGalFun K C p τ₂ x : Ω) : C) ∈ untiltField K C p N.1 := by
    rw [coe_untiltGalFun τ₂ N x hN]; exact Subtype.prop _
  have he : (⟨((untiltGalFun K C p τ₂ x : Ω) : C), hmem⟩ : untiltField K C p N.1) =
      untiltAut N.1 (resTilt K C p τ₂ N) ⟨x, hN⟩ := Subtype.ext (coe_untiltGalFun τ₂ N x hN)
  rw [AlgEquiv.mul_apply, coe_untiltGalFun τ₁ N _ hmem, he, coe_untiltGalFun _ N x hN,
    resTilt_mul, untiltAut_mul, AlgEquiv.mul_apply]

variable (K C p) in

def untiltGalEquiv : (Ω♭ ≃ₐ[K♭] Ω♭) ≃* (Ω ≃ₐ[K] Ω) where
  toFun := untiltGalFun K C p
  invFun := tiltGalFun K C p
  left_inv := tiltGalFun_untiltGalFun
  right_inv := untiltGalFun_tiltGalFun
  map_mul' := untiltGalFun_mul

theorem untiltGalEquiv_apply (τ : Ω♭ ≃ₐ[K♭] Ω♭) : untiltGalEquiv K C p τ = untiltGalFun K C p τ :=
  rfl

theorem untiltGalEquiv_fixes_iff (τ : Ω♭ ≃ₐ[K♭] Ω♭) (M : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ M] :
    (∀ x : Ω, (x : C) ∈ untiltField K C p M → untiltGalEquiv K C p τ x = x) ↔
      (∀ y : Ω♭, (y : C♭) ∈ M → τ y = y) := by
  obtain ⟨N, hMN⟩ := FiniteGaloisTilt.exists_le (K := K) (C := C) (p := p) M
  have key := untiltAut_mem_fixingSubgroup_iff N.1 hMN (resTilt K C p τ N)
  constructor
  · intro hΨ
    have h1 : untiltAut N.1 (resTilt K C p τ N) ∈
        (IntermediateField.restrict (untiltField_mono (K := K) (p := p) hMN)).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      have := hΨ ⟨x, N.untiltField_le_algebraicClosure x.2⟩ ((IntermediateField.mem_restrict _ x).1 hx)
      rw [untiltGalEquiv_apply] at this
      have e := coe_untiltGalFun τ N ⟨(x : C), N.untiltField_le_algebraicClosure x.2⟩ x.2
      exact e.symm.trans (congrArg Subtype.val this)
    have h2 := key.1 h1
    rw [IntermediateField.mem_fixingSubgroup_iff] at h2
    intro y hy
    apply Subtype.ext
    have := congrArg Subtype.val (h2 ⟨y, hMN hy⟩ ((IntermediateField.mem_restrict hMN _).2 hy))
    rw [coe_restrictAut] at this
    exact this
  · intro hτ
    have h2 : resTilt K C p τ N ∈ (IntermediateField.restrict hMN).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      apply Subtype.ext
      rw [coe_restrictAut]
      exact congrArg Subtype.val (hτ _ ((IntermediateField.mem_restrict hMN y).1 hy))
    have h1 := key.2 h2
    rw [IntermediateField.mem_fixingSubgroup_iff] at h1
    intro x hx
    have hxN := untiltField_mono (K := K) (p := p) hMN hx
    rw [untiltGalEquiv_apply]
    apply Subtype.ext
    rw [coe_untiltGalFun τ N x hxN]
    exact congrArg Subtype.val (h1 ⟨x, hxN⟩ ((IntermediateField.mem_restrict _ _).2 hx))

theorem continuous_untiltGalEquiv : Continuous (untiltGalEquiv K C p) := by
  apply continuous_of_continuousAt_one (untiltGalEquiv K C p) (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  have : FiniteDimensional K (IntermediateField.lift E) :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv E).toLinearEquiv
  obtain ⟨M, hM, hEM⟩ := exists_le_untiltField (p := p) (IntermediateField.lift E)
  refine ⟨IntermediateField.restrict (le_algebraicClosure_of_finiteDimensional M),
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv _).toLinearEquiv, ?_⟩
  intro τ hτ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ
  apply hsub
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (untiltGalEquiv_fixes_iff τ M).2
    (fun y hy => hτ y ((IntermediateField.mem_restrict _ y).2 hy)) x
    (hEM ((IntermediateField.mem_lift x).2 hx))

theorem continuous_untiltGalEquiv_symm : Continuous (untiltGalEquiv K C p).symm := by
  apply continuous_of_continuousAt_one (untiltGalEquiv K C p).symm (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  have : FiniteDimensional K♭ (IntermediateField.lift E) :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv E).toLinearEquiv
  refine ⟨IntermediateField.restrict
    (le_algebraicClosure_of_finiteDimensional (untiltField K C p (IntermediateField.lift E))),
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv _).toLinearEquiv, ?_⟩
  intro ρ hρ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hρ
  apply hsub
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  have hfix := (untiltGalEquiv_fixes_iff ((untiltGalEquiv K C p).symm ρ)
    (IntermediateField.lift E)).1 (fun x hx => by
      rw [MulEquiv.apply_symm_apply]
      exact hρ x ((IntermediateField.mem_restrict _ x).2 hx))
  intro y hy
  exact hfix y ((IntermediateField.mem_lift y).2 hy)

variable (K C p) in

def untiltGalHomeomorph : (Ω♭ ≃ₐ[K♭] Ω♭) ≃ₜ* (Ω ≃ₐ[K] Ω) where
  toMulEquiv := untiltGalEquiv K C p
  continuous_toFun := continuous_untiltGalEquiv
  continuous_invFun := continuous_untiltGalEquiv_symm

end Equiv

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Congr

theorem algEquiv_apply_eq_of_mem_adjoin {F M : Type*} [Field F] [Field M] [Algebra F M]
    (τ : M ≃ₐ[F] M) {S : Set M} (hS : ∀ s ∈ S, τ s = s) {x : M}
    (hx : x ∈ IntermediateField.adjoin F S) : τ x = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap c => exact τ.commutes c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem exists_finite_le_adjoin {F M : Type*} [Field F] [Field M] [Algebra F M]
    (W : IntermediateField F M) [FiniteDimensional F W] :
    ∃ S : Set M, S.Finite ∧ W ≤ IntermediateField.adjoin F S := by
  classical
  set B := Module.finBasis F W
  refine ⟨Set.range fun i => (B i : M), Set.finite_range _, fun x hx => ?_⟩
  have := congrArg (fun u : W => (u : M)) (B.sum_repr (⟨x, hx⟩ : W))
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
  rw [← this]
  exact sum_mem fun i _ => IntermediateField.smul_mem _
    (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))

variable {F F' : Type*} [Field F] [Field F']

def conjAlgEquiv {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M] (e : F ≃+* F')
    (E : L ≃+* M) (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) (σ : L ≃ₐ[F] L) :
    M ≃ₐ[F'] M :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans (σ.toRingEquiv.trans E)) fun c => by
    have h1 : E.symm (algebraMap F' M c) = algebraMap F L (e.symm c) := by
      rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
    rw [h1, AlgEquiv.commutes, hE, RingEquiv.apply_symm_apply]

theorem conjAlgEquiv_apply {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    (e : F ≃+* F') (E : L ≃+* M) (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c))
    (σ : L ≃ₐ[F] L) (x : M) : conjAlgEquiv e E hE σ x = E (σ (E.symm x)) :=
  rfl

theorem continuous_conjAlgEquiv {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    [Algebra.IsIntegral F L] (e : F ≃+* F') (E : L ≃+* M)
    (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) :
    Continuous (conjAlgEquiv e E hE) := by
  have hmul : ∀ σ τ : L ≃ₐ[F] L,
      conjAlgEquiv e E hE (σ * τ) = conjAlgEquiv e E hE σ * conjAlgEquiv e E hE τ := fun σ τ =>
    AlgEquiv.ext fun x => by simp [conjAlgEquiv_apply]
  let φ : (L ≃ₐ[F] L) →* (M ≃ₐ[F'] M) :=
    { toFun := conjAlgEquiv e E hE
      map_one' := AlgEquiv.ext fun x => by simp [conjAlgEquiv_apply]
      map_mul' := hmul }
  change Continuous φ
  apply continuous_of_continuousAt_one φ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨W, hW, hsub⟩ := hU
  obtain ⟨S, hSfin, hWS⟩ := exists_finite_le_adjoin W
  rw [krullTopology_mem_nhds_one_iff]
  have : Finite (E.symm '' S) := (hSfin.image _).to_subtype
  have : FiniteDimensional F (IntermediateField.adjoin F (E.symm '' S)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨IntermediateField.adjoin F (E.symm '' S), this, fun σ hσ => hsub ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  refine algEquiv_apply_eq_of_mem_adjoin (φ σ) (fun s hs => ?_) (hWS hx)
  change E (σ (E.symm s)) = s
  rw [hσ _ (IntermediateField.subset_adjoin _ _ ⟨s, hs, rfl⟩), RingEquiv.apply_symm_apply]

def conjHomeomorph {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    [Algebra.IsIntegral F L] [Algebra.IsIntegral F' M] (e : F ≃+* F') (E : L ≃+* M)
    (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) : (L ≃ₐ[F] L) ≃ₜ* (M ≃ₐ[F'] M) :=
  have hE' : ∀ c, E.symm (algebraMap F' M c) = algebraMap F L (e.symm c) := fun c => by
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  { toFun := conjAlgEquiv e E hE
    invFun := conjAlgEquiv e.symm E.symm hE'
    left_inv := fun σ => AlgEquiv.ext fun x => by
      rw [conjAlgEquiv_apply, conjAlgEquiv_apply, RingEquiv.symm_symm, RingEquiv.symm_apply_apply,
        RingEquiv.symm_apply_apply]
    right_inv := fun τ => AlgEquiv.ext fun x => by
      rw [conjAlgEquiv_apply, conjAlgEquiv_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply]
    map_mul' := fun σ τ => AlgEquiv.ext fun x => by
      simp only [conjAlgEquiv_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]
    continuous_toFun := continuous_conjAlgEquiv e E hE
    continuous_invFun := continuous_conjAlgEquiv e.symm E.symm hE' }

variable (F F') in

def absoluteGaloisGroupCongr (e : F ≃+* F') :
    Field.absoluteGaloisGroup F ≃ₜ* Field.absoluteGaloisGroup F' :=
  conjHomeomorph e (IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure F') e)
    (IsAlgClosure.equivOfEquiv_algebraMap _ _ e)

end Congr

section CharP

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝒪♭" => PreTilt (normInteger K) p

variable (K p) in

def untiltRingHomOfCharP : 𝒪♭ →+* normInteger K where
  toFun x := PreTilt.untilt x
  map_one' := map_one _
  map_mul' := untilt_mul
  map_zero' := untilt_zero
  map_add' := untilt_add_of_natCast_eq_zero (CharP.cast_eq_zero K p)

theorem untiltRingHomOfCharP_bijective : Function.Bijective (untiltRingHomOfCharP K p) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    exact untilt_eq_zero_iff.1 (congrArg Subtype.val hx)
  · intro a
    obtain ⟨x, hx⟩ := exists_mk_untilt_eq (p := p) a
    refine ⟨x, ?_⟩
    have hp : (p : normInteger K) = 0 := Subtype.ext (by simp)
    rw [Ideal.Quotient.eq, hp, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot, sub_eq_zero] at hx
    exact hx

variable (K p) in

def tiltRingEquivOfCharP : K♭ ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv (A := 𝒪♭) (K := K♭) (B := normInteger K) (L := K)
    (RingEquiv.ofBijective _ untiltRingHomOfCharP_bijective)

end CharP

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosed E] in

def absoluteGaloisGroupEquivAlgebraicClosure :
    Field.absoluteGaloisGroup F ≃ₜ* (algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :=
  autCongrHomeomorph (IsAlgClosure.equiv F (AlgebraicClosure F) (algebraicClosure F E))

section InC

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "Ω" => algebraicClosure K C
local notation "Ω♭" => algebraicClosure K♭ C♭

variable (C) in
include C in

theorem isAlgClosed_iff_isAlgClosed_tilt_of_isAlgClosed : IsAlgClosed K ↔ IsAlgClosed K♭ := by
  constructor
  · intro _
    infer_instance
  · intro _
    refine IsAlgClosed.of_exists_root K fun f hmon hirr => ?_
    have hdeg : f.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero C f hdeg
    have hint : IsIntegral K z := ⟨f, hmon, by rwa [← Polynomial.aeval_def]⟩
    have : FiniteDimensional K (IntermediateField.adjoin K {z}) :=
      IntermediateField.adjoin.finiteDimensional hint
    obtain ⟨hfin, -⟩ := untiltField_tiltIntermediateField (p := p) (IntermediateField.adjoin K {z})
    have h1 : tiltIntermediateField p (IntermediateField.adjoin K {z}) = ⊥ :=
      IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have h2 : Module.finrank K (IntermediateField.adjoin K {z}) = 1 := by
      rw [← finrank_tiltIntermediateField (p := p), h1, IntermediateField.finrank_bot]
    have h3 := IntermediateField.finrank_eq_one_iff.1 h2
    have hzb : z ∈ (⊥ : IntermediateField K C) := h3 ▸ IntermediateField.mem_adjoin_simple_self K z
    obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.1 hzb
    refine ⟨k, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply] at hz
    have := (algebraMap K C).injective (hz.trans (map_zero _).symm)
    rwa [Polynomial.coe_aeval_eq_eval] at this

variable (K C p) in

def galoisTiltEquiv : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω♭ ≃ₐ[K♭] Ω♭) :=
  (untiltGalHomeomorph K C p).symm



end InC

section Absolute

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p


variable (K p) in

def absoluteGaloisGroupTiltEquiv [CharZero K] :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup K♭ :=
  haveI := IsPerfectoidField.completeSpace (K := K) p
  haveI : IsPerfectoidField (CompletedAlgClosure K) p :=
    isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
  (absoluteGaloisGroupEquivAlgebraicClosure K (CompletedAlgClosure K)).trans
    ((galoisTiltEquiv K (CompletedAlgClosure K) p).trans
      (absoluteGaloisGroupEquivAlgebraicClosure K♭ (Tilt (CompletedAlgClosure K) NormedField.valuation
          (normInteger (CompletedAlgClosure K)) normInteger_integers p)).symm)

variable (K p) in

def absoluteGaloisGroupTiltEquivOfCharP [CharP K p] :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup K♭ :=
  absoluteGaloisGroupCongr K K♭ (tiltRingEquivOfCharP K p).symm


end Absolute

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable (p : ℕ) [Fact p.Prime]

def cyclInf : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n, cycl p n

theorem mem_cyclInf_iff {x : PadicAlgCl p} : x ∈ cyclInf p ↔ ∃ n, x ∈ cycl p n := by
  have hdir : Directed (· ≤ ·) (cycl p) := (cycl_mono (p := p)).directed_le
  rw [← SetLike.mem_coe, cyclInf, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion]
  rfl

def cyclComplete : Subfield ℂ_[p] :=
  ((cyclInf p).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])).topologicalClosure

theorem coe_mem_cyclComplete {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cycl p n) :
    (x : ℂ_[p]) ∈ cyclComplete p :=
  Subfield.le_topologicalClosure _ ⟨x, (mem_cyclInf_iff p).2 ⟨n, hx⟩, rfl⟩

theorem isClosed_cyclComplete : IsClosed (cyclComplete p : Set ℂ_[p]) :=
  Subfield.isClosed_topologicalClosure _

instance : CompleteSpace (cyclComplete p) := (isClosed_cyclComplete p).completeSpace_coe

theorem norm_natCast_cyclComplete : ‖(p : cyclComplete p)‖ = (p : ℝ)⁻¹ := by
  change ‖((p : cyclComplete p) : ℂ_[p])‖ = _
  rw [show ((p : cyclComplete p) : ℂ_[p]) = ((p : PadicAlgCl p) : ℂ_[p]) by simp,
    PadicComplex.norm_extends, norm_natCast_prime]

instance : NontriviallyNormedField (cyclComplete p) where
  non_trivial := ⟨(p : cyclComplete p)⁻¹, by
    rw [norm_inv, norm_natCast_cyclComplete, inv_inv]; exact one_lt_p_real⟩

instance isPerfectoidField_cyclComplete : IsPerfectoidField (cyclComplete p) p where
  complete := inferInstance
  norm_natCast_lt_one := by
    rw [norm_natCast_cyclComplete]; exact inv_lt_one_of_one_lt₀ one_lt_p_real
  exists_norm_mem_Ioo r hr := by
    obtain ⟨n, x, hx, h1, h2⟩ := exists_mem_cycl_norm_mem_Ioo (p := p) hr
    have hn : ‖(⟨(x : ℂ_[p]), coe_mem_cyclComplete p hx⟩ : cyclComplete p)‖ = ‖x‖ :=
      PadicComplex.norm_extends p x
    exact ⟨⟨x, coe_mem_cyclComplete p hx⟩, hn ▸ h1, hn ▸ h2⟩
  surjective_pow := by
    refine IsPerfectoidField.surjective_pow_of_norm p fun x hx1 => ?_
    have hx1' : ‖(x : ℂ_[p])‖ ≤ 1 := hx1
    have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)
    obtain ⟨b, ⟨u, hu, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 x.2 _ hpinv
    obtain ⟨n, hun⟩ := (mem_cyclInf_iff p).1 hu
    have hdist : ‖(x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] u‖ < (p : ℝ)⁻¹ := by
      rw [← dist_eq_norm]; exact hb
    have hu1 : ‖u‖ ≤ 1 := by
      rw [← PadicComplex.norm_extends p u]
      have h := IsUltrametricDist.norm_add_le_max (x : ℂ_[p])
        (algebraMap (PadicAlgCl p) ℂ_[p] u - x)
      rw [add_sub_cancel] at h
      refine h.trans (max_le hx1' ?_)
      rw [norm_sub_rev]
      exact hdist.le.trans (inv_lt_one_of_one_lt₀ one_lt_p_real).le
    obtain ⟨v, hv, hv1, hvu⟩ := exists_pow_approx_cycl hun hu1
    refine ⟨⟨(v : ℂ_[p]), coe_mem_cyclComplete p hv⟩, ?_, ?_⟩
    · exact (PadicComplex.norm_extends p v).trans_le hv1
    · rw [norm_natCast_cyclComplete]
      change ‖(x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] v ^ p‖ ≤ _
      have hsplit : (x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] v ^ p =
          ((x : ℂ_[p]) - algebraMap (PadicAlgCl p) ℂ_[p] u) +
            algebraMap (PadicAlgCl p) ℂ_[p] (u - v ^ p) := by
        rw [map_sub, map_pow]; ring
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hdist.le ?_)
      rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, ← norm_natCast_prime]
      exact hvu

instance : CharZero (cyclComplete p) :=
  (RingHom.charZero_iff (cyclComplete p).subtype.injective).2 inferInstance

instance : NormedAlgebra (cyclComplete p) ℂ_[p] where
  norm_smul_le k x := by rw [Algebra.smul_def, norm_mul]; rfl

local notation "K∞" => cyclComplete p
local notation "K∞♭" => Tilt (cyclComplete p) NormedField.valuation (normInteger (cyclComplete p))
  normInteger_integers p

def cyclGaloisTiltEquiv :
    (algebraicClosure K∞ ℂ_[p] ≃ₐ[K∞] algebraicClosure K∞ ℂ_[p]) ≃ₜ*
      (algebraicClosure K∞♭ (Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p) ≃ₐ[K∞♭]
        algebraicClosure K∞♭ (Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p)) :=
  galoisTiltEquiv K∞ ℂ_[p] p


end GroundTheory.PAdicHodge
end
end
