import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeAutomorphismLcm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLeSuccOfDvdMinkM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntSmulMem
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RationalRankMinkowski
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ObjOnNarrowOfObjectsExist

section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.DGamCoprime

theorem two_f_N_le (R : Ranks) (h : R.f * R.m ≤ R.k) : 2 * R.f * R.N R.m ≤ 4 * R.t * R.r := by
  have h1 : R.f ≤ R.k := R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.rank_add_five_le
  have h4 : R.k ≤ R.r := by unfold Ranks.r; omega
  have h5 : R.k + 1 ≤ R.t := by omega
  unfold Ranks.N
  have e : 2 * R.f * (R.k + R.m * (R.t + 1)) = 2 * (R.f * R.k) + 2 * ((R.f * R.m) * (R.t + 1)) := by ring
  have a1 : R.f * R.k ≤ R.k * R.k := Nat.mul_le_mul_right _ h1
  have a2 : (R.f * R.m) * (R.t + 1) ≤ R.k * (R.t + 1) := Nat.mul_le_mul_right _ h
  have a3 : R.k * (R.k + 1) ≤ R.k * R.t := Nat.mul_le_mul_left _ h5
  have a4 : R.t * R.k ≤ R.t * R.r := Nat.mul_le_mul_left _ h4
  rw [e]
  nlinarith

variable {D : D7} (L : SizeData₂ D)

theorem one_le_L : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b : 1 ≤ L.sc.b := Real.one_le_exp (by linarith [one_le_L L])

theorem f_mul_m_le (h : SizeKRel L) : D.R.f * D.R.m ≤ D.R.k := by
  have h1 := h.1
  have hx := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have a1 : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx (by unfold szTh; positivity)
  have a2 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx he.le
  have a3 := one_le_L L
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) D.R.two_le_m)
  have a4 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 := le_self_pow₀ hm (by norm_num)
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have key : (1 : ℝ) * D.R.m * D.R.f * 1 * 1 ≤
      L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps := by
    gcongr
  have : ((D.R.f * D.R.m : ℕ) : ℝ) ≤ D.R.k := by push_cast; linarith
  exact_mod_cast this

theorem q_le_sqrt_b (h : SizeCond L) (hd : 0 < D.host.d) (hq : 0 < D.host.q) :
    (D.host.q : ℝ) ≤ Real.sqrt L.sc.b := by
  unfold SizeCond at h
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hq' : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have ht : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (show 1 ≤ D.R.t by omega)
  have c1 : (D.host.q : ℝ) ≤ szCond L := by
    unfold szCond
    calc (D.host.q : ℝ) = 1 * D.host.q * 1 := by ring
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr; exact_mod_cast D.host.QS_pos
  have c2 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ (hq'.trans c1) (by norm_num)
  have c3 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
  have c4 : 0 ≤ szCond L ^ 36 := by linarith
  nlinarith

theorem primes_gt (hS : SizesAt L) (hT : L.TuGe) :
    (∀ u, 2 * D.R.f * D.R.N D.R.m + 1 < (D.mem u).A.T) ∧
    (∀ a, 2 * D.R.f * D.R.N D.R.m + 1 < D.host.g a) ∧
    2 * D.R.f * D.R.N D.R.m + 1 < D.host.q ∧ 2 * D.R.f * D.R.N D.R.m + 1 < D.host.d := by
  obtain ⟨-, -, -, hK, -, hC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have h0 := two_f_N_le D.R (f_mul_m_le L hK)
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hq' : 2 * D.R.f * D.R.N D.R.m + 1 < D.host.q := by omega
  have hd' : 2 * D.R.f * D.R.N D.R.m + 1 < D.host.d := by omega
  have hs := q_le_sqrt_b L hC (by omega) (by omega)
  have hb := one_le_b L
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hqb : (D.host.q : ℝ) ≤ L.sc.b := hs.trans hsb
  refine ⟨fun u => ?_, fun a => ?_, hq', hd'⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have h1 : L.sc.b ^ (1 : ℝ) ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    rw [Real.rpow_one] at h1
    have : (D.host.q : ℝ) ≤ ((D.mem u).A.T : ℝ) := hqb.trans (h1.trans (hT u))
    have : D.host.q ≤ (D.mem u).A.T := by exact_mod_cast this
    omega
  · have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have h1 : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h2 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ (hb.trans h1) (by norm_num)
    have : (D.host.q : ℝ) ≤ (D.host.g a : ℝ) := hqb.trans (h1.trans (h2.trans (hG a a).1))
    have : D.host.q ≤ D.host.g a := by exact_mod_cast this
    omega

end GlobalTheory.DGamCoprime
end

section
namespace GlobalTheory.MinkowskiExact

open Polynomial

theorem card_dvd_sum_trace {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) : (Fintype.card H : ℤ) ∣ ∑ g, (ρ g).trace := by
  let σ : H →* Matrix ι ι ℚ := (Int.castRingHom ℚ).mapMatrix.toMonoidHom.comp ρ
  have hc : (Fintype.card H : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∀ h, σ h * ∑ g, σ g = ∑ g, σ g := by
    intro h
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => (map_mul σ h g).symm
  have h2 : (∑ g, σ g) * ∑ g, σ g = (Fintype.card H : ℚ) • ∑ g, σ g := by
    rw [Finset.sum_mul, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  let e : Matrix ι ι ℚ := (Fintype.card H : ℚ)⁻¹ • ∑ g, σ g
  have he : e * e = e := by
    simp only [e]
    rw [smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hi : IsIdempotentElem (Matrix.toLin' e) := by
    change Matrix.toLin' e ∘ₗ Matrix.toLin' e = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [Matrix.trace_toLin'_eq] at ht
  refine ⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' e)), ?_⟩
  have h3 : ∀ g, (σ g).trace = ((ρ g).trace : ℚ) := by
    intro g
    simp [σ, Matrix.trace]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [← ht]
  simp only [e]
  rw [Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun g _ => (h3 g).symm

theorem card_dvd_sum_trace_pow {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) (j : ℕ) : (Fintype.card H : ℤ) ∣ ∑ g, (ρ g).trace ^ j := by
  let τ : H →* Matrix (Fin j → ι) (Fin j → ι) ℤ :=
    { toFun := fun g => Matrix.of fun a b => ∏ i, ρ g (a i) (b i)
      map_one' := by
        ext a b
        simp only [map_one, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      map_mul' := fun g h => by
        ext a b
        simp only [map_mul, Matrix.of_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib }
  have h := card_dvd_sum_trace τ
  convert h using 2 with g
  rw [Matrix.trace, Fintype.sum_pow]
  rfl

theorem card_dvd_sum_eval {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) (f : ℤ[X]) : (Fintype.card H : ℤ) ∣ ∑ g, f.eval (ρ g).trace := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, Finset.sum_add_distrib]
    exact dvd_add hp hq
  | monomial j a =>
    simp only [eval_monomial, ← Finset.mul_sum]
    exact Dvd.dvd.mul_left (card_dvd_sum_trace_pow ρ j) a

theorem norm_root {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1)
    {z : ℂ} (hz : z ∈ A.charpoly.roots) : ‖z‖ = 1 := by
  have h1 : z ∈ spectrum ℂ A :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hz)
  haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    rw [spectrum.of_subsingleton] at h1
    exact h1
  have h2 := spectrum.pow_mem_pow A m h1
  rw [h, spectrum.one_eq, Set.mem_singleton_iff] at h2
  exact Complex.norm_eq_one_of_pow_eq_one h2 hm

theorem card_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Multiset.card A.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem norm_trace_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1) :
    ‖A.trace‖ ≤ n := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_congr rfl fun z hz => norm_root A hm h hz]
  simp [card_roots]

theorem eq_one_of_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1)
    (ht : A.trace = n) : A = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  rw [Matrix.trace_eq_sum_roots_charpoly] at ht
  have hre : ∀ z ∈ A.charpoly.roots, z.re ≤ 1 := fun z hz =>
    (Complex.re_le_norm z).trans (norm_root A hm h hz).le
  have hs : (A.charpoly.roots.map fun z => 1 - z.re).sum = 0 := by
    have := congrArg Complex.re ht
    rw [Multiset.sum_map_sub]
    have h2 := map_multiset_sum Complex.reAddGroupHom A.charpoly.roots
    simp only [Complex.coe_reAddGroupHom] at h2
    rw [h2] at this
    simp [card_roots, this]
  have h1 : ∀ z ∈ A.charpoly.roots, z = 1 := by
    intro z hz
    have h0 : 1 - z.re = 0 := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero (by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      linarith [hre w hw]) hs _ (Multiset.mem_map_of_mem _ hz)
    have h3 := norm_root A hm h hz
    have h4 : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h3]; norm_num
    have h5 : z.re = 1 := by linarith
    rw [h5] at h4
    apply Complex.ext
    · simpa using h5
    · simpa using h4
  have hch : A.charpoly = (X - C 1) ^ n := by
    rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic,
      Multiset.eq_replicate.2 ⟨card_roots A, h1⟩]
    simp
  have hsq : Squarefree (minpoly ℂ A) := by
    have hsep : (X ^ m - C 1 : ℂ[X]).Separable :=
      separable_X_pow_sub_C 1 (by exact_mod_cast hm) one_ne_zero
    refine hsep.squarefree.squarefree_of_dvd (minpoly.dvd ℂ A ?_)
    simp [h]
  have hd : minpoly ℂ A ∣ X - C 1 := by
    rw [← hsq.dvd_pow_iff_dvd hn.ne', ← hch]
    exact A.minpoly_dvd_charpoly
  have := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval ℂ A)
  simpa [sub_eq_zero] using this

theorem two_dvd_sub_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {k : ℕ} (h : A ^ 2 ^ k = 1) :
    (2 : ℤ) ∣ n - A.trace := by
  have key : ∀ (k : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2)), (B ^ 2 ^ k).trace = B.trace := by
    intro k B
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ZMod.trace_pow_card, ZMod.pow_card, ih]
  have h1 := key k ((Int.castRingHom (ZMod 2)).mapMatrix A)
  rw [← map_pow, h, map_one, Matrix.trace_one, Fintype.card_fin] at h1
  have h2 : (((n : ℤ) - A.trace : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [h1]
    simp [Matrix.trace]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h2

theorem card_two_group_dvd {H : Type} [Group H] [Fintype H] {n k : ℕ} (ρ : H →* Matrix (Fin n) (Fin n) ℤ)
    (hρ : ∀ g, ρ g = 1 → g = 1) (hk : Fintype.card H = 2 ^ k) : 2 ^ k ∣ 2 ^ n * n.factorial := by
  classical
  have h := card_dvd_sum_eval ρ (∏ i ∈ Finset.range n, (X - C ((n : ℤ) - 2 * (i + 1))))
  rw [Finset.sum_eq_single (1 : H)] at h
  · rw [hk, map_one, Matrix.trace_one, Fintype.card_fin, eval_prod] at h
    have e : ∏ i ∈ Finset.range n, eval (n : ℤ) (X - C ((n : ℤ) - 2 * (i + 1)))
        = ((2 ^ n * n.factorial : ℕ) : ℤ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      rw [← Finset.card_range n, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by simp
    rw [e] at h
    exact_mod_cast h
  · intro g _ hg
    have hp : ρ g ^ 2 ^ k = 1 := by rw [← map_pow, ← hk, pow_card_eq_one, map_one]
    let A : Matrix (Fin n) (Fin n) ℂ := (Int.castRingHom ℂ).mapMatrix (ρ g)
    have hA : A ^ 2 ^ k = 1 := by simp only [A]; rw [← map_pow, hp, map_one]
    have hAt : A.trace = ((ρ g).trace : ℂ) := by simp [A, Matrix.trace]
    have h1 := norm_trace_le A (by positivity) hA
    rw [hAt, Complex.norm_intCast] at h1
    have h1' : |(ρ g).trace| ≤ n := by exact_mod_cast h1
    have h2 : (ρ g).trace ≠ n := by
      intro h2
      have h3 := eq_one_of_trace A (by positivity) hA (by rw [hAt, h2]; simp)
      apply hg
      apply hρ
      apply Matrix.map_injective (f := (Int.castRingHom ℂ : ℤ → ℂ)) Int.cast_injective
      have h4 : (ρ g).map (Int.castRingHom ℂ) = 1 := h3
      simp only [h4]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    obtain ⟨c, hc⟩ := two_dvd_sub_trace (ρ g) hp
    obtain ⟨h5, h6⟩ := abs_le.1 h1'
    rw [eval_prod]
    refine Finset.prod_eq_zero (i := (c - 1).toNat) (Finset.mem_range.2 (by omega)) ?_
    rw [eval_sub, eval_X, eval_C]
    omega
  · simp

theorem exp_eq (n p : ℕ) (hp : p.Prime) :
    n / (p - 1) + padicValNat p (n / (p - 1)).factorial = Formalism.HermitianLatticeCounting.S6.minkowskiExp n p := by
  haveI := Fact.mk hp
  have hl : Nat.log p (n / (p - 1)) < n + 1 :=
    Nat.lt_succ_of_le ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _))
  rw [padicValNat_factorial hl, Formalism.HermitianLatticeCounting.S6.minkowskiExp, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), pow_zero, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.div_div_eq_div_mul, mul_comm]

open MinkowskiOrder in

theorem minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound := by
  intro n G hG
  have hc : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hk
  haveI := Fact.mk hp
  have hle : k ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial := by
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hk
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card] at hK
      have h := card_two_group_dvd ((Units.coeHom _).comp (G.subtype.comp K.subtype))
        (fun g hg => Subtype.ext (Subtype.ext (Units.ext hg))) hK
      have hf := Nat.factorial_ne_zero n
      rw [padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by positivity) hf,
        padicValNat.prime_pow] at h
      simpa using h
    · obtain ⟨l, hl, hpl, h⟩ := exists_prime_gen p hp h2
      have hp2 := hp.two_le
      refine le_trans ?_ (sum_odd p l hp h2 hl hpl h n)
      rw [← val_prod n p l hp hl (by omega)]
      exact (hp.pow_dvd_iff_le_factorization (Finset.prod_ne_zero_iff.mpr fun i _ =>
        Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt i.2))).1
        (hk.trans (card_dvd_prod n G l hl (by omega)))
  by_cases hpn : p < n + 2
  · rw [exp_eq n p hp] at hle
    refine (pow_dvd_pow p hle).trans ?_
    exact Finset.dvd_prod_of_mem (fun q => q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 hpn, hp⟩)
  · rw [Nat.div_eq_of_lt (by omega)] at hle
    have : k = 0 := by simpa using hle
    rw [this, pow_zero]
    exact one_dvd _

end GlobalTheory.MinkowskiExact
end

section
noncomputable section

namespace GlobalTheory.DGamPrimeToLevel

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm

theorem minkMult_minkM (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) (n : ℕ) : MinkMult n (minkM n) := by
  intro H hH
  let e : Matrix.GeneralLinearGroup (Fin n) ℚ ≃* ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ (Fin n → ℚ))
  let G : Subgroup ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) := H.map e.toMonoidHom
  have e' : H ≃* G := e.subgroupMap H
  have hG : Finite G := Finite.of_equiv _ e'.toEquiv
  let v : G × Fin n → (Fin n → ℚ) := fun p => p.1.1 (Pi.basisFun ℚ (Fin n) p.2)
  let Λ : Submodule (𝓞 ℚ) (Fin n → ℚ) := Submodule.span (𝓞 ℚ) (Set.range v)
  have hfg : Λ.FG := Submodule.fg_span (Set.finite_range v)
  have hsp : Submodule.span ℚ (Λ : Set (Fin n → ℚ)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), rfl⟩
  have hst : ∀ g ∈ G, ∀ x ∈ Λ, g x ∈ Λ := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨g, hg⟩ * h, i), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul ℚ a x, map_smul, algebraMap_smul]
      exact Λ.smul_mem a hx
  have h := GlobalTheory.AutLattice.card_dvd_minkM hM ℚ (Fin n → ℚ) Λ hfg hsp G hG hst
  rw [Nat.card_congr e'.toEquiv]
  simpa using h

def PrimesLarge (D : D7) : Prop :=
  (∀ u, minkRank D + 1 < (D.mem u).A.T) ∧ (∀ a, minkRank D + 1 < D.host.g a) ∧
    minkRank D + 1 < D.host.q ∧ minkRank D + 1 < D.host.d

theorem primeToLevel_of_dvd {D : D7} (h : PrimesLarge D) {n : ℕ} (hn : n ∣ minkM (minkRank D)) :
    PrimeToLevel D n := by
  have hp : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ minkRank D + 1 := fun p hp hpn =>
    GlobalTheory.prime_le_succ_of_dvd_minkM _ p hp (hpn.trans hn)
  have key : ∀ p : ℕ, p.Prime → minkRank D + 1 < p → Nat.Coprime n p := by
    intro p hpp hlt
    refine ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun h => ?_).symm
    have := hp p hpp h
    omega
  obtain ⟨g1, g2, g3, g4⟩ := h
  exact ⟨hn, hp, key _ D.host.hyp.1 g3, key _ D.host.hyp.2.1 g4,
    fun a => key _ (D.host.g_prime a) (g2 a), fun u => key _ (D.mem u).A.T_prime (g1 u)⟩

theorem minkRank_le {D : D7} (L : SizeData₂ D) (hN : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (L.Ct + 1))
    (hx : 2 ≤ L.sc.x) : ((minkRank D + 1 : ℕ) : ℝ) ≤ L.sc.x ^ (2 * L.Ct + 5) := by
  have hf : D.R.f ≤ D.R.N D.R.m := le_trans (show D.R.f ≤ D.R.k from D.R.f_le_k) (Nat.le_add_right _ _)
  have h1 : 1 ≤ D.R.N D.R.m := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  have hf' : (D.R.f : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hf
  have h1' : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h1
  have hx0 : 0 < L.sc.x := by linarith
  have e : L.sc.x ^ (2 * L.Ct + 5) = (L.sc.x ^ (L.Ct + 1)) ^ 2 * L.sc.x ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  have h8 : (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3 := by gcongr
  have h2 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (L.sc.x ^ (L.Ct + 1)) ^ 2 := by gcongr
  have h3 : (D.R.N D.R.m : ℝ) ^ 2 * 2 ^ 3 ≤ (L.sc.x ^ (L.Ct + 1)) ^ 2 * L.sc.x ^ 3 := by gcongr
  rw [e]
  unfold minkRank
  push_cast
  nlinarith

theorem primesLarge_of_sizesUsed {D : D7} (L : SizeData₂ D) (h : SizesUsed L) : PrimesLarge D := by
  obtain ⟨⟨P⟩, hN, hT, hx⟩ := h
  have h0 := minkRank_le L hN hx
  have hq : minkRank D + 1 < D.host.q := by exact_mod_cast h0.trans_lt P.qd_pow.1
  have hd : minkRank D + 1 < D.host.d := by exact_mod_cast h0.trans_lt P.qd_pow.2
  have hC : SizeCond L := by
    have := P.condE_le
    unfold SizeCond szCond
    rw [Real.sqrt_eq_rpow]
    unfold LevelStarExponents.condE at this
    push_cast at this
    exact this
  have hs := GlobalTheory.DGamCoprime.q_le_sqrt_b L hC (by omega) (by omega)
  have hb := GlobalTheory.DGamCoprime.one_le_b L
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hqb : (D.host.q : ℝ) ≤ L.sc.b := hs.trans hsb
  refine ⟨fun u => ?_, fun a => ?_, hq, hd⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have h1 : L.sc.b ^ (1 : ℝ) ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    rw [Real.rpow_one] at h1
    have : (D.host.q : ℝ) ≤ ((D.mem u).A.T : ℝ) := hqb.trans (h1.trans (hT u))
    have : D.host.q ≤ (D.mem u).A.T := by exact_mod_cast this
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have h1 : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h2 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ (hb.trans h1) (by norm_num)
    have : (D.host.q : ℝ) ≤ (D.host.g a : ℝ) := hqb.trans (h1.trans (h2.trans (hY.trans (hg a).1)))
    have : D.host.q ≤ D.host.g a := by exact_mod_cast this
    omega

theorem primeToLevelAt_of (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) {D : D7} (h : PrimesLarge D) (hD : DGamDef D)
    (hC : DGamChoice_at D) : PrimeToLevelAt D := by
  intro u μ
  rw [hD.one u u μ]
  exact primeToLevel_of_dvd h (hC _ (minkMult_minkM hM _) u)

theorem primesLarge_family {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧ ∀ i : Fm.Ix x, PrimesLarge (Fm.D x i) := by
  obtain ⟨x0, hT⟩ := hT
  refine ⟨max x0 (Fm.x1 + 1), fun x hx => ?_⟩
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  exact ⟨hx1, fun i => GlobalTheory.DGamCoprime.primes_gt (Fm.L x i) (Fm.sizes x hx1 i)
    (hT x ((le_max_left _ _).trans hx) i).1⟩

theorem row_of_minkowski (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) : Row := by
  refine ⟨fun D L hS hD hC => primeToLevelAt_of hM (primesLarge_of_sizesUsed L hS) hD hC,
    fun eps Fm hC hT => ?_⟩
  obtain ⟨x0, hP⟩ := primesLarge_family Fm hT
  obtain ⟨x0', hC⟩ := hC
  refine ⟨max x0 x0', fun x hx i => ?_⟩
  obtain ⟨hx1, hP⟩ := hP x ((le_max_left _ _).trans hx)
  exact primeToLevelAt_of hM (hP i) (Fm.ex x hx1 i).err.dgam (hC x ((le_max_right _ _).trans hx) i)

theorem row : Row := row_of_minkowski GlobalTheory.MinkowskiExact.minkowskiBound

end GlobalTheory.DGamPrimeToLevel

end
end

section
noncomputable section

namespace GlobalTheory.DGamOnRecord

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm GlobalTheory.DGamPrimeToLevel
open Formalism.L2.Col (Sp hStd autLat PosStar)
open Formalism.HermitianLatticesTheory (isom IsUnimodular)
open GlobalTheory.Mem.Col2 (DGam autOrd autO gamOrd gamRanks)

section Transport

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

omit [StarRing E] in

theorem card_dvd_of_minkMult {n N M : ℕ} (hM : MinkMult N M) (hN : Module.finrank ℚ E * n ≤ N)
    (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) [Finite G] : Nat.card G ∣ M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hr : Module.finrank ℚ (Sp E n × (Fin k → ℚ)) = Module.finrank ℚ E * n + k := by
    rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  let b := Module.finBasisOfFinrankEq ℚ _ hr
  let r : G →* Module.End ℚ (Sp E n × (Fin k → ℚ)) :=
    { toFun := fun g => ((g.1 : Sp E n →ₗ[E] Sp E n).restrictScalars ℚ).prodMap LinearMap.id
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hr : Function.Injective r := fun g h hgh =>
    Subtype.ext (LinearEquiv.ext fun x => congrArg Prod.fst (LinearMap.congr_fun hgh (x, 0)))
  let φ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank ℚ E * n + k)) ℚ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := fun g h hgh =>
    hr ((LinearMap.toMatrixAlgEquiv b).injective (congrArg Units.val hgh))
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM φ.range (Finite.of_equiv _ e.toEquiv)

end Transport

end GlobalTheory.DGamOnRecord

end
end
