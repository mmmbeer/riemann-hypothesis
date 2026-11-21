import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfVal
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.Model

section General

variable {E : Type} [Field E] [NumberField E]


theorem IsCMType.bijective {I : Type} {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm


theorem expIn_eq_zero {𝔣 : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} : expIn 𝔣 v = 0 ↔ ¬ v.asIdeal ∣ 𝔣 :=
  multiplicity_eq_zero


theorem levelLe_one (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) : LevelLe (1 : HChar E) P n := fun _ _ _ => rfl


theorem exists_over (v : HeightOneSpectrum (OF E)) : ∃ P : HeightOneSpectrum (𝓞 E), Over P v := by
  have := v.isPrime
  obtain ⟨⟨P, hP, hl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
  exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl.over.symm⟩

theorem exists_ramified {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hf : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q)
    (h : IsValChar φ s κ 𝔣 Q χ) : ∃ P, ¬ UnrAt χ P := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 hf.2.1
  have hne : M ≠ ⊥ := fun e => hf.1 (le_bot_iff.1 (e ▸ hle))
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, hne⟩
  have hd : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.2 hle
  obtain ⟨P, hP⟩ := exists_over v
  refine ⟨P, fun hu => ?_⟩
  have h1 := ((h.2.2.2 v P hP).2 (fun hq => (hQ v hq).2 hd) 0).1 ((χ.unrAt_iff P).1 hu)
  exact expIn_eq_zero.1 (Nat.le_zero.1 h1) hd


end General

section Integrality

theorem IntAt.add {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a + b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have := ((isIntegral_natCast (R := ℤ) m).mul ha).add ((isIntegral_natCast (R := ℤ) n).mul hb)
  have e : ((n * m : ℕ) : ℂ) * (a + b) = m * (n * a) + n * (m * b) := by push_cast; ring
  rw [e]; exact this

theorem IntAt.mul {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have e : ((n * m : ℕ) : ℂ) * (a * b) = (n * a) * (m * b) := by push_cast; ring
  rw [e]; exact ha.mul hb

end Integrality

section Symmetry

variable {E : Type} [Field E] [NumberField E]

theorem LevelLe.mono {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (h : LevelLe χ P m) (hmn : m ≤ n) :
    LevelLe χ P n := fun y h1 h3 =>
  h y h1 (h3.trans (WithZero.exp_le_exp.2 (by omega)))

theorem levelLe_inv {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} : LevelLe χ⁻¹ P n ↔ LevelLe χ P n := by
  refine forall_congr' fun y => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  change (χ.loc P y)⁻¹ = 1 ↔ _
  exact inv_eq_one

theorem IsValChar.inv {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (h : IsValChar φ s κ 𝔣 Q χ) :
    IsValChar (fun i => ComplexEmbedding.conjugate (φ i)) s κ 𝔣 Q χ⁻¹ := by
  obtain ⟨h1, ⟨h2, h2'⟩, h3, h4⟩ := h
  refine ⟨fun x => ?_, ⟨fun v k => ?_, fun w k => ?_⟩, (hasInfRatio_iff _ _ _).2 fun k => ?_, fun v P hP => ⟨fun hv => ?_, fun hv m => ?_⟩⟩
  · change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, h1 x, inv_one]
  · have h := h2 v k
    unfold Formalism.L2.Host.HChar.resFin at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    rw [← inv_eq_one, ← Finset.prod_inv_distrib] at h
    exact h
  · have h := h2' w k
    unfold Formalism.L2.Host.HChar.resInf at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    rw [← inv_eq_one, ← Finset.prod_inv_distrib] at h
    exact h
  · change (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val, (hasInfRatio_iff _ _ _).1 h3 k, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← inv_zpow, inv_div]
    simp
  · exact levelLe_inv.2 ((h4 v P hP).1 hv)
  · rw [levelLe_inv]; exact (h4 v P hP).2 hv m

end Symmetry

section Twist

variable {E : Type} [Field E] [NumberField E]



theorem IsValChar.inf_eq {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q Q' : Finset (HeightOneSpectrum (OF E))} {χ χ' : HChar E} (h : IsValChar φ s κ 𝔣 Q χ) (h' : IsValChar φ s κ 𝔣 Q' χ')
    (k : Eˣ) : (χ * χ'⁻¹).inf k = 1 := by
  have : χ.inf k = χ'.inf k := Units.ext ((h.2.2.1 k).trans (h'.2.2.1 k).symm)
  simp [this]

theorem condQ_empty (𝔣 : Ideal (OF E)) : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]

end Twist

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local notation "cj" => IsCMField.ringOfIntegersComplexConj E

theorem splits_of_absNorm {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E))
    (hv : Over P v) (hN : Ideal.absNorm P.asIdeal = l) (x : 𝓞 E) (hx : x - cj x ∉ P.asIdeal) : Splits v := by
  have := P.isPrime
  let P' : HeightOneSpectrum (𝓞 E) := ⟨P.asIdeal.comap (cj).toRingEquiv.toRingHom, Ideal.comap_isPrime _ _, fun h => by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have : (cj).symm y ∈ P.asIdeal.comap (cj).toRingEquiv.toRingHom := by
      rw [Ideal.mem_comap]; simpa using hy
    rw [h, Ideal.mem_bot] at this
    exact hy0 (by simpa using this)⟩
  refine ⟨P, P', fun e => hx ?_, hv, ?_⟩
  · haveI : Fact (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime := ⟨by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]; exact hl⟩
    have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal) = ⊤ := by
      rcases (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal)).eq_bot_or_eq_top_of_prime_card with h | h
      · exact absurd (AddSubgroup.zmultiples_eq_bot.1 h) one_ne_zero
      · exact h
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (htop ▸ AddSubgroup.mem_top (Ideal.Quotient.mk P.asIdeal x))
    have h1 : x - n ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq, ← hn]; simp
    have h2 : x - n ∈ P'.asIdeal := e ▸ h1
    have h3 : cj x - n ∈ P.asIdeal := by
      have : cj (x - n) ∈ P.asIdeal := h2
      simpa using this
    have := P.asIdeal.sub_mem h1 h3
    simpa using this
  · unfold Over at hv ⊢
    rw [← hv]
    ext y
    change cj (algebraMap (OF E) (𝓞 E) y) ∈ P.asIdeal ↔ algebraMap (OF E) (𝓞 E) y ∈ P.asIdeal
    rw [AlgEquiv.commutes]

theorem sub_conj_notMem {z : 𝓞 E} (hz : IsPrimitiveRoot z 21) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) : z - cj z ∉ P := by
  intro h
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hpow : z ^ 21 = 1 := hz.pow_eq_one
  have hc : cj z * z = 1 := by
    apply RingOfIntegers.ext
    apply σ.injective
    have hn : ‖σ (z : E)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := 21) (by
      rw [← map_pow]
      have : (z : E) ^ 21 = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 E) E) hpow
      rw [this, map_one]) (by norm_num)
    change σ (IsCMField.complexConj E (z : E) * (z : E)) = σ 1
    rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.conj_mul', hn]; simp
  set q := Ideal.Quotient.mk P
  have h1 : q z = q (cj z) := Ideal.Quotient.eq.2 h
  have h2 : q z ^ 2 = 1 := by rw [sq]; nth_rw 1 [h1]; rw [← map_mul, hc, map_one]
  have h3 : q z ^ 21 = 1 := by rw [← map_pow, hpow, map_one]
  have h4 : q z = 1 := by
    have : q z ^ 21 = (q z ^ 2) ^ 10 * q z := by ring
    rw [this, h2] at h3; simpa using h3
  have a3 := congrArg q ((hz.pow (by norm_num) (show 21 = 7 * 3 by norm_num)).geom_sum_eq_zero (by norm_num))
  have a7 := congrArg q ((hz.pow (by norm_num) (show 21 = 3 * 7 by norm_num)).geom_sum_eq_zero (by norm_num))
  simp [h4] at a3 a7
  have : (1 : 𝓞 E ⧸ P) = 0 := by linear_combination a7 - 2 * a3
  exact hP (Ideal.Quotient.zero_eq_one_iff.1 this.symm)

end CM

section Cyclotomic

abbrev K : Type := CyclotomicField 21 ℚ

instance : IsCyclotomicExtension {21} ℚ K := CyclotomicField.isCyclotomicExtension 21 ℚ

instance : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {21}) ⟨21, rfl, by norm_num⟩

theorem zeta_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta_spec 21 ℚ K).toInteger 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ K).toInteger_isPrimitiveRoot

attribute [local instance] FractionRing.liftAlgebra in

theorem unramFin_K : UnramFin K := by
  have hu := Formalism.L2.Pj.unramBridge_holds K (fun P hP => ⟨_, sub_conj_notMem zeta_prim hP.ne_top⟩)
  have hsep : Algebra.IsSeparable (FractionRing (OF K)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (OF K) (maximalRealSubfield K)).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have := hM.isPrime
  exact (not_dvd_differentIdeal_iff (A := OF K) (P := M)).2 inferInstance (Ideal.dvd_iff_le.2 hle)

theorem absNorm_of_mem (P : HeightOneSpectrum (𝓞 K)) (h : ((43 : ℕ) : 𝓞 K) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = 43 := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have := P.isPrime
  haveI : P.asIdeal.LiesOver (Ideal.span {((43 : ℕ) : ℤ)}) := by
    refine ⟨?_⟩
    have hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 43
    refine hmax.eq_of_le (Ideal.IsPrime.under ℤ P.asIdeal).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) ((43 : ℕ) : ℤ) ∈ P.asIdeal
    simpa using h
  rw [← Ideal.pow_inertiaDeg 43 P.asIdeal,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 21) 43 K P.asIdeal (by norm_num)]
  have : ((43 : ℕ) : ZMod 21) = 1 := by decide
  rw [this, orderOf_one, pow_one]

theorem not_dvd_discr : ¬ ((43 : ℕ) : ℤ) ∣ discr K := fun h => by
  have h0 : (discr K).natAbs ∣ 21 ^ Nat.totient 21 :=
    IsCyclotomicExtension.Rat.natAbs_discr 21 K ▸
      Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (by norm_num))
  have h₂ := (by norm_num : Nat.Prime 43).dvd_of_dvd_pow ((Int.natCast_dvd.1 h).trans h0)
  omega

theorem splits_of_mem (v : HeightOneSpectrum (OF K)) (h : ((43 : ℕ) : OF K) ∈ v.asIdeal) : Splits v := by
  obtain ⟨P, hP⟩ := exists_over v
  refine splits_of_absNorm (by norm_num : Nat.Prime 43) P v hP (absNorm_of_mem P ?_) _
    (sub_conj_notMem zeta_prim P.isPrime.ne_top)
  rw [← hP, Ideal.mem_comap, map_natCast] at h
  exact h

theorem exists_place : ∃ v : HeightOneSpectrum (OF K), ((43 : ℕ) : OF K) ∈ v.asIdeal := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have hmax : (Ideal.span {((43 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 43
  obtain ⟨⟨P, hP, hl⟩⟩ := (Ideal.span {((43 : ℕ) : ℤ)}).nonempty_primesOver (S := OF K)
  refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {((43 : ℕ) : ℤ)}) (by simp) P⟩, ?_⟩
  have : ((43 : ℕ) : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
  simpa [Ideal.mem_comap] using this






theorem exists_place' : ∃ v : HeightOneSpectrum (OF K), ((127 : ℕ) : OF K) ∈ v.asIdeal := by
  haveI : Fact (Nat.Prime 127) := ⟨by norm_num⟩
  have hmax : (Ideal.span {((127 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 127
  obtain ⟨⟨P, hP, hl⟩⟩ := (Ideal.span {((127 : ℕ) : ℤ)}).nonempty_primesOver (S := OF K)
  refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {((127 : ℕ) : ℤ)}) (by simp) P⟩, ?_⟩
  have : ((127 : ℕ) : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
  simpa [Ideal.mem_comap] using this


end Cyclotomic

end GlobalTheory.CMVal.Model
