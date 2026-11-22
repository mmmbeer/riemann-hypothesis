import Mathlib

namespace UpperTheory.Reformulated.B.SquareOfApproximation

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter Topology

private lemma small_power_bound {A : Type*} [Ring A] [_i : Valued A (WithZero (Multiplicative ℤ))]
    (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ) :
    ∃ N : ℕ, ∀ x : A, Valued.v x ≤ exp (-(N : ℤ)) → _i.v.restrict x < γ.1 := by
  have hg : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp k :=
    ⟨log _, (exp_log hg).symm⟩
  refine ⟨(-k + 1).toNat, fun x hx => ?_⟩
  rw [Valuation.restrict_lt_iff_lt_embedding, hk]
  refine lt_of_le_of_lt hx ?_
  rw [exp_lt_exp]
  have := Int.self_le_toNat (-k + 1)
  omega

private lemma square_of_approx {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (b : ℕ → R) (d : R)
    (hb : ∀ m k, m ≤ k → b k - b m ∈ v.asIdeal ^ m)
    (hd : ∀ m, b m * b m - d ∈ v.asIdeal ^ m) :
    IsSquare (algebraMap K (v.adicCompletion K) (algebraMap R K d)) := by
  set f : ℕ → v.adicCompletion K :=
    fun m => algebraMap K (v.adicCompletion K) (algebraMap R K (b m)) with hf
  set D := algebraMap K (v.adicCompletion K) (algebraMap R K d) with hD
  have hval : ∀ (r : R) (m : ℕ), r ∈ v.asIdeal ^ m →
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ exp (-(m : ℤ)) := by
    intro r m hr
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) =
        v.valuation K (algebraMap R K r) := valuedAdicCompletion_eq_valuation' v _
    rw [h1, valuation_of_algebraMap]
    exact (intValuation_le_pow_iff_mem v r m).2 hr
  have hcau : CauchySeq f := by
    rw [CauchySeq, Valued.cauchy_iff]
    refine ⟨inferInstance, fun γ => ?_⟩
    obtain ⟨N, hN⟩ := small_power_bound γ
    refine ⟨f '' Set.Ici N, Filter.image_mem_map (Filter.mem_atTop N), ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩
    apply hN
    have hm' : N ≤ m := hm
    have hk' : N ≤ k := hk
    have : b k - b m ∈ v.asIdeal ^ N := by
      rcases le_total m k with h | h
      · exact Ideal.pow_le_pow_right hm' (hb m k h)
      · have := Ideal.pow_le_pow_right hk' (hb k m h)
        rw [← neg_sub]; exact neg_mem this
    have h2 := hval _ _ this
    simpa [hf, map_sub] using h2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have h0 : Tendsto (fun m => f m * f m - D) atTop (𝓝 0) := by
    rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := small_power_bound γ
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    apply hN
    have := hval _ _ (Ideal.pow_le_pow_right hm (hd m))
    simpa [hf, hD, map_sub, map_mul] using this
  have h1 : Tendsto (fun m => f m * f m - D) atTop (𝓝 (L * L - D)) :=
    (hL.mul hL).sub_const D
  have h2 : L * L - D = 0 := tendsto_nhds_unique h1 h0
  exact ⟨L, (sub_eq_zero.1 h2).symm⟩

private lemma approx {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
    (hσ : ∀ x, σ (σ x) = x)
    (htr : ∀ y, ∃ r : R, algebraMap R S r = y + σ y)
    (hnm : ∀ y, ∃ r : R, algebraMap R S r = y * σ y)
    (P Q : Ideal S) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (hne : P ≠ Q)
    (hc : P.comap (algebraMap R S) = Q.comap (algebraMap R S)) (t : S) (n : ℕ) :
    ∃ a : R, t - algebraMap R S a ∈ P ^ n := by
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hσ x⟩
  have hP'max : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hne' : P ≠ P.comap σ := by
    intro h
    obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q, x ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hne ((hQ.eq_of_le hP.ne_top hcon).symm)
    obtain ⟨r, hr⟩ := hnm x
    have h1 : r ∈ Q.comap (algebraMap R S) := by
      rw [Ideal.mem_comap, hr]; exact Q.mul_mem_right _ hxQ
    rw [← hc, Ideal.mem_comap, hr] at h1
    rcases hP.isPrime.mem_or_mem h1 with h2 | h2
    · exact hxP h2
    · apply hxP; rw [h]; exact h2
  have hcop : IsCoprime (P ^ n) ((P.comap σ) ^ n) :=
    IsCoprime.pow ((Ideal.isCoprime_iff_sup_eq).2 (Ideal.IsMaximal.coprime_of_ne hP hP'max hne'))
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨a, ha⟩ := htr (t * q)
  refine ⟨a, ?_⟩
  have hsq : σ q ∈ P ^ n := by
    have h1 : σ q ∈ ((P.comap σ) ^ n).map σ := Ideal.mem_map_of_mem σ hq
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_comap_le) n h1
  rw [ha, map_mul]
  have h3 : t - (t * q + σ t * σ q) = t * p - σ t * σ q := by
    have : q = 1 - p := by rw [← hpq]; ring
    rw [this]; simp only [map_sub, map_one]; ring
  rw [h3]
  exact sub_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hsq)

private theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d)
    (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (P Q : HeightOneSpectrum (𝓞 E)) (hne : P ≠ Q)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    (hQ : Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) :
    IsSquare (algebraMap F (v.adicCompletion F) (d : F)) := by
  have hsp' : ∀ x : E, ∃ u w : F, x = algebraMap F E u + algebraMap F E w * θ := by
    intro x
    obtain ⟨u, w, h⟩ := hsp x
    exact ⟨u, w, by rw [h, Algebra.smul_def, Algebra.smul_def, mul_one]⟩
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    apply hd
    have h0 : algebraMap F E d = 0 := by rw [← hθ]; simp
    exact (map_eq_zero (algebraMap F E)).1 h0
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add, map_mul, AlgHom.commutes, hσ, map_neg, mul_neg, neg_neg]
  have hfix : ∀ x, σ x = x → ∃ u : F, x = algebraMap F E u := by
    intro x hx
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add, map_mul, AlgHom.commutes, hσ, mul_neg] at hx
    have h2 : (2 : E) * (algebraMap F E w * θ) = 0 := by
      have h3 := add_left_cancel hx
      linear_combination -h3
    have hw : w = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h two_ne_zero
      · rcases mul_eq_zero.1 h with h | h
        · exact (map_eq_zero (algebraMap F E)).1 h
        · exact absurd h hθ0
    exact ⟨u, by simp [hw]⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply RingOfIntegers.ext
    rw [hs, hs, hσσ]
  have hfixO : ∀ y : 𝓞 E, s y = y → ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y := by
    intro y hy
    obtain ⟨u, hu⟩ := hfix (y : E) (by rw [← hs, hy])
    have hint : IsIntegral ℤ u := by
      have h1 : IsIntegral ℤ (algebraMap F E u) := hu ▸ RingOfIntegers.isIntegral_coe y
      exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1
    refine ⟨⟨u, hint⟩, ?_⟩
    apply RingOfIntegers.ext
    exact hu.symm
  have htr : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y + s y := fun y =>
    hfixO _ (by rw [map_add, hss, add_comm])
  have hnm : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y * s y := fun y =>
    hfixO _ (by rw [map_mul, hss, mul_comm])
  have hint : IsIntegral ℤ θ := by
    have h1 : IsIntegral ℤ (θ ^ 2) := by
      rw [pow_two, hθ]
      exact (RingOfIntegers.isIntegral_coe d).algebraMap
    exact h1.of_pow (by norm_num)
  let t : 𝓞 E := ⟨θ, hint⟩
  have ht : t * t = algebraMap (𝓞 F) (𝓞 E) d := by
    apply RingOfIntegers.ext
    exact hθ
  have := P.isMaximal
  have := Q.isMaximal
  have hne' : P.asIdeal ≠ Q.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  choose a ha using
    approx (R := 𝓞 F) s hss htr hnm P.asIdeal Q.asIdeal hne' (hP.trans hQ.symm) t
  have : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal v.ne_bot
  set e := v.asIdeal.ramificationIdx' P.asIdeal
  have hdown : ∀ (x : 𝓞 F) (m : ℕ), algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal ^ (e * m) →
      x ∈ v.asIdeal ^ m := by
    intro x m hx
    rw [← intValuation_le_pow_iff_mem] at hx ⊢
    rw [← intValuation_liesOver v P x] at hx
    have h1 : exp (-((e * m : ℕ) : ℤ)) = (exp (-(m : ℤ))) ^ e := by
      rw [← exp_nsmul]
      congr 1
      simp
    rw [h1] at hx
    exact (pow_le_pow_iff_left₀ zero_le zero_le he).1 hx
  have hb : ∀ m k, m ≤ k → a (e * k) - a (e * m) ∈ v.asIdeal ^ m := by
    intro m k hmk
    apply hdown
    have h1 := ha (e * m)
    have h2 := Ideal.pow_le_pow_right (Nat.mul_le_mul_left e hmk) (ha (e * k))
    have h3 := sub_mem h1 h2
    have h4 : t - algebraMap (𝓞 F) (𝓞 E) (a (e * m)) - (t - algebraMap (𝓞 F) (𝓞 E) (a (e * k))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * k) - a (e * m)) := by
      rw [map_sub]; ring
    rwa [h4] at h3
  have hdd : ∀ m, a (e * m) * a (e * m) - d ∈ v.asIdeal ^ m := by
    intro m
    apply hdown
    have h1 := Ideal.mul_mem_left _ (-(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m)))) (ha (e * m))
    have h2 : -(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m))) * (t - algebraMap (𝓞 F) (𝓞 E) (a (e * m))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * m) * a (e * m) - d) := by
      rw [map_sub, map_mul, ← ht]; ring
    rwa [h2] at h1
  exact square_of_approx v (fun m => a (e * m)) d hb hdd

noncomputable def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)

theorem aux2 {F E : Type} [Field F] [Field E] :
    RingHomClass (𝓞 F →+* 𝓞 E) (𝓞 F) (𝓞 E) :=
  inferInstance

noncomputable def IsSplit {F E : Type} [Field F] [Field E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P Q : HeightOneSpectrum (𝓞 E),
    P ≠ Q ∧
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal ∧
      Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Type :=
  v.adicCompletion F

theorem main {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (_ : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d) (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) d) := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  exact core σ hd hσ hθ hsp P Q hne hP hQ

end UpperTheory.Reformulated.B.SquareOfApproximation
