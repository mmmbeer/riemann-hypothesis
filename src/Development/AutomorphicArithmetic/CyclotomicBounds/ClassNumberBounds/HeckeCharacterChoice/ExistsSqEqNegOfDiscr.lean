import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.NCField
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HostPrimes
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsIsPrimitiveRootIff
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.PrincipalIdele
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.SplitDef
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.DelRay
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDefs
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HvQuadInertia

section
namespace KStar.Choice

structure IsLevelPair (N a b : ℕ) : Prop where
  prime_fst : a.Prime
  prime_snd : b.Prime
  ne_two : a ≠ 2
  lt : a < b
  lt_two_mul : b < 2 * a
  not_dvd_fst : ¬ a ∣ N
  not_dvd_snd : ¬ b ∣ N

example : IsLevelPair 1 3 5 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

noncomputable def levelFst (N : ℕ) : ℕ := sInf {a | ∃ b, IsLevelPair N a b}

noncomputable def levelSnd (N : ℕ) : ℕ := sInf {b | ∃ a, IsLevelPair N a b}

noncomputable def levelSnd' (N : ℕ) : ℕ := sInf {b | IsLevelPair N (levelFst N) b}



end KStar.Choice
end

section
open NumberField

namespace KStar.Choice

theorem ramLE_one_of_not_dvd (E L : Type*) [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {M l : ℕ} [NeZero M] [IsCyclotomicExtension {M} ℚ L]
    (hl : l.Prime) (h : ¬ l ∣ M) : RamLE E l 1 := by
  have := Fact.mk hl
  have hprime : (Ideal.span {(l : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hl
  obtain ⟨⟨P, h1, h2⟩⟩ := (Ideal.span {(l : ℤ)}).nonempty_primesOver (S := 𝓞 E)
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(l : ℤ)}) := Ideal.LiesOver.trans Q P _
  have h3 := Ideal.ramificationIdx_below_dvd (R := ℤ) P Q
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd l L Q h] at h3
  exact ⟨P, h1, h2, (Nat.dvd_one.1 h3).le⟩

theorem rootData_of_cyclotomic (E Ω : Type*) [Field E] [NumberField E] [Field Ω]
    [NumberField Ω] [Algebra E Ω] {M : ℕ} [NeZero M] [IsCyclotomicExtension {M} ℚ Ω]
    {S L : Finset ℕ} (hS : ∀ l ∈ S, l.Prime)
    (hM : ∀ l, l.Prime → l ≠ 2 → l ∣ M → l ∈ S ∨ l ∈ L)
    (hL : ∀ l ∈ L, l.Prime ∧ 3 < l ∧ RamLE E l 2) : RootData S L (rootNu E) (rootDeg E) :=
  rootData_field E hS (fun l hl h2 h3 h4 => ramLE_one_of_not_dvd E Ω hl fun h =>
    (hM l hl h2 h).elim h3 h4) hL

example (M : ℕ) [NeZero M] : RootData M.primeFactors ∅ (rootNu (CyclotomicField M ℚ))
    (rootDeg (CyclotomicField M ℚ)) :=
  haveI : IsCyclotomicExtension {M} ℚ (CyclotomicField M ℚ) :=
    CyclotomicField.isCyclotomicExtension M ℚ
  rootData_of_cyclotomic _ (CyclotomicField M ℚ) (M := M)
    (fun _ h => Nat.prime_of_mem_primeFactors h)
    (fun _ hl _ h => Or.inl (Nat.mem_primeFactors.2 ⟨hl, h, NeZero.ne M⟩)) (by simp)


end KStar.Choice
end

section
namespace KStar.Choice

theorem exists_avoid (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (bad : (p : ℕ) → Finset (ZMod p)) (hbad : ∀ p ∈ s, (bad p).card < p) (Y : ℤ) :
    ∃ u : ℤ, Y ≤ u ∧ u < Y + ∏ p ∈ s, (p : ℤ) ∧ ∀ p ∈ s, (u : ZMod p) ∉ bad p := by
  classical
  have hc : ∀ p : ℕ, ∃ c : ℕ, p ∈ s → (c : ZMod p) ∉ bad p := by
    intro p
    by_cases hp : p ∈ s
    · have : Fact p.Prime := ⟨hs p hp⟩
      have h1 : (bad p).card < (Finset.univ : Finset (ZMod p)).card := by
        rw [Finset.card_univ, ZMod.card]; exact hbad p hp
      obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
      exact ⟨c.val, fun _ => by rwa [ZMod.natCast_zmod_val]⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose c hc using hc
  have hne : ∀ p ∈ s, id p ≠ 0 := fun p hp => (hs p hp).ne_zero
  have hco : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).2 hpq
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset c id s hne hco
  have hP : (0 : ℤ) < ∏ p ∈ s, (p : ℤ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hs p hp).pos
  refine ⟨Y + ((k : ℤ) - Y) % ∏ p ∈ s, (p : ℤ), ?_, ?_, ?_⟩
  · have := Int.emod_nonneg ((k : ℤ) - Y) hP.ne'
    linarith
  · have := Int.emod_lt_of_pos ((k : ℤ) - Y) hP
    linarith
  · intro p hp
    have hd : (p : ℤ) ∣ ∏ p ∈ s, (p : ℤ) := Finset.dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hp
    have h0 : ((∏ p ∈ s, (p : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    have h1 : ((Y + ((k : ℤ) - Y) % ∏ p ∈ s, (p : ℤ) : ℤ) : ZMod p) = (c p : ZMod p) := by
      rw [Int.emod_def, Int.cast_add, Int.cast_sub, Int.cast_mul, h0, Int.cast_sub,
        Int.cast_natCast, zero_mul, sub_zero, add_sub_cancel]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (hk p hp)
    rw [h1]
    exact hc p hp

end KStar.Choice
end

section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {E : Type*} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)}

end KStar.Choice
end

section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

abbrev modInt (E : Type*) [Field E] (M : ℕ) : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)}

noncomputable def modMap {F E : Type*} [Field F] [Field E] (M : ℕ) (f : 𝓞 F →+* 𝓞 E) :
    (𝓞 F ⧸ modInt F M)ˣ →* (𝓞 E ⧸ modInt E M)ˣ :=
  Units.map (Ideal.quotientMap (I := modInt F M) (modInt E M) f (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)).toMonoidHom

variable {E : Type*} [Field E] [NumberField E]

noncomputable def placeRed {M N : ℕ} (h : N ∣ M) (φ : 𝓞 E →+* ZMod N) :
    (𝓞 E ⧸ modInt E M)ˣ →* (ZMod N)ˣ :=
  Units.map (Ideal.Quotient.lift (modInt E M) φ (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, (ZMod.natCast_eq_zero_iff M N).2 h, zero_mul])).toMonoidHom

def HasCondExp (χ : Idele E →* ℂˣ) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop :=
  (∀ x ∈ localUnits w, Valued.v (finComp w x - 1) ≤ WithZero.exp (-(n : ℤ)) → χ x = 1) ∧
    ∀ m : ℕ, m < n → ∃ x ∈ localUnits w,
      Valued.v (finComp w x - 1) ≤ WithZero.exp (-(m : ℤ)) ∧ χ x ≠ 1

example (w : HeightOneSpectrum (𝓞 E)) : HasCondExp 1 w 0 := ⟨fun _ _ _ => rfl, by simp⟩

section CM

variable [IsCMField E]

noncomputable def antiFin {M : ℕ} (θ : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ) :
    (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ :=
  θ / θ.comp (modMap M (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom)

structure IsAntiHecke {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) (e : ι → ℤ)
    (χ : Idele E →* ℂˣ) : Prop where
  continuous : Continuous χ
  principal : ∀ α : Eˣ, χ (principalIdele E α) = 1
  base : χ.comp (ideleMap (maximalRealSubfield E) E) = 1
  infinite : ∀ x : Idele E, (∀ v, finComp v x = 1) →
    χ x = infType conjRatio τ e (infPart E x)

example {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) : IsAntiHecke τ 0 1 :=
  ⟨continuous_const, fun _ => rfl, rfl, fun _ _ => by simp [infType]⟩

end CM

section Eta

variable (F : Type*) [Field F] [NumberField F] [Algebra F E]

variable {F} (E) in

noncomputable def etaSign (v : HeightOneSpectrum (𝓞 F)) : ℂˣ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1

variable (E) in

noncomputable def etaIdeal : IdealGroup F →* ℂˣ where
  toFun I := ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    etaSign E v ^ FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F)
  map_one' := by simp [FractionalIdeal.count_one]
  map_mul' I J := by
    have h : ∀ I : FractionalIdeal (𝓞 F)⁰ F, Function.HasFiniteMulSupport
        fun v : HeightOneSpectrum (𝓞 F) => etaSign E v ^ FractionalIdeal.count F v I := fun I =>
      (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset
        fun v hv h0 => hv (by simp [h0])
    rw [← finprod_mul_distrib (h _) (h _)]
    refine finprod_congr fun v => ?_
    rw [Units.val_mul, FractionalIdeal.count_mul F _ I.ne_zero J.ne_zero, zpow_add]

noncomputable def signInf : (InfiniteAdeleRing F)ˣ →* ℂˣ :=
  infType phase (fun φ : F →+* ℂ => φ) fun _ => 1

variable (E) in

def EtaRecip : Prop :=
  ∀ a : Fˣ, etaIdeal E F (toPrincipalIdeal (𝓞 F) F a) * signInf F (infDiag F a) = 1

variable (E) in

def IsEta (η : Idele F →* ℂˣ) : Prop :=
  IsHeckeIdele (modInt F 1) (signInf F) 1 η ∧
    HeckeCompat (modInt F 1) (signInf F) 1 η ((etaIdeal E F).comp (primeToMod _).subtype)

end Eta

end KStar.Choice
end

section
open NumberField

namespace KStar.Choice

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {p : ℕ}

def homsOver (E : Type*) [Field E] [Algebra K E] (ψ : 𝓞 K →+* ZMod p) :
    Set (𝓞 E →+* ZMod p) :=
  {φ | φ.comp (algebraMap (𝓞 K) (𝓞 E)) = ψ}

end KStar.Choice
end

section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [IsCMField E] [IsGalois K E]

noncomputable def tameFin (E : Type*) [Field E] [NumberField E] [Algebra K E] {ι : Type*}
    [Fintype ι] {M : ℕ} {g : ι → ℕ} (h : ∀ i, g i ∣ M) (ψ : ∀ i, 𝓞 K →+* ZMod (g i))
    (ω : ∀ i, (ZMod (g i))ˣ →* ℂˣ) : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ :=
  ∏ i, ∏ᶠ φ ∈ homsOver E (ψ i), (ω i).comp (placeRed (h i) φ)

private noncomputable def hfPlace {p : ℕ} (hp : p.Prime) (φ : 𝓞 E →+* ZMod p) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal := RingHom.ker φ
  isPrime := by
    have := Fact.mk hp
    exact RingHom.ker_isPrime φ
  ne_bot := by
    intro h
    have h1 : (p : 𝓞 E) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [h, Ideal.mem_bot] at h1
    exact hp.ne_zero (by exact_mod_cast h1)

end KStar.Choice
end

section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

open KStar.Ram DirichletCharacter

private theorem exists_sq_eq_neg_of_quadratic_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hKd : discr K = -(d : ℤ)) : ∃ δ : K, δ ^ 2 = -(d : K) := by
  obtain ⟨x, hx⟩ : ∃ x : K, ∀ c : ℚ, c • (1 : K) ≠ x := by
    by_contra h
    push_neg at h
    have := (finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).2 h
    omega
  have li : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx (-(s / t))
      rw [neg_smul, neg_eq_iff_add_eq_zero, ← one_smul ℚ x, ← inv_mul_cancel₀ ht, mul_smul, div_eq_inv_mul, mul_smul, ← smul_add, hst, smul_zero]
  let b := basisOfLinearIndependentOfCardEqFinrank li (by simp [hK])
  have hb : ⇑b = ![(1 : K), x] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  set A := b.repr (x ^ 2) 0
  set B := b.repr (x ^ 2) 1
  have hx2 : x ^ 2 = A • (1 : K) + B • x := by
    conv_lhs => rw [← b.sum_repr (x ^ 2)]
    simp [Fin.sum_univ_two, hb, A, B]
  have hrx : b.repr x = Finsupp.single 1 1 := by
    rw [show x = b 1 by simp [hb]]
    exact b.repr_self 1
  have t1 : Algebra.trace ℚ K 1 = 2 := by
    have := Algebra.trace_algebraMap (R := ℚ) (S := K) 1
    simpa [hK] using this
  have tx : Algebra.trace ℚ K x = B := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul]
    simp [hb, hrx, ← sq, B]
  have tx2 : Algebra.trace ℚ K (x ^ 2) = 2 * A + B ^ 2 := by
    rw [hx2, map_add, map_smul, map_smul, t1, tx]
    simp
    ring
  have db : Algebra.discr ℚ b = 4 * A + B ^ 2 := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb, t1, tx, tx2, ← sq]
    ring
  classical
  let I := integralBasis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis I, hK]
  let e := Fintype.equivFinOfCardEq hcard
  let c := b.reindex e.symm
  let P := c.toMatrix I
  have hI : Algebra.discr ℚ I = P.det ^ 2 * Algebra.discr ℚ b := by
    have h1 : Matrix.vecMul (⇑c) (P.map (algebraMap ℚ K)) = ⇑I := c.toMatrix_map_vecMul I
    rw [← h1, Algebra.discr_of_matrix_vecMul]
    congr 1
    rw [Module.Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ b e.symm
  have key : ((Algebra.discr ℚ I : ℚ) : K) = -(d : K) := by
    rw [← coe_discr, hKd]
    push_cast
    ring
  refine ⟨(P.det : K) * (2 * x - B), ?_⟩
  rw [← key, hI, db]
  simp only [Rat.smul_def, mul_one] at hx2
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat]
  linear_combination (4 * (P.det : K) ^ 2) * hx2

private theorem isTotallyComplex_of_quadratic_neg_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hd : d ≠ 0) (hKd : discr K = -(d : ℤ)) : IsTotallyComplex K := by
  have hs := NumberField.sign_discr (K := K)
  rw [hKd] at hs
  have hneg : (-(d : ℤ)).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  rw [hneg, eq_comm, neg_one_pow_eq_neg_one_iff_odd (by decide)] at hs
  obtain ⟨k, hk⟩ := hs
  have hr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hK] at hr
  apply NumberField.nrRealPlaces_eq_zero_iff.mp
  omega

theorem exists_sq_eq_neg_of_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {d : ℕ} (hd : d ≠ 0) (hKd : discr K = -(d : ℤ)) :
    (∃ δ : K, δ ^ 2 = -(d : K)) ∧ IsTotallyComplex K := ⟨exists_sq_eq_neg_of_quadratic_discr hK hKd, isTotallyComplex_of_quadratic_neg_discr hK hd hKd⟩

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}
  {L : Type} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]

end KStar.Choice
end
