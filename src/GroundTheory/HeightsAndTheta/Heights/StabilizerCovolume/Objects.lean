import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Gauss

open NumberField Polynomial
open scoped Matrix ComplexConjugate

abbrev Em : Type := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance cycl4 : IsCyclotomicExtension {4} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance gaussian_isCyclotomic_four : IsCyclotomicExtension {2 ^ 2} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance : IsCMField Em :=
  IsCyclotomicExtension.Rat.isCMField Em (S := {4}) ⟨4, Set.mem_singleton _, by norm_num⟩

def ζ : Em := IsCyclotomicExtension.zeta 4 ℚ Em

theorem hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Em

theorem ζ_sq : ζ ^ 2 = -1 := by
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
  have h : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = ζ ^ 4 - 1 := by ring
  rw [h4, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact eq_neg_of_add_eq_zero_left h

theorem ζ_isIntegral : IsIntegral ℤ ζ := hζ.isIntegral (by norm_num)

theorem exists_of_mem_adjoin {R : Type} [CommRing R] [Algebra R Em] {x : Em}
    (hx : x ∈ Algebra.adjoin R ({ζ} : Set Em)) :
    ∃ a b : R, x = algebraMap R Em a + algebraMap R Em b * ζ := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    simp only [map_sub, map_add, map_mul]
    linear_combination (algebraMap R Em b * algebraMap R Em d) * ζ_sq

theorem exists_rat (x : Em) : ∃ a b : ℚ, x = (a : Em) + (b : Em) * ζ := by
  have hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set Em) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
    trivial
  obtain ⟨a, b, h⟩ := exists_of_mem_adjoin hx
  exact ⟨a, b, by rw [h, eq_ratCast, eq_ratCast]⟩

theorem exists_int {x : Em} (hx : IsIntegral ℤ x) : ∃ a b : ℤ, x = (a : Em) + (b : Em) * ζ := by
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p := 2) (k := 2) (ζ := ζ) (hcycl := gaussian_isCyclotomic_four) hζ
  obtain ⟨y, rfl⟩ := hcl.isIntegral_iff.1 hx
  obtain ⟨a, b, h⟩ := exists_of_mem_adjoin (R := ℤ) y.2
  refine ⟨a, b, Eq.trans ?_ (h.trans (by rw [eq_intCast, eq_intCast]))⟩
  rfl

theorem isIntegral_rep (a b : ℤ) : IsIntegral ℤ ((a : Em) + (b : Em) * ζ) := by
  have ha : IsIntegral ℤ (a : Em) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Em a))
  have hb : IsIntegral ℤ (b : Em) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Em b))
  exact ha.add (hb.mul ζ_isIntegral)

abbrev cc : Em ≃ₐ[maximalRealSubfield Em] Em := IsCMField.complexConj Em

def φ₀ : Em →+* ℂ := Classical.choice inferInstance

theorem emb_ζ (σ : Em →+* ℂ) : σ ζ = Complex.I ∨ σ ζ = -Complex.I := by
  have hs : σ ζ ^ 2 = -1 := by rw [← map_pow, ζ_sq, map_neg, map_one]
  have h : (σ ζ - Complex.I) * (σ ζ + Complex.I) = σ ζ ^ 2 - Complex.I ^ 2 := by ring
  rw [hs, Complex.I_sq, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem ringHom_ext {σ σ' : Em →+* ℂ} (h : σ ζ = σ' ζ) : σ = σ' := by
  have : σ.toRatAlgHom = σ'.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  ext x
  exact congrArg (fun f : Em →ₐ[ℚ] ℂ => f x) this

theorem conj_emb_ζ (σ : Em →+* ℂ) : conj (σ ζ) = -σ ζ := by
  rcases emb_ζ σ with h | h <;> rw [h] <;> simp [Complex.conj_I]

theorem cc_ζ : cc ζ = -ζ := by
  apply φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg, conj_emb_ζ]


theorem cc_intCast (n : ℤ) : cc (n : Em) = n := map_intCast cc n

theorem cmType (σ : Em →+* ℂ) :
    (∃ τ : Unit, (fun _ => φ₀) τ = σ) ↔ ¬ ∃ τ : Unit, (fun _ => φ₀) τ = (starRingEnd ℂ).comp σ := by
  simp only [exists_const]
  constructor
  · rintro rfl h
    have h1 := congrArg (fun f : Em →+* ℂ => f ζ) h
    simp only [RingHom.coe_comp, Function.comp_apply, conj_emb_ζ] at h1
    have h0 : φ₀ ζ ≠ 0 := by rcases emb_ζ φ₀ with h | h <;> rw [h] <;> simp [Complex.I_ne_zero]
    exact h0 (by linear_combination h1 / 2)
  · intro h
    rcases emb_ζ σ with hs | hs <;> rcases emb_ζ φ₀ with hp | hp
    · exact ringHom_ext (hp.trans hs.symm)
    · exact absurd (ringHom_ext (by simp [hs, hp, Complex.conj_I])) h
    · exact absurd (ringHom_ext (by simp [hs, hp, Complex.conj_I])) h
    · exact ringHom_ext (hp.trans hs.symm)

theorem finrank_Em : Module.finrank ℚ Em = 2 := by
  rw [IsCyclotomicExtension.finrank Em (cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

theorem trace_ζ : Algebra.trace ℚ Em ζ = 0 := by
  have h := Algebra.trace_eq_of_algEquiv (cc.restrictScalars ℚ) ζ
  rw [AlgEquiv.restrictScalars_apply, cc_ζ, map_neg] at h
  linarith

theorem trace_rep (a b : ℚ) : Algebra.trace ℚ Em ((a : Em) + (b : Em) * ζ) = 2 * a := by
  have h1 : Algebra.trace ℚ Em (a : Em) = 2 * a := by
    rw [← eq_ratCast (algebraMap ℚ Em) a, Algebra.trace_algebraMap, finrank_Em, nsmul_eq_mul]
    norm_num
  have h2 : Algebra.trace ℚ Em ((b : Em) * ζ) = 0 := by
    rw [← eq_ratCast (algebraMap ℚ Em) b, ← Algebra.smul_def, map_smul, trace_ζ, smul_zero]
  rw [map_add, h1, h2, add_zero]

theorem qsmul_eq (q : ℚ) (v : Em) : q • v = (q : Em) * v := by
  rw [← eq_ratCast (algebraMap ℚ Em) q]
  exact Algebra.smul_def q v

theorem trace_of_integral {w : Em} (hw : IsIntegral ℤ w) : ∃ m : ℤ, Algebra.trace ℚ Em (ζ / 2 * w) = m := by
  obtain ⟨c, d, rfl⟩ := exists_int hw
  refine ⟨-d, ?_⟩
  have : ζ / 2 * ((c : Em) + (d : Em) * ζ) = (((-(d : ℚ) / 2 : ℚ)) : Em) + (((c : ℚ) / 2 : ℚ) : Em) * ζ := by
    push_cast
    linear_combination (d / 2 : Em) * ζ_sq
  rw [this, trace_rep]
  push_cast
  ring

theorem integral_of_trace {v : Em} (h1 : ∃ m : ℤ, Algebra.trace ℚ Em (ζ / 2 * v) = m)
    (h2 : ∃ m : ℤ, Algebra.trace ℚ Em (ζ / 2 * (v * ζ)) = m) : IsIntegral ℤ v := by
  obtain ⟨a, b, rfl⟩ := exists_rat v
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  have e1 : ζ / 2 * ((a : Em) + (b : Em) * ζ) = (((-b / 2 : ℚ)) : Em) + (((a / 2 : ℚ)) : Em) * ζ := by
    push_cast
    linear_combination (b / 2 : Em) * ζ_sq
  have e2 : ζ / 2 * (((a : Em) + (b : Em) * ζ) * ζ) =
      (((-a / 2 : ℚ)) : Em) + (((-b / 2 : ℚ)) : Em) * ζ := by
    push_cast
    linear_combination (a / 2 + b / 2 * ζ : Em) * ζ_sq
  rw [e1, trace_rep] at hm1
  rw [e2, trace_rep] at hm2
  have hb : b = ((-m1 : ℤ) : ℚ) := by push_cast; linarith
  have ha : a = ((-m2 : ℤ) : ℚ) := by push_cast; linarith
  rw [ha, hb]
  have := isIntegral_rep (-m2) (-m1)
  simpa using this

def gaussH : Matrix (Fin 2) (Fin 2) Em := !![1, 0; 0, -1]

theorem hermForm_gauss (x y : Fin 2 → Em) :
    hermForm Em gaussH x y = cc (x 0) * y 0 - cc (x 1) * y 1 := by
  simp [hermForm, gaussH, Fin.sum_univ_two]
  ring

def gaussL : Submodule (𝓞 Em) (Fin 2 → Em) where
  carrier := {x | ∀ a, IsIntegral ℤ (x a)}
  add_mem' hx hy a := (hx a).add (hy a)
  zero_mem' _ := isIntegral_zero
  smul_mem' c x hx a := by
    show IsIntegral ℤ ((c • x) a)
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (hx a)


theorem single_mem (a : Fin 2) {v : Em} (hv : IsIntegral ℤ v) : Pi.single a v ∈ gaussL := by
  intro b
  by_cases h : b = a
  · subst h; simpa using hv
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero

theorem gaussL_fg : (gaussL.restrictScalars ℤ).FG := by
  let f : (Fin 2 → 𝓞 Em) →ₗ[ℤ] (Fin 2 → Em) :=
    LinearMap.pi fun a => ((Algebra.linearMap (𝓞 Em) Em).restrictScalars ℤ).comp (LinearMap.proj a)
  have : gaussL.restrictScalars ℤ = Submodule.map f ⊤ := by
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.map_top, LinearMap.mem_range]
    constructor
    · intro hx
      exact ⟨fun a => ⟨x a, hx a⟩, by funext a; rfl⟩
    · rintro ⟨z, rfl⟩ a
      exact RingOfIntegers.isIntegral_coe (z a)
  rw [this]
  exact (Module.Finite.fg_top).map f

theorem gaussL_span : Submodule.span ℚ (gaussL : Set (Fin 2 → Em)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  obtain ⟨p0, q0, h0⟩ := exists_rat (x 0)
  obtain ⟨p1, q1, h1⟩ := exists_rat (x 1)
  have hx : x = p0 • (Pi.single 0 (1 : Em) : Fin 2 → Em) + q0 • (Pi.single 0 ζ : Fin 2 → Em) +
      (p1 • (Pi.single 1 (1 : Em) : Fin 2 → Em) + q1 • (Pi.single 1 ζ : Fin 2 → Em)) := by
    funext b
    fin_cases b
    · simp [h0, qsmul_eq]
    · simp [h1, qsmul_eq]
  have m : ∀ (a : Fin 2) (v : Em), IsIntegral ℤ v → Pi.single a v ∈ Submodule.span ℚ (gaussL : Set (Fin 2 → Em)) :=
    fun a v hv => Submodule.subset_span (single_mem a hv)
  rw [hx]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (m 0 1 isIntegral_one))
    (Submodule.smul_mem _ _ (m 0 ζ ζ_isIntegral)))
    (add_mem (Submodule.smul_mem _ _ (m 1 1 isIntegral_one)) (Submodule.smul_mem _ _ (m 1 ζ ζ_isIntegral)))

theorem cc_isIntegral {v : Em} (hv : IsIntegral ℤ v) : IsIntegral ℤ (cc v) :=
  hv.map (cc : Em →+* Em).toIntAlgHom

theorem gauss_selfDual (x : Fin 2 → Em) :
    x ∈ gaussL ↔ ∀ y ∈ gaussL, ∃ m : ℤ, trForm Em (ζ / 2) gaussH x y = m := by
  constructor
  · intro hx y hy
    unfold trForm
    rw [hermForm_gauss]
    exact trace_of_integral (((cc_isIntegral (hx 0)).mul (hy 0)).sub ((cc_isIntegral (hx 1)).mul (hy 1)))
  · intro h
    have hv : ∀ (a : Fin 2) (v : Em), IsIntegral ℤ v → ∃ m : ℤ, trForm Em (ζ / 2) gaussH x (Pi.single a v) = m :=
      fun a v hv => h _ (single_mem a hv)
    have i0 : IsIntegral ℤ (cc (x 0)) := by
      refine integral_of_trace ?_ ?_
      · obtain ⟨m, hm⟩ := hv 0 1 isIntegral_one
        exact ⟨m, by simpa [trForm, hermForm_gauss] using hm⟩
      · obtain ⟨m, hm⟩ := hv 0 ζ ζ_isIntegral
        exact ⟨m, by simpa [trForm, hermForm_gauss] using hm⟩
    have i1 : IsIntegral ℤ (-cc (x 1)) := by
      refine integral_of_trace ?_ ?_
      · obtain ⟨m, hm⟩ := hv 1 1 isIntegral_one
        exact ⟨m, by simpa [trForm, hermForm_gauss] using hm⟩
      · obtain ⟨m, hm⟩ := hv 1 ζ ζ_isIntegral
        exact ⟨m, by simpa [trForm, hermForm_gauss, neg_mul] using hm⟩
    intro a
    fin_cases a
    · simpa using cc_isIntegral i0
    · simpa using cc_isIntegral i1.neg

theorem gauss_signature :
    (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * gaussH.map φ₀ * 1 = signMat 2 1 := by
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gaussH, signMat, Matrix.diagonal]

def gaussDatum : HermDatum Em Unit 2 1 where
  emb _ := φ₀
  emb_inj _ _ _ := rfl
  cmType := cmType
  H := gaussH
  herm a b := by
    fin_cases a <;> fin_cases b <;> simp [gaussH]
  ξ := ζ / 2
  ξ_ne := div_ne_zero (hζ.ne_zero (by norm_num)) two_ne_zero
  ξ_conj := by rw [map_div₀, cc_ζ, map_ofNat, neg_div]
  L := gaussL
  fg := gaussL_fg
  span := gaussL_span
  selfDual := gauss_selfDual
  signature _ := ⟨1, by simp, gauss_signature⟩
  level := 3
  three_le_level := le_rfl

end GroundTheory.Heights₂.Heights.NineStatements.Gauss
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Twist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix ComplexOrder

section Bundle

variable {Ω' : Type} [Field Ω'] {κ : Type}

def twistLat (x : κ → Ω') (i : κ) : AddSubgroup (Fin 2 → Ω') where
  carrier := {e | e 0 ∈ chartRing ℤ x i ∧ x i * e 1 ∈ chartRing ℤ x i}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [Pi.add_apply, mul_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [Pi.zero_apply, mul_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [Pi.neg_apply, mul_neg]; exact neg_mem ha.2⟩

def twW (x : κ → Ω') (i : κ) (q : Fin 2) : Ω' := if q = 0 then 1 else (x i)⁻¹

def twistVec (x : κ → Ω') (i : κ) (q : Fin 2) : Fin 2 → Ω' := twW x i q • Pi.single q 1

theorem sum_twistVec (x : κ → Ω') (i : κ) (a : Fin 2 → Ω') :
    ∑ q, a q • twistVec x i q = fun p => a p * twW x i p := by
  funext p
  fin_cases p <;> simp [twistVec, Fin.sum_univ_two, twW]

theorem twW_ne_zero {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (q : Fin 2) : twW x i q ≠ 0 := by
  unfold twW
  split_ifs
  · exact one_ne_zero
  · exact inv_ne_zero hi

def twistBasis {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) : Module.Basis (Fin 2) Ω' (Fin 2 → Ω') :=
  (Pi.basisFun Ω' (Fin 2)).isUnitSMul (w := twW x i) fun q => (twW_ne_zero hi q).isUnit

theorem twistBasis_apply {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (q : Fin 2) :
    twistBasis hi q = twistVec x i q := by
  rw [twistBasis, Module.Basis.isUnitSMul_apply, Pi.basisFun_apply]
  rfl

theorem twistVec_linearIndependent {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) :
    LinearIndependent Ω' (twistVec x i) := by
  have := (twistBasis hi).linearIndependent
  rwa [show ⇑(twistBasis hi) = twistVec x i from funext (twistBasis_apply hi)] at this

theorem twistVec_span {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) :
    Submodule.span Ω' (Set.range (twistVec x i)) = ⊤ := by
  have := (twistBasis hi).span_eq
  rwa [show ⇑(twistBasis hi) = twistVec x i from funext (twistBasis_apply hi)] at this

theorem twist_frame_iff {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (e : Fin 2 → Ω') :
    (∃ n : ℕ, (1 : Ω') ^ n • e ∈ twistLat x i) ↔
      ∃ a : Fin 2 → Ω', (∀ q, ∃ n : ℕ, (1 : Ω') ^ n * a q ∈ chartRing ℤ x i) ∧
        e = ∑ q, a q • twistVec x i q := by
  simp only [one_pow, one_smul, one_mul, exists_const, sum_twistVec]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun q => if q = 0 then e 0 else x i * e 1, fun q => ?_, ?_⟩
    · fin_cases q
      · simpa using h0
      · simpa using h1
    · funext p
      fin_cases p
      · simp [twW]
      · simp [twW]
        field_simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨by simpa [twW] using ha 0, ?_⟩
    have h1 : x i * (a 1 * twW x i 1) = a 1 := by
      simp only [twW, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      field_simp
    rw [h1]
    simpa using ha 1

def twistBundle (x : κ → Ω') : ChartBundle ℤ x 2 (Fin 2 → Ω') where
  lat := twistLat x
  stable i a ha e he := ⟨by simpa [smul_eq_mul] using mul_mem ha he.1,
    by simpa [smul_eq_mul, mul_left_comm] using mul_mem ha he.2⟩
  frame i hi := ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp,
    fun _ => ⟨twistVec x i, twistVec_linearIndependent hi, twistVec_span hi, twist_frame_iff hi⟩⟩
  overlap i j hi hj e he := by
    obtain ⟨m0, hm0⟩ := exists_pow_mul_mem_chartRing (o := ℤ) x i j hi he.1
    obtain ⟨m1, hm1⟩ := exists_pow_mul_mem_chartRing (o := ℤ) x i j hi he.2
    have hij : x i / x j ∈ chartRing ℤ x j := div_mem_chartRing x j i
    set r := x i / x j with hr
    refine ⟨m0 + m1 + 1, ?_, ?_⟩
    · have : (r ^ (m0 + m1 + 1) • e) 0 = r ^ (m1 + 1) * (r ^ m0 * e 0) := by
        rw [Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      exact mul_mem (pow_mem hij _) hm0
    · have hxx : x j * r = x i := mul_div_cancel₀ _ hj
      have : x j * (r ^ (m0 + m1 + 1) • e) 1 = r ^ m0 * (r ^ m1 * (x i * e 1)) := by
        rw [Pi.smul_apply, smul_eq_mul, ← hxx]
        ring
      rw [this]
      exact mul_mem (pow_mem hij _) hm1

end Bundle

abbrev ch (l : Fin 2) : Unit → Fin 2 := fun _ => l

theorem segreCoord_ch (l : Fin 2) : segreCoord yLine (ch l) = yLine ⟨(), l⟩ := by
  simp [segreCoord]

def tautSq (l : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) : ℝ :=
  (‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2) / ‖z ⟨(), l⟩‖ ^ 2

theorem tautSq_pos {l : Fin 2} {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ⟨(), l⟩ ≠ 0) : 0 < tautSq l z := by
  have hl : 0 < ‖z ⟨(), l⟩‖ ^ 2 := by positivity
  have : ‖z ⟨(), l⟩‖ ^ 2 ≤ ‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2 := by
    fin_cases l
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖z ⟨(), 1⟩‖]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖z ⟨(), 0⟩‖]
  exact div_pos (lt_of_lt_of_le hl this) hl

def twistGram (l : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, (tautSq l z : ℂ)]

theorem tautSq_chart (a : Fin 2) (t : Fin 1 → ℂ) : tautSq a (chartMap a t) = 1 + 4 * ‖t 0‖ ^ 2 := by
  fin_cases a <;> simp [tautSq, chartMap_apply] <;> ring

theorem isValueAt_ratio (l l' : Fin 2) {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ⟨(), l'⟩ ≠ 0) :
    IsValueAt yLine (yLine ⟨(), l⟩ / yLine ⟨(), l'⟩) z (z ⟨(), l⟩ / z ⟨(), l'⟩) := by
  have h := isMultiHomog_prod_X (ι := PBlk 2) (ch l)
  have h' := isMultiHomog_prod_X (ι := PBlk 2) (ch l')
  refine ⟨fun _ => 1, ∏ k, X ⟨k, ch l k⟩, ∏ k, X ⟨k, ch l' k⟩, h, h', ?_, ?_, ?_, ?_⟩
  · simpa using yLine_ne_zero ⟨(), l'⟩
  · simp only [aeval_X, Fintype.prod_unique]
    exact (div_mul_cancel₀ _ (yLine_ne_zero _)).symm
  · simpa using hz
  · simp

theorem contDiff_chartMap {n : WithTop ℕ∞} (a p : Fin 2) :
    ContDiff ℝ n (fun t : Fin 1 → ℂ => chartMap a t ⟨(), p⟩) := by
  have : (fun t : Fin 1 → ℂ => chartMap a t ⟨(), p⟩) = fun t => if p = a then 1 else 2 * t 0 := by
    funext t
    simp only [chartMap_apply]
  rw [this]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const.mul (contDiff_apply ℝ ℂ (0 : Fin 1))

theorem contDiffAt_tautSq {n : WithTop ℕ∞} (l a : Fin 2) (t : Fin 1 → ℂ) (hz : chartMap a t ⟨(), l⟩ ≠ 0) :
    ContDiffAt ℝ n (fun t' => tautSq l (chartMap a t')) t := by
  have hn : ∀ p : Fin 2, ContDiff ℝ n (fun t' : Fin 1 → ℂ => ‖chartMap a t' ⟨(), p⟩‖ ^ 2) :=
    fun p => (contDiff_norm_sq ℝ).comp (contDiff_chartMap a p)
  exact (((hn 0).add (hn 1)).contDiffAt).div (hn l).contDiffAt (by positivity)

theorem inv_diag2 (s : ℝ) (hs : s ≠ 0) :
    (Matrix.diagonal ![(1 : ℂ), (s : ℂ)])⁻¹ = Matrix.diagonal ![(1 : ℂ), ((s⁻¹ : ℝ) : ℂ)] := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hs]

theorem psd_diag2 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (Matrix.diagonal ![(u : ℂ), (v : ℂ)]).PosSemidef := by
  refine Matrix.PosSemidef.diagonal fun i => ?_
  fin_cases i
  · simpa using Complex.zero_le_real.2 hu
  · simpa using Complex.zero_le_real.2 hv

theorem diagonal_two_sub_smul_one (s c : ℝ) :
    Matrix.diagonal ![(1 : ℂ), ((s : ℝ) : ℂ)] - ((c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![((1 - c : ℝ) : ℂ), ((s - c : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sub_diag2 (C s : ℝ) :
    ((C : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Matrix.diagonal ![(1 : ℂ), ((s : ℝ) : ℂ)] =
      Matrix.diagonal ![((C - 1 : ℝ) : ℂ), ((C - s : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem norm_fderiv_taut (t : Fin 1 → ℂ) (ht : ‖t‖ < 1) :
    ‖fderiv ℝ (fun t' : Fin 1 → ℂ => (((1 + 4 * ‖t' 0‖ ^ 2 : ℝ)) : ℂ)) t‖ ≤ 8 := by
  have h1 : HasFDerivAt (fun t' : Fin 1 → ℂ => t' 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0) t := hasFDerivAt_apply 0 t
  have h2 := (h1.norm_sq.const_mul (4 : ℝ)).const_add 1
  have h3 : HasFDerivAt (fun t' : Fin 1 → ℂ => (((1 + 4 * ‖t' 0‖ ^ 2 : ℝ)) : ℂ)) _ t :=
    Complex.ofRealCLM.hasFDerivAt.comp t h2
  rw [h3.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hp : ‖(innerSL ℝ (t 0)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)‖ ≤ ‖t 0‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (norm_nonneg _))
  have ht0 : ‖t 0‖ ≤ 1 := (norm_le_pi_norm t 0).trans ht.le
  rw [Complex.ofRealCLM_norm, one_mul, norm_smul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
  norm_num
  nlinarith [norm_nonneg ((innerSL ℝ (t 0)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0))]

def twistMetric : HermMetric yLine (twistBundle (segreCoord yLine))
    (mcPts (mCoordIdeal yLine) \ ∅) lineChart where
  m := 2
  chart l := ch l
  fr _ := 1
  b l := twistVec (segreCoord yLine) (ch l)
  isFrame l := ⟨segreCoord_line_ne_zero l, one_mem _, one_ne_zero,
    twistVec_linearIndependent (segreCoord_line_ne_zero l), twist_frame_iff (segreCoord_line_ne_zero l)⟩
  gram := twistGram
  cover z hz := by
    obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz.1
    exact ⟨i, inFrameDomain_line hi⟩
  posDef l z _ hl := by
    rw [twistGram, Matrix.posDef_diagonal_iff]
    intro p
    fin_cases p
    · simp
    · simpa using Complex.zero_lt_real.2 (tautSq_pos (hl.1 ()))
  compat l l' z hz hl hl' S hS Sz hSz := by
    have hzl : z ⟨(), l⟩ ≠ 0 := hl.1 ()
    have hzl' : z ⟨(), l'⟩ ≠ 0 := hl'.1 ()
    have hy : ∀ p : Fin 2, yLine ⟨(), p⟩ ≠ 0 := fun p => yLine_ne_zero _

    have hS' : ∀ p q, twW (segreCoord yLine) (ch l') q * (Pi.single q 1 : Fin 2 → Ω) p =
        S p q * twW (segreCoord yLine) (ch l) p := by
      intro p q
      have h := congrFun (hS q) p
      rw [sum_twistVec] at h
      simpa only [twistVec, Pi.smul_apply, smul_eq_mul] using h
    have hw : ∀ p, twW (segreCoord yLine) (ch l) p ≠ 0 := twW_ne_zero (segreCoord_line_ne_zero l)
    have n10 : (1 : Fin 2) ≠ 0 := by decide
    have e00 : S 0 0 = 1 := by
      have h := hS' 0 0
      simp only [twW, ↓reduceIte, Pi.single_eq_same, mul_one] at h
      exact h.symm
    have e10 : S 1 0 = 0 := by
      have h := hS' 1 0
      simp only [twW, ↓reduceIte, if_neg n10, Pi.single_eq_of_ne n10, mul_zero, segreCoord_ch] at h
      exact (mul_eq_zero.1 h.symm).resolve_right (inv_ne_zero (hy l))
    have e01 : S 0 1 = 0 := by
      have h := hS' 0 1
      simp only [twW, ↓reduceIte, if_neg n10, Pi.single_eq_of_ne n10.symm, mul_zero, mul_one] at h
      exact h.symm
    have e11 : S 1 1 = yLine ⟨(), l⟩ / yLine ⟨(), l'⟩ := by
      have h := hS' 1 1
      simp only [twW, if_neg n10, Pi.single_eq_same, mul_one, segreCoord_ch] at h
      calc
        S 1 1 = S 1 1 * (yLine ⟨(), l⟩)⁻¹ * yLine ⟨(), l⟩ := by rw [inv_mul_cancel_right₀ (hy l)]
        _ = yLine ⟨(), l⟩ / yLine ⟨(), l'⟩ := by rw [← h, div_eq_inv_mul]
    have v00 : Sz 0 0 = 1 := isValueAt_one hz.1 (e00 ▸ hSz 0 0)
    have v10 : Sz 1 0 = 0 := isValueAt_zero hz.1 (e10 ▸ hSz 1 0)
    have v01 : Sz 0 1 = 0 := isValueAt_zero hz.1 (e01 ▸ hSz 0 1)
    have v11 : Sz 1 1 = z ⟨(), l⟩ / z ⟨(), l'⟩ :=
      isValueAt_unique hz.1 (e11 ▸ hSz 1 1) (isValueAt_ratio l l' hzl')
    have key : (tautSq l' z : ℂ) = starRingEnd ℂ (z ⟨(), l⟩ / z ⟨(), l'⟩) * (tautSq l z : ℂ) *
        (z ⟨(), l⟩ / z ⟨(), l'⟩) := by
      have h1 : starRingEnd ℂ (z ⟨(), l⟩ / z ⟨(), l'⟩) * (tautSq l z : ℂ) * (z ⟨(), l⟩ / z ⟨(), l'⟩) =
          ((Complex.normSq (z ⟨(), l⟩ / z ⟨(), l'⟩) * tautSq l z : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
        ring
      rw [h1, Complex.normSq_eq_norm_sq, norm_div]
      congr 1
      have a1 : ‖z ⟨(), l⟩‖ ≠ 0 := norm_ne_zero_iff.2 hzl
      have a2 : ‖z ⟨(), l'⟩‖ ≠ 0 := norm_ne_zero_iff.2 hzl'
      simp only [tautSq]
      field_simp
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [twistGram, Matrix.mul_apply, Fin.sum_univ_two, v00, v10, v01, v11, key]
  torus l z _ _ c hc := by
    have hc0 : ‖c ()‖ ^ 2 ≠ 0 := by have := hc (); positivity
    simp only [twistGram, tautSq, torusSmul, norm_mul, mul_pow]
    rw [← mul_add, mul_div_mul_left _ _ hc0]
  conj l z _ _ := by
    have : tautSq l (conjVec z) = tautSq l z := by simp [tautSq, conjVec]
    rw [twistGram, twistGram, this, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext p
    fin_cases p <;> simp
  smooth a l t _ _ hd p q := by
    have hz : chartMap a t ⟨(), l⟩ ≠ 0 := hd.1 ()
    fin_cases p <;> fin_cases q
    · simp [twistGram]
      exact contDiffAt_const
    · simp [twistGram]
      exact contDiffAt_const
    · simp [twistGram]
      exact contDiffAt_const
    · simp only [twistGram, lineChart_γ, Fin.mk_one, Matrix.diagonal_apply_eq, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp t (contDiffAt_tautSq l a t hz)
  logBound a t₀ _ := by
    refine ⟨a, inFrameDomain_line (by rw [lineChart_γ, chartMap_apply, if_pos rfl]; exact one_ne_zero),
      1, one_pos, 1 / 5, by norm_num, 8, by norm_num, fun t _ ht _ _ => ?_⟩
    have ht0 : ‖t 0‖ ≤ ‖t‖ := norm_le_pi_norm t 0
    have hg : twistGram a ((lineChart a).γ t) = Matrix.diagonal ![(1 : ℂ), ((1 + 4 * ‖t 0‖ ^ 2 : ℝ) : ℂ)] := by
      rw [twistGram, lineChart_γ, tautSq_chart]
    have hs : (1 : ℝ) ≤ 1 + 4 * ‖t 0‖ ^ 2 := by nlinarith [norm_nonneg (t 0)]
    have hs5 : 1 + 4 * ‖t 0‖ ^ 2 ≤ (5 : ℝ) := by nlinarith [norm_nonneg (t 0)]
    rw [hg, inv_diag2 _ (by linarith), logR_lineChart]
    refine ⟨?_, ?_, fun p q => ?_⟩
    · rw [diagonal_two_sub_smul_one]
      refine psd_diag2 _ _ (by norm_num) ?_
      rw [sub_nonneg, le_inv_comm₀ (by norm_num) (by linarith)]
      linarith
    · rw [sub_diag2]
      have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      refine psd_diag2 _ _ (by nlinarith) ?_
      have : (1 + 4 * ‖t 0‖ ^ 2)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hs
      nlinarith
    · have hC : (8 : ℝ) ≤ 8 * Real.exp (Real.exp 1 / 2) := by
        have := Real.one_le_exp (show (0 : ℝ) ≤ Real.exp 1 / 2 by positivity)
        nlinarith
      refine le_trans ?_ hC
      fin_cases p <;> fin_cases q
      · simp [twistGram, lineChart_γ]
      · simp [twistGram, lineChart_γ]
      · simp [twistGram, lineChart_γ]
      · have hf : (fun t' => twistGram a ((lineChart a).γ t') 1 1) =
            fun t' : Fin 1 → ℂ => (((1 + 4 * ‖t' 0‖ ^ 2 : ℝ)) : ℂ) := by
          funext t'
          simp [twistGram, lineChart_γ, tautSq_chart]
        simp only [Fin.mk_one]
        rw [hf]
        exact norm_fderiv_taut t ht

end GroundTheory.Heights₂.Heights.NineStatements.Twist
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.LowerBoundFree.Line GroundTheory.Heights₂.Heights.NineStatements.Twist
open scoped Matrix

namespace LineFuller

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def twistData : ComponentData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  { lineData II hII with
    W := fun _ => twistBundle (segreCoord yLine)
    h := fun _ => twistMetric }

theorem twistVec_image (c : Unit → Fin 2) :
    twistVec (segreCoord yLine) c '' {i : Fin 2 | (i : ℕ) < 1} = {Pi.single 0 1} := by
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp hi)]
    simp [twistVec, twW]
  · rintro rfl
    exact ⟨0, by simp, by simp [twistVec, twW]⟩

theorem isFrameOver_twist {c : Unit → Fin 2} (hc : segreCoord yLine c ≠ 0) :
    IsFrameOver yLine (twistBundle (segreCoord yLine)) c 1 (twistVec (segreCoord yLine) c) :=
  ⟨hc, one_mem _, one_ne_zero, twistVec_linearIndependent hc, twist_frame_iff hc⟩

theorem isSubbundle_twist : IsSubbundle yLine (twistBundle (segreCoord yLine)) lineF 1 := by
  intro c hc
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ _ => ?_⟩
  refine ⟨twistVec (segreCoord yLine) c, isFrameOver_twist hc, ?_⟩
  rw [twistVec_image]
  rfl

def twistDataHodge : ComponentDataHodge II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) where
  toComponentData := twistData II hII
  F _ := lineF
  hodge _ := isSubbundle_twist

theorem ιMulti_const_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (n : ℕ) (r : K) (v : M) :
    exteriorPower.ιMulti K n (fun _ => r • v) = r ^ n • exteriorPower.ιMulti K n (fun _ => v) := by
  have h := AlternatingMap.map_smul_univ (exteriorPower.ιMulti K n) (fun _ => r) (fun _ => v)
  simpa [Finset.prod_const] using h

theorem tprod_unit_scale {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (x : K) (hx : x ≠ 0) (v : M) :
    PiTensorProduct.tprod K (fun _ : Unit => v) =
      (1 * x) • PiTensorProduct.tprod K (fun _ : Unit => (x⁻¹) ^ (2 - 1) • v) := by
  have h := MultilinearMap.map_smul_univ (PiTensorProduct.tprod K (s := fun _ : Unit => M))
    (fun _ => (x⁻¹) ^ (2 - 1)) (fun _ => v)
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  rw [h, smul_smul]
  norm_num [hx]

set_option synthInstance.maxHeartbeats 400000 in

theorem tprod_unit_scale' {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (x y : K) (hxy : y = x)
    (hx : x ≠ 0) (v w : M) (hw : w = (x⁻¹) ^ (2 - 1) • v) :
    PiTensorProduct.tprod K (fun _ : Unit => v) = (1 * y) • PiTensorProduct.tprod K (fun _ : Unit => w) := by
  subst hxy
  subst hw
  exact tprod_unit_scale y hx v

def eBar : ⋀[Ω]^(2 - 1) ((Fin 2 → Ω) ⧸ lineF) := exteriorPower.ιMulti Ω (2 - 1) fun _ => lineF.mkQ (Pi.single 1 1)

set_option synthInstance.maxHeartbeats 400000 in
theorem quotWedge_twist (c : Unit → Fin 2) (hj : 1 ≤ 2) :
    quotWedge lineF hj (twistVec (segreCoord yLine) c) = (segreCoord yLine c)⁻¹ ^ (2 - 1) • eBar := by
  have hv : ∀ a : Fin (2 - 1), lineF.mkQ (twistVec (segreCoord yLine) c (tailIdx hj a)) =
      (segreCoord yLine c)⁻¹ • lineF.mkQ (Pi.single 1 1) := by
    intro a
    have ha : tailIdx hj a = 1 := Fin.ext (by have := a.isLt; simp only [tailIdx]; omega)
    rw [ha, twistVec, twW, if_neg (by decide), map_smul]
  unfold quotWedge eBar
  rw [← ιMulti_const_smul]
  congr 1
  funext a
  exact hv a

theorem headIdx_range (c : Unit → Fin 2) (hj : 1 ≤ 2) :
    Set.range (twistVec (segreCoord yLine) c ∘ headIdx hj) = {Pi.single 0 1} := by
  ext v
  simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Fin.fin_one_eq_zero a]
    simp [headIdx, twistVec, twW]
  · rintro rfl
    exact ⟨0, by simp [headIdx, twistVec, twW]⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem twistMu_eq (c : Unit → Fin 2) (hc : segreCoord yLine c ≠ 0) :
    (PiTensorProduct.tprod Ω fun _ : Unit => eBar) = (1 * chartMono yLine c 1) •
      PiTensorProduct.tprod Ω fun _ : Unit => quotWedge lineF (show 1 ≤ 2 by decide) (twistVec (segreCoord yLine) c) := by
  have hx : chartMono yLine c 1 = segreCoord yLine c := by
    simp [chartMono, segreCoord]
  exact tprod_unit_scale' _ _ hx hc eBar _ (quotWedge_twist c _)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def twistMu : HodgeData (twistData II hII) where
  F _ := lineF
  aMu := 1
  Λ := PiTensorProduct.tprod Ω fun _ => eBar
  locally c hc := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨fun _ => twistVec (segreCoord yLine) c, fun _ => ⟨isFrameOver_twist hc, twistVec_span hc, ?_⟩,
      1, isUnitOn_one _ _ _, ?_⟩
    · show Submodule.span Ω (Set.range (twistVec (segreCoord yLine) c ∘ headIdx (show 1 ≤ 2 by decide))) = lineF
      rw [headIdx_range]
      rfl
    · exact twistMu_eq c hc

def lineFuller : FullerData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) Gauss.Em where
  toComponentDataHodge := twistDataHodge II hII
  herm := Gauss.gaussDatum
  per _ _ := 1
  per_witt _ _ _ := Gauss.gauss_signature
  per_torus _ _ _ := rfl
  nStrata := 0
  stratum := Fin.elim0
  stratum_sub s := s.elim0
  stratum_cover _ h := absurd h (Set.notMem_empty _)
  stratum_torus s := s.elim0
  torLat := Fin.elim0
  torLat_le s := s.elim0
  torLat_ne s := s.elim0
  torLat_iso s := s.elim0
  torLat_sat s := s.elim0
  nz_near s := s.elim0
  mu := twistMu II hII
  mu_F _ := rfl
  htLat _ _ := twistBundle (segreCoord yLine)
  ht_away _ h := absurd h (Finset.notMem_empty _)

def lineFullerZero : FullerData zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) Gauss.Em :=
  lineFuller zeroSystem fun _ _ => le_rfl




end LineFuller

end GroundTheory.Heights₂.Heights.NineStatements
end
end
