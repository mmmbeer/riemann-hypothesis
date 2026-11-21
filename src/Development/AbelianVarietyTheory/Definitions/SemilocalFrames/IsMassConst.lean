import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners

section
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc MeasureTheory

namespace GlobalTheory.SgGlob.LocModel

section Alg
variable {K B : Type} [Field K] [ValuativeRel K] [CommRing B] [Algebra K B]

structure IsUnitGen (cj : B ≃ₐ[K] B) (θ : B) (t n : K) : Prop where
  inj : Function.Injective (algebraMap K B)
  gen : ∀ x : B, ∃ a b : K, x = algebraMap K B a + algebraMap K B b * θ
  tr : θ + cj θ = algebraMap K B t
  nm : θ * cj θ = algebraMap K B n
  t_int : t ∈ 𝒪[K]
  n_int : n ∈ 𝒪[K]
  disc_ne : t ^ 2 - 4 * n ≠ 0
  disc_inv : (t ^ 2 - 4 * n)⁻¹ ∈ 𝒪[K]

theorem int_algebraMap {a : K} (ha : a ∈ 𝒪[K]) : IsIntegral 𝒪[K] (algebraMap K B a) :=
  (isIntegral_algebraMap (R := 𝒪[K]) (A := K) (x := ⟨a, ha⟩)).algebraMap

theorem mem_of_int {a : K} (ha : IsIntegral 𝒪[K] a) : a ∈ 𝒪[K] := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪[K]) (K := K)).1 ha
  rw [← hy]; exact y.2

theorem int_cj (cj : B ≃ₐ[K] B) {x : B} (hx : IsIntegral 𝒪[K] x) : IsIntegral 𝒪[K] (cj x) :=
  hx.map (cj.restrictScalars 𝒪[K]).toAlgHom

namespace IsUnitGen
variable {cj : B ≃ₐ[K] B} {θ : B} {t n : K} (h : IsUnitGen cj θ t n)
include h

theorem mem_of_int' {a : K} (ha : IsIntegral 𝒪[K] (algebraMap K B a)) : a ∈ 𝒪[K] :=
  mem_of_int ((isIntegral_algebraMap_iff h.inj).1 ha)

theorem cj_gen : cj θ = algebraMap K B t - θ := by rw [← h.tr]; ring

theorem delta_sq : (θ - cj θ) ^ 2 = algebraMap K B (t ^ 2 - 4 * n) := by
  simp only [map_sub, map_pow, map_mul, map_ofNat, ← h.tr, ← h.nm]; ring

theorem cj_cj (x : B) : cj (cj x) = x := by
  obtain ⟨a, b, rfl⟩ := h.gen x
  simp only [map_add, map_mul, AlgEquiv.commutes]
  rw [h.cj_gen, map_sub, AlgEquiv.commutes, h.cj_gen]; ring

theorem sub_cj (a b : K) : (algebraMap K B a + algebraMap K B b * θ - cj (algebraMap K B a + algebraMap K B b * θ))
    * (θ - cj θ) = algebraMap K B (b * (t ^ 2 - 4 * n)) := by
  rw [map_mul (algebraMap K B) b, ← h.delta_sq]
  simp only [map_add, map_mul, AlgEquiv.commutes]; ring

theorem cj_fix (x : B) : cj x = x ↔ ∃ a : K, algebraMap K B a = x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := h.gen x
    have e := h.sub_cj a b
    rw [hx, sub_self, zero_mul, ← map_zero (algebraMap K B)] at e
    have hb : b = 0 := (mul_eq_zero.1 (h.inj e).symm).resolve_right h.disc_ne
    exact ⟨a, by simp [hb]⟩
  · rintro ⟨a, rfl⟩; exact cj.commutes a

theorem int_gen : IsIntegral 𝒪[K] θ := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨t, h.t_int⟩ * Polynomial.X + Polynomial.C ⟨n, h.n_int⟩, by monicity!, ?_⟩
  have e1 : algebraMap 𝒪[K] B ⟨t, h.t_int⟩ = algebraMap K B t := rfl
  have e2 : algebraMap 𝒪[K] B ⟨n, h.n_int⟩ = algebraMap K B n := rfl
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, e1, e2, ← h.tr, ← h.nm]
  ring

theorem int_delta : IsIntegral 𝒪[K] (θ - cj θ) := h.int_gen.sub (int_cj cj h.int_gen)

theorem mem_of_mul_disc {b : K} (hb : b * (t ^ 2 - 4 * n) ∈ 𝒪[K]) : b ∈ 𝒪[K] := by
  have := mul_mem hb h.disc_inv
  rwa [mul_inv_cancel_right₀ h.disc_ne] at this

theorem int_iff (a b : K) : IsIntegral 𝒪[K] (algebraMap K B a + algebraMap K B b * θ) ↔ a ∈ 𝒪[K] ∧ b ∈ 𝒪[K] := by
  constructor
  · intro hx
    have hb : b ∈ 𝒪[K] := by
      apply h.mem_of_mul_disc
      apply h.mem_of_int'
      rw [← h.sub_cj a b]
      exact (hx.sub (int_cj cj hx)).mul h.int_delta
    refine ⟨h.mem_of_int' ?_, hb⟩
    have := hx.sub ((int_algebraMap hb).mul h.int_gen)
    simpa using this
  · rintro ⟨ha, hb⟩
    exact (int_algebraMap ha).add ((int_algebraMap hb).mul h.int_gen)

theorem reduced : IsReduced B := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨a, b, rfl⟩ := h.gen x
  have h1 : IsNilpotent (algebraMap K B (b * (t ^ 2 - 4 * n))) := by
    rw [← h.sub_cj a b]
    exact (Commute.all _ _).isNilpotent_mul_right ((Commute.all _ _).isNilpotent_sub hx (hx.map cj))
  have hb : b = 0 := (mul_eq_zero.1 ((IsNilpotent.map_iff h.inj).1 h1).eq_zero).resolve_right h.disc_ne
  subst hb
  simp only [map_zero, zero_mul, add_zero] at hx ⊢
  rw [((IsNilpotent.map_iff h.inj).1 hx).eq_zero, map_zero]

theorem trace_eq [CharZero K] (hr : Module.finrank K B = 2) (x : B) :
    algebraMap K B (Algebra.trace K B x) = x + cj x := by
  have h1 : ∀ a : K, Algebra.trace K B (algebraMap K B a) = 2 * a := fun a => by
    rw [Algebra.trace_algebraMap, hr]; simp
  have h2 : Algebra.trace K B θ = t := by
    have e := congrArg (Algebra.trace K B) h.tr
    rw [map_add, Algebra.trace_eq_of_algEquiv cj, h1] at e
    linear_combination e / 2
  obtain ⟨a, b, rfl⟩ := h.gen x
  rw [map_add, h1, ← Algebra.smul_def, map_smul, h2, Algebra.smul_def, Algebra.smul_def]
  simp only [map_add, map_mul, AlgEquiv.commutes, map_ofNat, Algebra.algebraMap_self, RingHom.id_apply, ← h.tr]
  ring

theorem trace_dual [CharZero K] (hr : Module.finrank K B = 2) (x : B) :
    (∀ y : B, IsIntegral 𝒪[K] y → Algebra.trace K B (x * y) ∈ 𝒪[K]) ↔ IsIntegral 𝒪[K] x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := h.gen x
    rw [h.int_iff]
    have e1 := h.trace_eq hr ((algebraMap K B a + algebraMap K B b * θ) * (θ - cj θ))
    have e2 := h.trace_eq hr ((algebraMap K B a + algebraMap K B b * θ) * (cj θ * (θ - cj θ)))
    have f1 : Algebra.trace K B ((algebraMap K B a + algebraMap K B b * θ) * (θ - cj θ)) = b * (t ^ 2 - 4 * n) := by
      apply h.inj
      rw [e1, map_mul (algebraMap K B) b, ← h.delta_sq]
      simp only [map_add, map_mul, map_sub, AlgEquiv.commutes, h.cj_cj]; ring
    have f2 : Algebra.trace K B ((algebraMap K B a + algebraMap K B b * θ) * (cj θ * (θ - cj θ)))
        = (-a) * (t ^ 2 - 4 * n) := by
      apply h.inj
      rw [e2, map_mul (algebraMap K B) (-a), ← h.delta_sq]
      simp only [map_add, map_mul, map_sub, map_neg, AlgEquiv.commutes, h.cj_cj]; ring
    have g1 := hx _ h.int_delta
    have g2 := hx _ ((int_cj cj h.int_gen).mul h.int_delta)
    rw [f1] at g1; rw [f2] at g2
    exact ⟨by simpa using neg_mem (h.mem_of_mul_disc g2), h.mem_of_mul_disc g1⟩
  · intro hx y hy
    apply h.mem_of_int'
    rw [h.trace_eq hr]
    exact (hx.mul hy).add (int_cj cj (hx.mul hy))

theorem unram (O : Subring B) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[K] x) (ϖ : 𝒪[K]) (hϖ : Prime ϖ) (x : B) (hx : x ∈ O)
    (hxx : x * x ∈ Submodule.span O {algebraMap K B ϖ}) : x ∈ Submodule.span O {algebraMap K B ϖ} := by
  have hϖ0 : (ϖ : K) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have key : ∀ (c : K) (hc : c ∈ 𝒪[K]) (z : B), IsIntegral 𝒪[K] z → algebraMap K B c = z * algebraMap K B ϖ →
      ϖ ∣ ⟨c, hc⟩ := by
    intro c hc z hz e
    have : z = algebraMap K B (c / ϖ) := by
      rw [div_eq_mul_inv, map_mul, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, mul_one]
    rw [this] at hz
    refine ⟨⟨c / ϖ, h.mem_of_int' hz⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul]; field_simp
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hxx
  have hz' : (z : B) * algebraMap K B ϖ = x * x := hz
  have hzi := (hO z).1 z.2
  have hxi := (hO x).1 hx
  obtain ⟨a, b, hab⟩ := h.gen x
  obtain ⟨ha, hb⟩ := (h.int_iff a b).1 (hab ▸ hxi)
  have hcz : cj z * algebraMap K B ϖ = cj x * cj x := by
    have := congrArg cj hz'
    simpa only [map_mul, AlgEquiv.commutes] using this
  have hd : t ^ 2 - 4 * n ∈ 𝒪[K] := sub_mem (pow_mem h.t_int 2) (mul_mem (by exact_mod_cast natCast_mem 𝒪[K] 4) h.n_int)
  have h3 : IsIntegral 𝒪[K] (3 : B) := by exact_mod_cast (isIntegral_natCast (R := 𝒪[K]) (B := B) 3)
  have h2 : IsIntegral 𝒪[K] (2 : B) := by exact_mod_cast (isIntegral_natCast (R := 𝒪[K]) (B := B) 2)
  have hbd : ϖ ∣ (⟨b * (t ^ 2 - 4 * n), mul_mem hb hd⟩ : 𝒪[K]) := by
    apply hϖ.dvd_of_dvd_pow (n := 3)
    refine key _ (pow_mem (mul_mem hb hd) 3)
      ((z * (x - 3 * cj x) + cj z * (3 * x - cj x)) * (θ - cj θ) ^ 3) ?_ ?_
    · exact ((hzi.mul (hxi.sub (h3.mul (int_cj cj hxi)))).add
        ((int_cj cj hzi).mul ((h3.mul hxi).sub (int_cj cj hxi)))).mul (h.int_delta.pow 3)
    · rw [map_pow, ← h.sub_cj a b, ← hab]
      linear_combination (-(x - 3 * cj x) * (θ - cj θ) ^ 3) * hz' - ((3 * x - cj x) * (θ - cj θ) ^ 3) * hcz
  obtain ⟨b', hb'⟩ : ϖ ∣ (⟨b, hb⟩ : 𝒪[K]) := by
    have := hbd.mul_right ⟨_, h.disc_inv⟩
    convert this using 1
    apply Subtype.ext
    simp only [MulMemClass.mk_mul_mk]
    rw [mul_inv_cancel_right₀ h.disc_ne]
  have eb : algebraMap K B b = algebraMap K B ϖ * algebraMap K B b' := by
    rw [← map_mul]; congr 1; exact congrArg Subtype.val hb'
  obtain ⟨a', ha'⟩ : ϖ ∣ (⟨a, ha⟩ : 𝒪[K]) := by
    apply hϖ.dvd_of_dvd_pow (n := 2)
    refine key _ (pow_mem ha 2) (z - algebraMap K B b' * θ * (2 * x - algebraMap K B b * θ)) ?_ ?_
    · exact hzi.sub (((int_algebraMap b'.2).mul h.int_gen).mul
        ((h2.mul hxi).sub ((int_algebraMap hb).mul h.int_gen)))
    · have ea : algebraMap K B a = x - algebraMap K B b * θ := by rw [hab]; ring
      rw [map_pow, ea]
      linear_combination (-1 : B) * hz' - θ * (2 * x - algebraMap K B b * θ) * eb
  have ea : algebraMap K B a = algebraMap K B ϖ * algebraMap K B a' := by
    rw [← map_mul]; congr 1; exact congrArg Subtype.val ha'
  refine Submodule.mem_span_singleton.2 ⟨⟨algebraMap K B a' + algebraMap K B b' * θ,
    (hO _).2 ((h.int_iff _ _).2 ⟨a'.2, b'.2⟩)⟩, ?_⟩
  change (algebraMap K B a' + algebraMap K B b' * θ) * algebraMap K B ϖ = x
  rw [hab, ea, eb]; ring

end IsUnitGen
end Alg

section Top
variable {K B : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CommRing B] [Algebra K B] [TopologicalSpace B] [IsModuleTopology K B]

theorem isOpen_int : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[K] : Set K) := IsNonarchimedeanLocalField.isCompact_closedBall K 1

theorem secondCountable : SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  infer_instance

theorem isOpen_coord (f : B ≃ₗ[K] K × K) (S : Set B) (hS : ∀ x, x ∈ S ↔ (f x).1 ∈ 𝒪[K] ∧ (f x).2 ∈ 𝒪[K]) :
    IsOpen S := by
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  have : S = f ⁻¹' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) := by ext x; exact hS x
  rw [this]
  exact (isOpen_int.prod isOpen_int).preimage hf

theorem exists_haar [MeasurableSpace B] [BorelSpace B] (f : B ≃ₗ[K] K × K) (S : Set B)
    (hS : ∀ x, x ∈ S ↔ (f x).1 ∈ 𝒪[K] ∧ (f x).2 ∈ 𝒪[K]) :
    ∃ μ : Measure B, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ S = 1 := by
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup K B
  haveI : ContinuousSMul K B := IsModuleTopology.toContinuousSMul K B
  haveI := secondCountable (K := K)
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  have hg : Continuous f.symm := IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap
  let φ : B ≃ₜ K × K := ⟨f.toEquiv, hf, hg⟩
  haveI : SecondCountableTopology B := φ.secondCountableTopology
  haveI : LocallyCompactSpace B := φ.isOpenEmbedding.locallyCompactSpace
  have hc : IsCompact S := by
    have : S = φ ⁻¹' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) := by ext x; exact hS x
    rw [this]
    exact φ.isCompact_preimage.2 (isCompact_int.prod isCompact_int)
  have ho := isOpen_coord f S hS
  let P : TopologicalSpace.PositiveCompacts B := ⟨⟨S, hc⟩, by
    change (interior S).Nonempty
    rw [ho.interior_eq]
    exact ⟨0, (hS 0).2 (by simp)⟩⟩
  exact ⟨Measure.addHaarMeasure P, inferInstance, inferInstance, Measure.addHaarMeasure_self⟩

theorem continuous_char {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalAddGroup B] (ψ : AddChar B ℂ) (S : Set B) (hS : IsOpen S) (h0 : (0 : B) ∈ S) (hψ : ∀ x ∈ S, ψ x = 1) :
    Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' S, hS.preimage (by fun_prop), by simpa using h0, fun y hy => ?_⟩
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ _ hy, mul_one]

theorem exists_de (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    [FiniteDimensional ℚ_[l] K] : ∃ de : K, de ≠ 0 ∧
      ∀ x : K, (∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * y)‖ ≤ 1) ↔ de * x ∈ 𝒪[K] := by
  haveI : ContinuousSMul ℚ_[l] K := continuousSMul_of_algebraMap _ _ hc
  haveI : T2Space K := by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have htr : Continuous (Algebra.trace ℚ_[l] K) := LinearMap.continuous_of_finiteDimensional _
  have hsm : ∀ (c : ℚ_[l]) (y : K), Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K c * y) = c * Algebra.trace ℚ_[l] K y :=
    fun c y => by rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  obtain ⟨C, hC⟩ := (isCompact_int.image htr).isBounded.exists_norm_le
  obtain ⟨x₁, hx₁, hD₁⟩ : ∃ x : K, x ≠ 0 ∧ ∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * y)‖ ≤ 1 := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    have hc0 : 0 < ‖c‖ := lt_of_le_of_lt (le_max_right _ _) hc
    have hc1 : c ≠ 0 := norm_pos_iff.1 hc0
    refine ⟨algebraMap ℚ_[l] K c⁻¹, by simpa using hc1, fun y hy => ?_⟩
    rw [hsm, norm_mul, norm_inv, inv_mul_le_one₀ hc0]
    exact (hC _ ⟨y, hy, rfl⟩).trans ((le_max_left _ _).trans hc.le)
  obtain ⟨x₀, hx₀⟩ : ∃ x : K, ¬ ‖Algebra.trace ℚ_[l] K x‖ ≤ 1 := by
    have h1 : Algebra.trace ℚ_[l] K 1 ≠ 0 := by
      rw [← map_one (algebraMap ℚ_[l] K), Algebra.trace_algebraMap]
      simpa using (Module.finrank_pos (R := ℚ_[l]) (M := K)).ne'
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] 1
    refine ⟨algebraMap ℚ_[l] K (c / Algebra.trace ℚ_[l] K 1) * 1, ?_⟩
    rw [hsm, div_mul_cancel₀ _ h1]; exact not_le.2 hc
  have hx0 : x₀ ≠ 0 := by rintro rfl; simp at hx₀
  have hmem : ∀ x : K, (∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * y)‖ ≤ 1) → x / x₀ ∈ 𝒪[K] := by
    intro x hx
    by_cases hx' : x = 0
    · simp [hx']
    rcases ValuationRing.isInteger_or_isInteger 𝒪[K] (x / x₀) with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [← hy]; exact y.2
    · exfalso
      apply hx₀
      have := hx y y.2
      have e : (y : K) = (x / x₀)⁻¹ := hy
      rwa [e, inv_div, mul_div_cancel₀ _ hx'] at this
  let I : Ideal 𝒪[K] :=
    { carrier := {a | ∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x₀ * a * y)‖ ≤ 1}
      zero_mem' := fun y _ => by simp
      add_mem' := fun {a b} ha hb y hy => by
        have : x₀ * ((a + b : 𝒪[K]) : K) * y = x₀ * a * y + x₀ * b * y := by push_cast; ring
        rw [this, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y hy) (hb y hy))
      smul_mem' := fun c a ha y hy => by
        have : x₀ * ((c • a : 𝒪[K]) : K) * y = x₀ * a * (c * y) := by
          simp only [smul_eq_mul]; push_cast; ring
        rw [this]
        exact ha _ (mul_mem c.2 hy) }
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have hI : ∀ b : 𝒪[K], (∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x₀ * b * y)‖ ≤ 1) ↔ a ∣ b := fun b => by
    rw [← Ideal.mem_span_singleton]
    change b ∈ I ↔ _
    rw [ha]
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := (hI ⟨x₁ / x₀, hmem _ hD₁⟩).1 (by simpa only [mul_div_cancel₀ _ hx0] using hD₁)
    have := congrArg Subtype.val hc
    simp only [MulMemClass.coe_mul, h0, zero_mul] at this
    exact div_ne_zero hx₁ hx0 this
  refine ⟨(x₀ * a)⁻¹, inv_ne_zero (mul_ne_zero hx0 ha0), fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (hI ⟨x / x₀, hmem _ hx⟩).1 (by simpa only [mul_div_cancel₀ _ hx0] using hx)
    have e : x / x₀ = a * c := congrArg Subtype.val hc
    have : (x₀ * a)⁻¹ * x = c := by
      rw [div_eq_iff hx0] at e
      rw [e]; field_simp
    rw [this]; exact c.2
  · have := (hI a).2 dvd_rfl _ (mul_mem hx hy)
    convert this using 3
    field_simp

end Top

theorem char_eq_one_iff (l : ℕ) [hl : Fact l.Prime] (x : ℚ_[l]) (z : ℂ)
    (h : ∃ a : ℚ, (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1 ∧
      z = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ))) : z = 1 ↔ ‖x‖ ≤ 1 := by
  obtain ⟨a, ⟨n, hn⟩, hx, rfl⟩ := h
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have : (a : ℂ) = (m : ℂ) := mul_left_cancel₀ h2 (by rw [hm]; ring)
    have ha : a = m := by exact_mod_cast this
    have e : x = (x - (a : ℚ_[l])) + (m : ℚ_[l]) := by rw [ha]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (Padic.norm_int_le_one m))
  · intro h1
    have ha : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have e : (a : ℚ_[l]) = x + -(x - (a : ℚ_[l])) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    have hd : ¬ l ∣ a.den := GlobalTheory.LocalData.not_dvd_den l ha
    have hn0 : n = 0 := by
      by_contra h0
      exact hd (hn ▸ dvd_pow_self l h0)
    rw [hn0, pow_zero] at hn
    refine ⟨a.num, ?_⟩
    have : (a : ℂ) = (a.num : ℂ) := by exact_mod_cast congrArg (fun r : ℚ => (r : ℂ)) ((Rat.den_eq_one_iff a).1 hn).symm
    rw [this]; ring

section Build
variable {K B : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CommRing B] [Algebra K B] [TopologicalSpace B] [IsModuleTopology K B]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace B] [IsModuleTopology K B] in

theorem IsUnitGen.exists_coord {cj : B ≃ₐ[K] B} {θ : B} {t n : K} (h : IsUnitGen cj θ t n) :
    ∃ f : B ≃ₗ[K] K × K, ∀ x, IsIntegral 𝒪[K] x ↔ (f x).1 ∈ 𝒪[K] ∧ (f x).2 ∈ 𝒪[K] := by
  let g : K × K →ₗ[K] B := (LinearMap.toSpanSingleton K B 1).coprod (LinearMap.toSpanSingleton K B θ)
  have hg : ∀ z, g z = algebraMap K B z.1 + algebraMap K B z.2 * θ := fun z => by
    simp [g, Algebra.smul_def]
  have hb : Function.Bijective g := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ e
      rw [hg] at e
      have e2 := h.sub_cj a b
      simp only at e
      rw [e, map_zero, sub_zero, zero_mul, ← map_zero (algebraMap K B)] at e2
      have hb : b = 0 := (mul_eq_zero.1 (h.inj e2).symm).resolve_right h.disc_ne
      subst hb
      simp only [map_zero, zero_mul, add_zero] at e
      rw [← map_zero (algebraMap K B)] at e
      rw [h.inj e]; rfl
    · intro x
      obtain ⟨a, b, e⟩ := h.gen x
      exact ⟨(a, b), by rw [hg, e]⟩
  refine ⟨(LinearEquiv.ofBijective g hb).symm, fun x => ?_⟩
  rw [← h.int_iff, ← hg]
  have : g ((LinearEquiv.ofBijective g hb).symm x) = x := (LinearEquiv.ofBijective g hb).apply_symm_apply x
  rw [this]

theorem exists_splitG (L : LocE K B) {l : ℕ} (S : SplitAt K B L.cj l) :
    ∃ G : SplitG L, G.e = S.e ∧ G.q = S.q := by
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup K B
  haveI : ContinuousSMul K B := IsModuleTopology.toContinuousSMul K B
  have hs : Continuous S.e.symm := IsModuleTopology.continuous_of_linearMap S.e.symm.toLinearMap
  have hin : ∀ y ∈ 𝒪[K], S.e.symm (y, 0) ∈ L.O := by
    intro y hy
    rw [L.O_def]
    have e : S.e.symm (y, 0) = algebraMap K B y * S.e.symm (1, 0) := by
      apply S.e.injective; simp
    rw [e]
    refine (int_algebraMap hy).mul ?_
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    apply S.e.injective; simp
  have hout : ∀ w ∈ L.O, (S.e w).1 ∈ 𝒪[K] := by
    intro w hw
    rw [L.O_def] at hw
    exact mem_of_int (hw.map (((AlgHom.fst K K K).comp S.e.toAlgHom).restrictScalars 𝒪[K]))
  let j : K →+ B := S.e.symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl K K)
  have hj : ∀ y, j y = S.e.symm (y, 0) := fun _ => rfl
  have hq0 : (S.q : K) ≠ 0 := fun e => S.q_irr.ne_zero (Subtype.ext e)
  refine ⟨⟨S.e, S.e_cj, S.q, S.q_irr, L.psi0.compAddMonoidHom j, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · change Continuous fun y => L.psi0 (S.e.symm (y, 0))
    exact L.local_additive_char_continuous.comp (hs.comp (by fun_prop))
  · intro y hy
    change L.psi0 (S.e.symm (y, 0)) = 1
    simpa using (L.additive_character_dual_ring _).2 (hin y hy) 1 L.O.one_mem
  · by_contra hne
    push Not at hne
    have h1 : S.e.symm ((S.q : K)⁻¹, 0) ∈ L.O := by
      refine (L.additive_character_dual_ring _).1 fun w hw => ?_
      have := hne ⟨_, hout w hw⟩
      change L.psi0 (S.e.symm (_, 0)) = 1 at this
      rw [← this]
      congr 1
      apply S.e.injective
      ext <;> simp [div_eq_inv_mul]
    have h2 := hout _ h1
    simp only [AlgEquiv.apply_symm_apply] at h2
    exact S.q_irr.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext (mul_inv_cancel₀ hq0)))
  · intro x
    rw [AddChar.map_add_eq_mul]
    change _ = L.psi0 (S.e.symm (_, 0)) * L.psi0 (S.e.symm (_, 0))
    rw [← L.local_additive_char_conj (S.e.symm ((S.e x).2, 0)), ← AddChar.map_add_eq_mul]
    congr 1
    apply S.e.injective
    ext <;> simp [S.e_cj]

omit [IsNonarchimedeanLocalField K] [IsModuleTopology K B] in

theorem mem_R_split [MeasurableSpace B] (L : LocE K B) (G : SplitG L) (μ : Measure B) (x : B) :
    x ∈ (Model.mk L (some G) μ).R ↔ (G.e x).1 ∈ 𝒪[K] ∧ ((G.e x).1 - (G.e x).2) / (G.q : K) ∈ 𝒪[K] := by
  have hq0 : (G.q : K) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
  simp only [Model.R, Subring.mem_comap, Subring.mem_map, RingHom.mem_eqLocus, RingHom.comp_apply,
    Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, hc⟩, e⟩
    have e1 : (a : K) = (G.e x).1 := congrArg Prod.fst e
    have e2 : (b : K) = (G.e x).2 := congrArg Prod.snd e
    have e3 : (a : K) - b = G.q * c := congrArg Subtype.val hc
    rw [← e1, ← e2, e3, mul_div_cancel_left₀ _ hq0]
    exact ⟨a.2, c.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(⟨_, h1⟩, ⟨_, h1⟩ - G.q * ⟨_, h2⟩), ⟨⟨_, h2⟩, by simp⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change (G.e x).1 - G.q * (((G.e x).1 - (G.e x).2) / G.q) = (G.e x).2
      field_simp; ring

theorem exists_haar_split [MeasurableSpace B] [BorelSpace B] (L : LocE K B) (G : SplitG L) :
    ∃ μ : Measure B, (Model.mk L (some G) μ).HaarOK := by
  have hq0 : (G.q : K) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
  let c : (K × K) ≃ₗ[K] K × K :=
    { toFun := fun z => (z.1, (z.1 - z.2) / G.q)
      invFun := fun z => (z.1, z.1 - G.q * z.2)
      map_add' := fun z w => by ext <;> simp; ring
      map_smul' := fun a z => by ext <;> simp; ring
      left_inv := fun z => by ext <;> simp; field_simp; ring
      right_inv := fun z => by ext <;> simp; field_simp }
  obtain ⟨μ, h1, h2, h3⟩ := exists_haar (G.e.toLinearEquiv.trans c) ((Model.mk L (some G) 0).R : Set B)
    (fun x => mem_R_split L G 0 x)
  exact ⟨μ, h1, h2, h3⟩

end Build

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem psiE_eq_one_iff (y : A.Ep) : A.psiE y = 1 ↔ (haveI := A.ellPrime;
    ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep y)‖ ≤ 1) := by
  haveI := A.ellPrime
  letI : Algebra ℚ_[resChar p] A.Ep := ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[resChar p] A.Fp A.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := A.qlFin
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  rw [Algebra.trace_trace]
  exact char_eq_one_iff _ _ _ (A.psiE_def y)

theorem exists_model {θ : A.Ep} {t n : A.Fp} (h : IsUnitGen A.cj θ t n) :
    ∃ (M : Model A.Fp A.Ep) (de : A.Fp), M.OK ∧ de ≠ 0 ∧
      (∀ x : A.Fp, (haveI := A.ellPrime;
        ∀ y ∈ 𝒪[A.Fp], ‖Algebra.trace ℚ_[resChar p] A.Fp (x * y)‖ ≤ 1) ↔ de * x ∈ 𝒪[A.Fp]) ∧
      M.L.cj = A.cj ∧ (∀ y, M.L.psi0 y = A.psiE (-(algebraMap A.Fp A.Ep de⁻¹ * y))) ∧
      (M.split.isSome ↔ A.split.isSome) ∧
      ∀ G : SplitG M.L, M.split = some G →
        (G.q : A.Fp) = (resChar p : A.Fp) ∧ ∃ S, A.split = some S ∧ S.e = G.e := by
  haveI := A.ellPrime
  haveI := A.lf
  haveI := A.char0
  haveI := A.top
  haveI := A.borel
  haveI := A.qlFin
  haveI : IsTopologicalAddGroup A.Ep := IsModuleTopology.topologicalAddGroup A.Fp A.Ep
  obtain ⟨de, hde, hgen⟩ := exists_de (K := A.Fp) (resChar p) A.qlCont
  let ψ : AddChar A.Ep ℂ :=
    A.psiE.compAddMonoidHom (-(AddMonoidHom.mulLeft (algebraMap A.Fp A.Ep de⁻¹)))
  have hψ : ∀ y, ψ y = A.psiE (-(algebraMap A.Fp A.Ep de⁻¹ * y)) := fun _ => rfl
  have hψ1 : ∀ y, ψ y = 1 ↔ ‖Algebra.trace ℚ_[resChar p] A.Fp (de⁻¹ * Algebra.trace A.Fp A.Ep y)‖ ≤ 1 := by
    intro y
    rw [hψ, psiE_eq_one_iff, map_neg, map_neg, norm_neg, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hdual : ∀ x : A.Ep, (∀ y ∈ A.O, ψ (x * y) = 1) ↔ x ∈ A.O := by
    intro x
    rw [A.O_def, ← h.trace_dual A.rank]
    constructor
    · intro hx y hy
      have := (hgen (de⁻¹ * Algebra.trace A.Fp A.Ep (x * y))).1 fun c hc => by
        have h2 := (hψ1 _).1 (hx (algebraMap A.Fp A.Ep c * y) ((A.O_def _).2 ((int_algebraMap hc).mul hy)))
        rw [mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul] at h2
        convert h2 using 3
        ring
      rwa [mul_inv_cancel_left₀ hde] at this
    · intro hx y hy
      rw [hψ1]
      have := (hgen (de⁻¹ * Algebra.trace A.Fp A.Ep (x * y))).2 (by
        rw [mul_inv_cancel_left₀ hde]; exact hx y ((A.O_def y).1 hy)) 1 (one_mem _)
      rwa [mul_one] at this
  obtain ⟨f, hf⟩ := h.exists_coord
  have hfO : ∀ x, x ∈ (A.O : Set A.Ep) ↔ (f x).1 ∈ 𝒪[A.Fp] ∧ (f x).2 ∈ 𝒪[A.Fp] := fun x =>
    (A.O_def x).trans (hf x)
  let L : LocE A.Fp A.Ep :=
    { cj := A.cj
      cj_cj := h.cj_cj
      cj_fix := h.cj_fix
      free := A.free
      rank := A.rank
      reduced := h.reduced
      top := A.top
      O := A.O
      O_def := A.O_def
      unram := fun ϖ hϖ x hx => h.unram A.O A.O_def ϖ hϖ.prime x hx
      psi0 := ψ
      local_additive_char_continuous := continuous_char ψ A.O (isOpen_coord f _ hfO) A.O.zero_mem fun x hx => by
        simpa using (hdual x).2 hx 1 A.O.one_mem
      local_additive_char_conj := fun y => by
        have e : A.cj y = y + (A.cj y - y) := by ring
        have : ψ (A.cj y - y) = 1 := by
          rw [hψ1, map_sub, Algebra.trace_eq_of_algEquiv A.cj]; simp
        rw [e, AddChar.map_add_eq_mul, this, mul_one]
      additive_character_dual_ring := hdual }
  cases hS : A.split with
  | none =>
    obtain ⟨μ, h1, h2, h3⟩ := exists_haar f _ hfO
    exact ⟨⟨L, none, μ⟩, de, ⟨A.lf, A.char0, A.borel, h1, h2, h3⟩, hde, hgen, rfl, hψ, by simp,
      fun G hG => by cases hG⟩
  | some S =>
    obtain ⟨G, hG1, hG2⟩ := exists_splitG L S
    obtain ⟨μ, hμ⟩ := exists_haar_split L G
    refine ⟨⟨L, some G, μ⟩, de, ⟨A.lf, A.char0, A.borel, hμ⟩, hde, hgen, rfl, hψ, by simp, fun G' hG' => ?_⟩
    obtain rfl : G = G' := Option.some.inj hG'
    exact ⟨by rw [hG2]; exact S.q_eq, S, rfl, hG1.symm⟩

omit A in

theorem exists_isUnitGen [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (A : LocAt F E hc.sig p) :
    ∃ θ t n, IsUnitGen A.cj θ t n := by
  obtain ⟨θ, t, n, ht, hn, hd⟩ := GlobalTheory.cm_exists_unit_disc hc p.asIdeal p.isMaximal
  have hv : ∀ x : F, p.valuation F x ≤ 1 → A.ιF x ∈ 𝒪[A.Fp] := fun x hx => by
    have := (A.val x 1).2 (by simpa using hx)
    rw [Valuation.Compatible.vle_iff_le (v := valuation A.Fp), map_one, map_one] at this
    exact this
  have hi : ∀ x : 𝓞 F, A.ιF x ∈ 𝒪[A.Fp] := fun x => hv _ (p.valuation_le_one x)
  have hd1 : p.valuation F ((t : F) ^ 2 - 4 * n) = 1 := by
    have := (p.valuation_eq_one_iff_notMem (K := F)).2 hd
    simpa only [map_sub, map_pow, map_mul, map_ofNat] using this
  have hd0 : (t : F) ^ 2 - 4 * n ≠ 0 := fun e => by simp [e] at hd1
  have hθ : (θ : E) - star (θ : E) ≠ 0 := by
    intro e
    apply hd0
    apply (algebraMap F E).injective
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero, ← ht, ← hn]
    linear_combination ((θ : E) - star (θ : E)) * e
  have hcj : ∀ x : E, A.cj (A.ιE x) = A.ιE (star x) := A.cj_ιE
  have ed : A.ιF t ^ 2 - 4 * A.ιF n = A.ιF ((t : F) ^ 2 - 4 * n) := by
    simp only [map_sub, map_pow, map_mul, map_ofNat]
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  refine ⟨A.ιE θ, A.ιF t, A.ιF n, (algebraMap A.Fp A.Ep).injective, fun x => ?_, ?_, ?_, hi t, hi n, ?_, ?_⟩
  · have hx : x ∈ Submodule.span A.Fp (Set.range A.ιE) := A.span ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨a, b, rfl⟩ := GlobalTheory.cm_exists_coords hc θ hθ y
      exact ⟨A.ιF a, A.ιF b, by rw [map_add, map_mul, A.compat, A.compat]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
    | smul c x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨c * a, c * b, by simp only [map_mul, Algebra.smul_def]; ring⟩
  · rw [hcj, ← map_add, ht, A.compat]
  · rw [hcj, ← map_mul, hn, A.compat]
  · rw [ed]; exact (map_ne_zero _).2 hd0
  · rw [ed, ← map_inv₀]; exact hv _ (by rw [map_inv₀, hd1, inv_one])

end GlobalTheory.SgGlob.LocModel
end
end

section
noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc
open scoped Classical

namespace GlobalTheory.SgGlob

structure ModFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (g₁ g₂ : ℕ) where
  rank : Module.finrank F E = 2
  g₁_prime : g₁.Prime
  g₂_prime : g₂.Prime
  g_ne : g₁ ≠ g₂
  A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  M : ∀ p, Model (A p).Fp (A p).Ep
  ok : ∀ p, (M p).OK
  de : ∀ p, (A p).Fp
  de_ne : ∀ p, de p ≠ 0
  de_gen : ∀ p (x : (A p).Fp), (haveI := (A p).ellPrime;
    ∀ y ∈ 𝒪[(A p).Fp], ‖Algebra.trace ℚ_[resChar p] (A p).Fp (x * y)‖ ≤ 1) ↔ de p * x ∈ 𝒪[(A p).Fp]
  cj_eq : ∀ p, (M p).L.cj = (A p).cj
  fractionFieldToGenericStalk_algebraMap_eq : ∀ p y, (M p).L.psi0 y = (A p).psiE (-(algebraMap (A p).Fp (A p).Ep (de p)⁻¹ * y))
  typed : ∀ p, (M p).split.isSome ↔ (resChar p = g₁ ∨ resChar p = g₂)
  split_eq : ∀ p (G : SplitG (M p).L), (M p).split = some G →
    (G.q : (A p).Fp) = (resChar p : (A p).Fp) ∧ ∃ S, (A p).split = some S ∧ S.e = G.e

section Inhabitant




end Inhabitant

section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def tau0 (M : Model F E) (T T' : F) : E :=
  match M.split with
  | none => 0
  | some G => G.e.symm (-T / (G.q : F), T' / (G.q : F))

def dLoc (M : Model F E) (τ : E) {n : ℕ} (w : Pt E n) : ℂ :=
  match w.blocks.getLast? with
  | none => 1
  | some b => if (b.2 : ℕ) = 2 then M.psiR (τ * ((b.1⁻¹ : Eˣ) : E)) else 1

def LastOne {r : ℕ} (w : Pt E (r + 1)) : Prop := ∃ x : Pt E r × Eˣ, w.blocks = x.1.blocks ++ [(x.2, 1)]

def KtopLoc (M : Model F E) (τ : E) {r : ℕ} (w w' : Pt E (r + 1)) : ℂ :=
  if h : LastOne w then
    (if h' : LastOne w' then
      (if h.choose.2 = h'.choose.2 then M.CuspSpanExtension ((h.choose.2 : E) - τ) h.choose.1 h'.choose.1 else 0)
    else 0)
  else if LastOne w' then 0 else dLoc M τ w * M.Kk (r + 1) w w' * conj (dLoc M τ w')

omit [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] in

theorem lastOne_iff {r : ℕ} (w : Pt E (r + 1)) : LastOne w ↔ ∃ l t, w.blocks = l ++ [(t, 1)] := by
  refine ⟨fun ⟨x, hx⟩ => ⟨_, _, hx⟩, fun ⟨l, t, h⟩ => ⟨(⟨l, ?_⟩, t), h⟩⟩
  have := w.size
  rw [h] at this
  simpa using this



end Local

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

def uP (p : HeightOneSpectrum (𝓞 F)) : ℚ :=
  (if resChar p = g₁ ∨ resChar p = g₂ then (resChar p : ℚ) else 1) / ((g₁ : ℚ) * g₂)

def cP (p : HeightOneSpectrum (𝓞 F)) : (X.A p).Fp := X.de p * ((uP (F := F) (g₁ := g₁) (g₂ := g₂) p : ℚ) : (X.A p).Fp)

def tmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : E) : (X.A p).Ep :=
  match (X.M p).split with
  | none => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ (-ν)) * (X.A p).ιE t
  | some G => G.e.symm (X.cP p ^ (-ν) * (G.e ((X.A p).ιE t)).1 / (G.q : (X.A p).Fp),
      (-1) ^ s * X.cP p ^ (-ν) * (G.e ((X.A p).ιE t)).2 / (G.q : (X.A p).Fp))

include X in

theorem exists_unitAt_eq_inv (p : HeightOneSpectrum (𝓞 F)) :
    ∃ m : ℕ, ¬ resChar p ∣ m ∧ uP (F := F) (g₁ := g₁) (g₂ := g₂) p = (m : ℚ)⁻¹ ∧
      g₁ * g₂ = (if resChar p = g₁ ∨ resChar p = g₂ then resChar p else 1) * m := by
  have h1 : (g₁ : ℚ) ≠ 0 := by exact_mod_cast X.g₁_prime.ne_zero
  have h2 : (g₂ : ℚ) ≠ 0 := by exact_mod_cast X.g₂_prime.ne_zero
  have hp : (resChar p).Prime := (X.A p).ellPrime.out
  unfold uP
  by_cases e1 : resChar p = g₁
  · refine ⟨g₂, fun h => X.g_ne (e1 ▸ (Nat.prime_dvd_prime_iff_eq hp X.g₂_prime).1 h), ?_, by simp [e1]⟩
    rw [if_pos (Or.inl e1), e1]; field_simp
  by_cases e2 : resChar p = g₂
  · refine ⟨g₁, fun h => e1 ((Nat.prime_dvd_prime_iff_eq hp X.g₁_prime).1 h), ?_, by simp [e2, mul_comm]⟩
    rw [if_pos (Or.inr e2), e2]; field_simp
  refine ⟨g₁ * g₂, fun h => ?_, by simp [e1, e2], by simp [e1, e2]⟩
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact e1 ((Nat.prime_dvd_prime_iff_eq hp X.g₁_prime).1 h)
  · exact e2 ((Nat.prime_dvd_prime_iff_eq hp X.g₂_prime).1 h)

theorem cP_ne_zero (p : HeightOneSpectrum (𝓞 F)) : X.cP p ≠ 0 := by
  haveI := (X.A p).char0
  obtain ⟨m, hm, e, -⟩ := X.exists_unitAt_eq_inv p
  have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  unfold cP
  rw [e]
  exact mul_ne_zero (X.de_ne p) (by simpa using this)

def xmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x : E) : (X.A p).Ep :=
  match (X.M p).split with
  | none => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ ν) * (X.A p).ιE x
  | some G => G.e.symm (X.cP p ^ ν * (G.e ((X.A p).ιE x)).1 * (G.q : (X.A p).Fp),
      (-1) ^ s * X.cP p ^ ν * (G.e ((X.A p).ιE x)).2 * (G.q : (X.A p).Fp))

def tfac (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : (X.A p).Ep := X.tmod ν s p 1

theorem tmod_eq (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : E) :
    X.tmod ν s p t = X.tfac ν s p * (X.A p).ιE t := by
  unfold tfac tmod
  cases (X.M p).split with
  | none => simp
  | some G => apply G.e.injective; ext <;> simp <;> ring

theorem xmod_eq (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x : E) :
    X.xmod ν s p x = X.xmod ν s p 1 * (X.A p).ιE x := by
  unfold xmod
  cases (X.M p).split with
  | none => simp
  | some G => apply G.e.injective; ext <;> simp <;> ring

theorem tfac_mul (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : X.tfac ν s p * X.xmod ν s p 1 = 1 := by
  have hc : X.cP p ^ ν ≠ 0 := zpow_ne_zero _ (X.cP_ne_zero p)
  unfold tfac tmod xmod
  cases (X.M p).split with
  | none => simp only [map_one, mul_one]; rw [← map_mul, zpow_neg, inv_mul_cancel₀ hc, map_one]
  | some G =>
    have hq : (G.q : (X.A p).Fp) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
    have hs : ((-1 : (X.A p).Fp) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    apply G.e.injective
    ext
    · simp only [map_one, map_mul, AlgEquiv.apply_symm_apply, Prod.fst_mul, Prod.fst_one, zpow_neg]
      field_simp
    · simp only [map_one, map_mul, AlgEquiv.apply_symm_apply, Prod.snd_mul, Prod.snd_one, zpow_neg]
      field_simp
      exact hs

theorem tmod_mul_xmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) {t : E} (ht : t ≠ 0) :
    X.tmod ν s p t * X.xmod ν s p t⁻¹ = 1 := by
  rw [tmod_eq, xmod_eq, mul_mul_mul_comm, tfac_mul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]

theorem isUnit_tmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) : IsUnit (X.tmod ν s p t) :=
  IsUnit.of_mul_eq_one _ (X.tmod_mul_xmod ν s p t.ne_zero)


theorem tmod_sub (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t t' : E) :
    X.tmod ν s p (t - t') = X.tmod ν s p t - X.tmod ν s p t' := by
  simp only [tmod_eq, map_sub, mul_sub]

@[simp] theorem tmod_zero (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : X.tmod ν s p 0 = 0 := by
  simp [tmod_eq]



def tmodU (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) : (X.A p).Epˣ :=
  if h : IsUnit (X.tmod ν s p t) then h.unit else 1

@[simp] theorem coe_tmodU (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) :
    ((X.tmodU ν s p t : (X.A p).Epˣ) : (X.A p).Ep) = X.tmod ν s p t := by
  unfold tmodU
  rw [dif_pos (X.isUnit_tmod ν s p t), IsUnit.unit_spec]



def nu (r a s : ℕ) : ℤ := 2 * (r : ℤ) + 1 - 2 * a - s

def off (l : List (Eˣ × ℕ+)) (n : ℕ) : ℕ := ((l.take n).map fun b => (b.2 : ℕ)).sum

def blocksMod (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) (l : List (Eˣ × ℕ+)) : List ((X.A p).Epˣ × ℕ+) :=
  l.mapIdx fun n b => (X.tmodU (nu r (off l n) b.2) b.2 p b.1, b.2)

lemma blocksMod_size (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) (l : List (Eˣ × ℕ+)) :
    (X.blocksMod r p l).map (fun b => (b.2 : ℕ)) = l.map (fun b => (b.2 : ℕ)) := by
  apply List.ext_getElem <;> simp [blocksMod]


def ptMod (r : ℕ) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ} (w : Pt E n) : Pt (X.A p).Ep n :=
  ⟨X.blocksMod r p w.blocks, by rw [X.blocksMod_size]; exact w.size⟩



def La (ν : ℤ) (s : ℕ) : Set E := {t | ∀ p, X.tmod ν s p t ∈ (X.M p).R}

def LaSub (ν : ℤ) (s : ℕ) : AddSubgroup E :=
  AddSubgroup.ofSub (X.La ν s) ⟨0, fun p => by simp⟩ fun t ht t' ht' p => by
    rw [← sub_eq_add_neg, tmod_sub]; exact sub_mem (ht p) (ht' p)

@[simp] theorem coe_LaSub (ν : ℤ) (s : ℕ) : (X.LaSub ν s : Set E) = X.La ν s := rfl

def La' (ν : ℤ) (s : ℕ) : Set E := {x | ∀ p, X.xmod ν s p x ∈ (X.M p).R}


def Kglob (r i : ℕ) (w w' : Pt E i) : ℂ := ∏ᶠ p, (X.M p).Kk i (X.ptMod r p w) (X.ptMod r p w')

def Ktop (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  if ∃ p, KtopLoc (X.M p) (tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')) (X.ptMod r p w) (X.ptMod r p w') = 0 then 0
  else ∏ᶠ p, KtopLoc (X.M p) (tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')) (X.ptMod r p w) (X.ptMod r p w')

omit X in

theorem nonempty_place : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩





def Nt (ν : ℤ) (s : ℕ) (t : E) : ℝ := if t = 0 then 0 else ∏ᶠ p, ((X.M p).modK (X.tmod ν s p t))⁻¹

@[simp] theorem Nt_zero (ν : ℤ) (s : ℕ) : X.Nt ν s 0 = 0 := if_pos rfl


def phi (r : ℕ) {i : ℕ} (w : Pt E i) : ℝ :=
  (w.blocks.mapIdx fun n b => X.Nt (nu r (off w.blocks n) b.2) b.2 b.1 ^
    ((b.2 : ℕ) * (2 * (i - (off w.blocks n + b.2)) + b.2 - 1) / 2)).prod

def KA (r i : ℕ) (w w' : Pt E i) : ℂ := X.Kglob r i w w' / ((X.phi r w * X.phi r w' : ℝ) : ℂ)

end ModFam

def lead {K : Type} [CommRing K] {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (l : ℕ) (hl : l ≤ n) : K :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def GZ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {r : ℕ} (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * sig Z.det - algebraMap F E (T * T') * (lead Z r (Nat.le_succ r) * sig (lead Z r (Nat.le_succ r)))

def psiInf {E : Type} [Field E] [NumberField E] (x : E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ))

example (r : ℕ) : ModFam.nu r r 1 = 0 := by simp [ModFam.nu]

example (r a s : ℕ) : ModFam.nu r a s = 2 * r + 3 - 2 * ((a : ℤ) + 1) - s := by unfold ModFam.nu; ring

example {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) (T T' : F) (z : E) :
    GZ (r := 0) sig T T' !![z] = z * sig z - algebraMap F E (T * T') := by
  simp [GZ, lead]

example : psiInf (1 / 4 : ℚ) = Complex.I := by
  unfold psiInf
  rw [Subsingleton.elim (DivisionRing.toRatAlgebra : Algebra ℚ ℚ) (Algebra.id ℚ), Algebra.trace_self_apply]
  refine Eq.trans ?_ Complex.exp_pi_div_two_mul_I
  congr 1
  push_cast
  ring

end GlobalTheory.SgGlob
end
end

section
noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc Matrix MeasureTheory
open scoped Classical

namespace GlobalTheory.SgGlob

section Rat
variable {E : Type} [Field E] [NumberField E]

def IntUp {r : ℕ} (u : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  GlobalTheory.SgAlg.IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)

def Tied (σ : E →+* E) (g : ℕ) {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IntUp u ∧ IntUp u' ∧
    (∀ a b : Fin (r + 1), a < b → (g : E)⁻¹ * (u a b - u' a b) ∈ dInv E ((b : ℕ) - a)) ∧
    Z' = GlobalTheory.SgAlg.cT σ u * Z * u'

def eps (K : Type) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun b => (-1) ^ (r - (b : ℕ))

def Xs {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (GlobalTheory.SgAlg.eOf P).mulVecLin

def W0 (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Set (Fin n → E) :=
  {v | (GlobalTheory.SgAlg.cT σ P * J) *ᵥ v = 0 ∧ (GlobalTheory.SgAlg.cT σ P' * J) *ᵥ v = 0}

end Rat

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

def Zloc {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  Matrix.of fun a b => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ (-(2 * (r : ℤ) - a - b))) * (X.A p).ιE (Z a b)

def Zmod {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  GlobalTheory.SgDen.zz (X.M p) (X.Zloc p Z) * eps (X.A p).Ep r

def tau (p : HeightOneSpectrum (𝓞 F)) (T T' : F) : (X.A p).Ep :=
  tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')

def Zplus {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  X.Zmod p Z - Matrix.single (Fin.last r) (Fin.last r) (X.tau p T T')

def wtLoc {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (w : Pt E (r + 1))
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  (GlobalTheory.SgLoc.orbMeas (X.M p) (X.ptMod r p w) {xy | ∃ l u, GlobalTheory.SgAlg.IsLo l ∧ GlobalTheory.SgAlg.IsUp u ∧
    GlobalTheory.SgDen.IntR (X.M p) l ∧ GlobalTheory.SgDen.IntR (X.M p) u ∧
    GlobalTheory.SgLoc.orbMat (X.ptMod r p w) xy = l * X.Zmod p Z * u}).toReal

def wt {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ := ∏ᶠ p, X.wtLoc p w Z

def gramPlus {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (X.A p).Ep :=
  let l : (X.A p).Ep := GlobalTheory.SgDen.levInv (X.M p)
  let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (X.A p).Ep :=
    Matrix.fromBlocks 1 (if (X.M p).split.isSome then (-l) • 1 else 0) 0 (l • 1)
  GlobalTheory.SgDen.ct (X.M p).L A *
    Matrix.fromBlocks (GlobalTheory.SgAlg.TF r ((X.A p).ιE (algebraMap F E T))) (X.Zloc p Z)
      (GlobalTheory.SgDen.ct (X.M p).L (X.Zloc p Z)) (GlobalTheory.SgAlg.TF r ((X.A p).ιE (algebraMap F E T'))) * A

def densLoc (n : ℕ) {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F))
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  GlobalTheory.SgDen.densF (GlobalTheory.SgDen.resQ (X.A p).Fp) (GlobalTheory.SgDen.eta (X.A p).Ep) n (2 * r + 2)
    (GlobalTheory.SgDen.corank (X.M p).L (X.gramPlus T T' p Z))

def dens (n : ℕ) {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  ∏' p, X.densLoc n T T' p Z

def admitted {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∀ p, GlobalTheory.SgDen.IntR (X.M p) (X.Zplus T T' p Z)

def IsMassConst (k r : ℕ) (J : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E) (T T' : F) (c : ℝ) : Prop :=
  ∀ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E, TotPos (GZ sig T T' Z) → X.admitted T T' Z →
    Mass (sig : E →+* E) J (algebraMap F E T) (algebraMap F E T') (g₁ * g₂) Z =
      ENNReal.ofReal (c * normInf (GZ sig T T' Z) ^ (k - 1) * X.dens (k + 2 * r + 1) T T' Z)

end ModFam

end GlobalTheory.SgGlob
end
end
