import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabelling
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetAutWdTieLabConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem not_isUnit_natCast {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) : ¬ IsUnit (p : 𝓞 K) := by
  intro h
  have : IsLocalHom (algebraMap ℤ (𝓞 K)) := Algebra.IsIntegral.isLocalHom _ _
  rw [← map_natCast (algebraMap ℤ (𝓞 K))] at h
  exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ h)

theorem rayField_splitsIn_of_isRayPrime (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M)
    (hf : FiniteDimensional ℚ M) :
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  intro hM p hp
  obtain ⟨hpp, π, hπK, hπi, hπc, σ, hσ⟩ := hp
  have hc0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
    exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
  let φ : D.host.K →+* Qb := jE.comp (D.host.K.val : D.host.K →+* D.host.E)
  have hφ : Function.Injective φ := jE.injective.comp Subtype.val_injective
  have hint : ∀ z : D.host.K, IsIntegral ℤ (φ z) → IsIntegral ℤ z := fun z hz =>
    (isIntegral_algHom_iff φ.toIntAlgHom hφ).1 hz
  have hmem : ∀ w : Qb, w ∈ KQbar D jE → ∃ z : D.host.K, φ z = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hw
    exact ⟨⟨z, hz⟩, rfl⟩
  have hp0 : (p : Qb) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hπ0 : π ≠ 0 := left_ne_zero_of_mul (hσ ▸ hp0)
  have hσπ : σ π = p / π := by rw [← hσ, mul_div_cancel_left₀ _ hπ0]
  have hσK : σ π ∈ KQbar D jE := hσπ ▸ div_mem (natCast_mem _ p) hπK
  obtain ⟨x, hx⟩ := hmem π hπK
  obtain ⟨y, hy⟩ := hmem (σ π) hσK
  let σZ : Qb →ₐ[ℤ] Qb := σ.toRingHom.toIntAlgHom
  let a : 𝓞 D.host.K := ⟨x, hint x (hx ▸ hπi)⟩
  let b : 𝓞 D.host.K := ⟨y, hint y (hy ▸ hπi.map σZ)⟩

  have hab : a * b = p := by
    apply RingOfIntegers.coe_injective
    apply hφ
    rw [map_mul, map_natCast, map_mul, map_natCast]
    show φ x * φ y = _
    rw [hx, hy, hσ]

  have hdvd : ∀ z : 𝓞 D.host.K,
      IsIntegral ℤ ((φ z - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) →
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.K) ∣ z - 1 := by
    intro z hz
    set c : ℕ := D.host.QS * D.host.q * D.host.d
    have hcK : (c : D.host.K) ≠ 0 := by exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
    have hφw : φ (((z : D.host.K) - 1) / c) = (φ z - 1) / c := by
      rw [map_div₀, map_sub, map_one, map_natCast]
    let w : 𝓞 D.host.K := ⟨((z : D.host.K) - 1) / c, hint _ (hφw ▸ hz)⟩
    refine ⟨w, RingOfIntegers.coe_injective ?_⟩
    show (z : D.host.K) - 1 = (c : D.host.K) * (((z : D.host.K) - 1) / c)
    rw [mul_div_cancel₀ _ hcK]
  have hca := hdvd a (by show IsIntegral ℤ ((φ x - 1) / _); rw [hx]; exact hπc)
  have hcb := hdvd b (by
    show IsIntegral ℤ ((φ y - 1) / _)
    have e : σZ ((π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) =
        (σ π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) := by
      show σ _ = _
      rw [map_div₀, map_sub, map_one, map_natCast]
    rw [hy, ← e]
    exact hπc.map σZ)

  have hpu : ¬ IsUnit (p : 𝓞 D.host.K) := not_isUnit_natCast hpp
  have hunit : ∀ (z : 𝓞 D.host.K), (z : D.host.K) ≠ 0 → IsIntegral ℤ (φ z)⁻¹ → IsUnit z := by
    intro z hz0 hz
    have hi : IsIntegral ℤ ((z : D.host.K)⁻¹) := hint _ (by rw [map_inv₀]; exact hz)
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝓞 D.host.K) (RingOfIntegers.coe_injective ?_)
    show (z : D.host.K) * (z : D.host.K)⁻¹ = 1
    exact mul_inv_cancel₀ hz0
  have hinv : ∀ (z : 𝓞 D.host.K), IsUnit z → IsIntegral ℤ (φ z)⁻¹ := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    have h1 : (algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K) =
        ((algebraMap (𝓞 D.host.K) D.host.K) (u : 𝓞 D.host.K))⁻¹ :=
      map_units_inv (algebraMap (𝓞 D.host.K) D.host.K) u
    have h2 : φ ((algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K)) =
        (φ ((u : 𝓞 D.host.K) : D.host.K))⁻¹ := by
      rw [h1, map_inv₀]
    rw [← h2]
    exact (RingOfIntegers.isIntegral_coe _).map φ.toIntAlgHom
  have hx0 : (x : D.host.K) ≠ 0 := fun h0 => hπ0 (by rw [← hx, h0, map_zero])
  have hy0 : (y : D.host.K) ≠ 0 := fun h0 => hp0 (by rw [← hσ, ← hy, h0, map_zero, mul_zero])
  have hu : ¬ IsUnit a := fun ha => hpu (by
    have h1 := (hinv a ha).map σZ
    have h2 : σZ (φ x)⁻¹ = (φ y)⁻¹ := by
      show σ (φ x)⁻¹ = _
      rw [map_inv₀, hx, hy]
    rw [← hab]
    exact ha.mul (hunit b hy0 (h2 ▸ h1)))
  have hu' : ¬ IsUnit b := fun hb => hpu (by
    haveI : Algebra.IsAlgebraic ℚ Qb := by
      unfold Qb; convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
    let τ : Qb ≃ₐ[ℚ] Qb := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
    let τZ : Qb →ₐ[ℤ] Qb := τ.symm.toRingEquiv.toRingHom.toIntAlgHom
    have h1 := (hinv b hb).map τZ
    have h2 : τZ (φ y)⁻¹ = (φ x)⁻¹ := by
      show τ.symm (φ y)⁻¹ = _
      rw [map_inv₀, hy, hx]
      congr 1
      exact τ.symm_apply_apply π
    rw [← hab]
    exact (hunit a hx0 (h2 ▸ h1)).mul hb)

  have hpc : ¬ p ∣ D.host.QS * D.host.q * D.host.d := fun hd => hpu (by
    have h1 : (p : 𝓞 D.host.K) ∣ a - 1 := (Nat.cast_dvd_cast hd).trans hca
    have h2 : (p : 𝓞 D.host.K) ∣ b - 1 := (Nat.cast_dvd_cast hd).trans hcb
    have h3 : (1 : 𝓞 D.host.K) = p - (a * (b - 1) + (a - 1)) := by rw [← hab]; ring
    exact isUnit_of_dvd_one (h3 ▸ dvd_sub dvd_rfl (dvd_add (h2.mul_left _) h1)))
  have hd : ¬ (p : ℤ) ∣ discr M := fun hd => hpc (GlobalTheory.Mem.RaySplit.unr_of_ray hM p hpp hd)
  exact (GlobalTheory.HostSplit.ncard_placesOver M hpp).trans
    (GlobalTheory.Mem.RaySplit.ncard_primesOver_eq hM (GlobalTheory.Mem.RaySplit.isEmpty_real D.host)
      (GlobalTheory.Mem.RaySplit.finrank_K D.host) hpp hd hab hu hu' hca hcb)

end GlobalTheory.ParRay

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime : ∀ (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  atlas_forward_decl GlobalTheory.ParRay.rayField_splitsIn_of_isRayPrime
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.Mem.RaySplit

open GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

theorem exists_span_eq_of_splits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)) (hR : GlobalTheory.Mem.Fld.IsRayField K L 𝔮) (𝔭 : HeightOneSpectrum (𝓞 K)) (hnd : ¬ 𝔭.asIdeal ∣ 𝔮)
    (hs : (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  have := hR.1
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))
  obtain ⟨σ, P, hP, hPo, hσ⟩ := exists_isFrob L 𝔭
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hef := (GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩
  have hf : 𝔭.asIdeal.inertiaDeg' P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  have hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI := Ideal.Quotient.field P
  letI := Fintype.ofFinite (𝓞 L ⧸ P)
  have hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := fun x => by
    rw [← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hin : InInertia L 𝔭 σ := ⟨P, hP, hPo, fun x => by
    have := add_mem (hσ x) (hpow x)
    rwa [sub_add_sub_cancel] at this⟩
  have hσ1 : σ = 1 := hR.2.1 𝔭 hnd σ hin
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1 := fun χ => by
    rw [heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]
  obtain ⟨α, β, hab, he⟩ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ
  have hα : α ∈ 𝔭.asIdeal * Ideal.span {β} := he ▸ Ideal.mem_span_singleton_self α
  obtain ⟨π, hπ, rfl⟩ := Ideal.mem_mul_span_singleton.1 hα
  have hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab.2.1
  have hsp : 𝔭.asIdeal = Ideal.span {π} := by
    refine mul_right_cancel₀ hβ0 ?_
    rw [he, Ideal.span_singleton_mul_span_singleton]
  refine ⟨π, hsp, ?_⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hab.2.2.2.1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have h1 : (π - 1) * β ∈ 𝔮 := by
    have := hab.2.2.2.2.1
    rwa [show π * β - β = (π - 1) * β by ring] at this
  have h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j := by
    linear_combination (π - 1) * hij.symm
  rw [h2]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)

end GlobalTheory.Mem.RaySplit
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)),
    GlobalTheory.Mem.Fld.IsRayField K L 𝔮 → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 →
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L →
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  atlas_forward_decl GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RayFieldNorm

theorem normSq_eq_absNorm {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (π : 𝓞 K) :
    ‖φ π‖ ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℝ) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem isTotallyComplex_of_isEmpty {K : Type} [Field K] [NumberField K]
    (h : IsEmpty (K →+* ℝ)) : IsTotallyComplex K := by
  rw [isTotallyComplex_iff]
  intro w
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  obtain ⟨φ, hφ, -⟩ := hw
  exact h.elim (NumberField.ComplexEmbedding.IsReal.embedding hφ)

theorem exists_mul_conj_eq_norm : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  intro K _ _ hE hK j π p hp
  haveI := isTotallyComplex_of_isEmpty hE
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qb →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := Qb)).toRingHom
  refine ⟨(Formalism.L2.DIV.conjQb ι).toAlgHom, ?_⟩
  apply ι.injective
  have hn := normSq_eq_absNorm hK (ι.comp j) π
  rw [hp] at hn
  have hc : ι (j (π : K)) * starRingEnd ℂ (ι (j (π : K))) = ((‖ι (j (π : K))‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs := Formalism.L2.DIV.conjQb_spec ι (j (π : K))
  change ι (j (π : K) * (Formalism.L2.DIV.conjQb ι) (j (π : K))) = ι (p : Qb)
  rw [map_mul, hs, hc, map_natCast]
  simp only [RingHom.comp_apply] at hn
  rw [hn]
  simp

end GlobalTheory.RayFieldNorm
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_galois_conj_eq_prime_imagQuadratic : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  atlas_forward_decl GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitTower

theorem splits_completely_of_intermediate :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  intro K L _ _ _ _ _ p hp hcount 𝔭 hp𝔭
  rw [GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭]
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  have hPmax : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI := hPmax
  haveI : Fintype (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : (P.primesOver (𝓞 L)).ncard = ∑ _q : P.primesOver (𝓞 L), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hall : ∀ Q ∈ P.primesOver (𝓞 L), Q.ramificationIdx ℤ * Q.inertiaDeg ℤ = 1 := by
    rw [← hsum, h1, Finset.sum_eq_sum_iff_of_le] at hcount
    · intro Q hQ
      exact (hcount ⟨Q, hQ⟩ (Finset.mem_univ _)).symm
    · rintro ⟨Q, hQ, _⟩ -
      exact Nat.mul_pos (Ideal.ramificationIdx_pos Q _) (Ideal.inertiaDeg_pos Q _)
  intro Q hQ
  obtain ⟨hQp, hQ𝔭⟩ := hQ
  haveI := 𝔭.isPrime
  haveI h𝔭P : 𝔭.asIdeal.LiesOver P := by
    refine ⟨hPmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_⟩
    rw [hPdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hp𝔭
  haveI : Q.LiesOver P := Ideal.LiesOver.trans Q 𝔭.asIdeal P
  have h := hall Q ⟨hQp, inferInstance⟩
  rw [Ideal.ramificationIdx_tower 𝔭.asIdeal Q, Ideal.inertiaDeg_tower 𝔭.asIdeal Q] at h
  refine Nat.eq_one_of_dvd_one ?_
  rw [← h]
  exact ⟨𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ, by ring⟩

end GlobalTheory.SplitTower
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  atlas_forward_decl GlobalTheory.SplitTower.splits_completely_of_intermediate
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ParRayMax

@[reducible] def algQb (D : D7) (jE : D.host.E →+* Qb) : Algebra D.host.K Qb :=
  (jE.comp (algebraMap D.host.K D.host.E)).toAlgebra

def toIF (D : D7) (jE : D.host.E →+* Qb) (L : Fld) (h : KQbar D jE ≤ L) :
    @IntermediateField D.host.K Qb _ _ (algQb D jE) :=
  letI := algQb D jE
  { L.toSubfield with algebraMap_mem' := fun x => h ⟨x.1, x.2, rfl⟩ }

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_embedded (hray : GlobalTheory.Published.RayClassFieldSt) (D : D7) (jE : D.host.E →+* Qb) :
    ∃ (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Published.rayClassFieldSt_iff_isRayField.1 hray D.host.K _
    (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)
  letI := algQb D jE
  let ψ : M →ₐ[D.host.K] Qb := IsAlgClosed.lift
  let M1 : Fld := (ψ : M →+* Qb).toRatAlgHom.fieldRange
  have hψ : ∀ x : D.host.K, ψ (algebraMap D.host.K M x) = jE x := fun x => ψ.commutes x
  have hK : KQbar D jE ≤ M1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨algebraMap D.host.K M ⟨x, hx⟩, hψ ⟨x, hx⟩⟩
  let e₀ : M ≃ₐ[ℚ] M1 := AlgEquiv.ofInjectiveField (ψ : M →+* Qb).toRatAlgHom
  have hf : FiniteDimensional ℚ M1 := e₀.toLinearEquiv.finiteDimensional
  refine ⟨M1, hK, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE hK
  haveI := GlobalTheory.ParRay.nfOf hf
  exact hM.of_algEquiv (AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun x => Subtype.ext (hψ x))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem le_of_rayAdm (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M)
    (hM : letI := GlobalTheory.ParRay.algK D jE h; haveI := GlobalTheory.ParRay.nfOf hf;
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host))
    (L : Fld) (hL : RayAdm (KQbar D jE) (D.host.QS * D.host.q * D.host.d) L) : L ≤ M := by
  have h2K := GlobalTheory.Mem.RaySplit.finrank_K D.host
  have h3K := GlobalTheory.Mem.RaySplit.isEmpty_real D.host
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  letI := algQb D jE
  obtain ⟨hKL, hfL, hspl⟩ := hL
  let mkE : ∀ (X : Fld) (hX : KQbar D jE ≤ X), X ≃+* toIF D jE X hX := fun X hX =>
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  let R := toIF D jE M h
  let L' := toIF D jE L hKL
  let eR : M ≃ₐ[D.host.K] R := AlgEquiv.ofRingEquiv (f := mkE M h) fun x => rfl
  let eL : L ≃+* L' := mkE L hKL
  haveI : NumberField R := { to_finiteDimensional := (eR.toRingEquiv.toRatAlgEquiv).toLinearEquiv.finiteDimensional }
  haveI : NumberField L' := { to_finiteDimensional := eL.toRatAlgEquiv.toLinearEquiv.finiteDimensional }
  have hR : GlobalTheory.Mem.Fld.IsRayField D.host.K R (GlobalTheory.Mem.RaySplit.condIdeal D.host) := hM.of_algEquiv eR
  have hab : IsAbelianGalois D.host.K R := hR.1
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), ¬ 𝔭.asIdeal ∣ GlobalTheory.Mem.RaySplit.condIdeal D.host →
      (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank D.host.K R →
        ∃ π : 𝓞 D.host.K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ GlobalTheory.Mem.RaySplit.condIdeal D.host :=
    fun 𝔭 h1 h2 => GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField D.host.K R _ hR 𝔭 h1 h2
  have hle : L' ≤ R := by
    refine @GlobalTheory.Bauer.le_of_finite_split_not_split D.host.K Qb _ _ _ _ R L' _ _ hab.toIsGalois
      ((Ideal.finite_factors (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)).subset ?_)
    rintro 𝔭 ⟨hpr, hRs, hLs⟩
    by_contra hnd
    apply hLs
    rw [GlobalTheory.Bauer.ncard_eq_ncard_primesOver] at hRs ⊢
    obtain ⟨π, hπ, hπ1⟩ := key 𝔭 hnd hRs
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_mul_galois_conj_eq_prime_imagQuadratic D.host.K h3K h2K
      (jE.comp (algebraMap D.host.K D.host.E)) π (Ideal.absNorm 𝔭.asIdeal) (congrArg Ideal.absNorm hπ).symm
    have hray : IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (Ideal.absNorm 𝔭.asIdeal) := by
      refine ⟨hpr, jE ((π : D.host.K) : D.host.E), ⟨_, (π : D.host.K).2, rfl⟩, ?_, ?_, σ, hσ⟩
      · exact (RingOfIntegers.isIntegral_coe π).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
      · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hπ1
        have hm0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
          exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
        have e : (jE ((π : D.host.K) : D.host.E) - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) =
            (jE.comp (algebraMap D.host.K D.host.E)) (y : D.host.K) := by
          rw [div_eq_iff hm0]
          have e1 := congrArg ((jE.comp (algebraMap D.host.K D.host.E)).comp (algebraMap (𝓞 D.host.K) D.host.K)) hy
          simp only [map_mul, map_sub, map_one, map_natCast] at e1
          exact e1.symm
        rw [e]
        exact (RingOfIntegers.isIntegral_coe y).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
    have hsp := hspl _ hray
    have h1 : ((Ideal.span {((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ)}).primesOver (𝓞 L')).ncard = Module.finrank ℚ L' := by
      rw [← GlobalTheory.HostSplit.ncard_placesOver L' hpr, ← finrank_eq_of_equiv eL]
      exact (ncard_places_of_equiv eL _).symm.trans hsp
    exact GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat D.host.K L' _ hpr h1 𝔭 (Ideal.absNorm_mem 𝔭.asIdeal)
  exact fun x hx => hle hx

theorem rayField_isRay : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  intro hray D jE
  obtain ⟨M, h, hf, hM⟩ := exists_embedded hray D jE
  have hsplit := GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime D jE M h hf hM
  have heq : MrayC D jE = M :=
    le_antisymm (iSup₂_le fun L hL => le_of_rayAdm D jE M h hf hM L hL) (le_rayField ⟨h, hf, hsplit⟩)
  generalize MrayC D jE = X at heq ⊢
  subst heq
  refine ⟨h, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  exact ⟨GlobalTheory.Mem.RaySplit.isGalois_of_ray hM, GlobalTheory.Mem.RaySplit.comm_of_ray hM, GlobalTheory.Mem.RaySplit.unr_of_ray hM, hsplit⟩

end GlobalTheory.ParRayMax

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFieldHostConductor_isRayClassField : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  atlas_forward_decl GlobalTheory.ParRayMax.rayField_isRay
end

section
noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_types : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc)
    (jE : D.host.E →+* Qb) (Pl : PlSide D), (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) →
    ∃ X h1 h0, X.tg = D.ntypes.tg ∧ X.teichC = D.ntypes.teichC ∧ X.eSer = D.ntypes.eSer ∧ X.cenAmb = D.ntypes.cenAmb ∧
      X.cenMt = D.ntypes.cenMt ∧ Nonempty (ParSide (setTy D hE X h1 h0) jE) ∧
      (Nonempty (GrpSide D) → IotaOk (setTy D hE X h1 h0) ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩) := by
  intro hray _ D hE jE Pl hg
  obtain ⟨h, hf, hgal, hab, hunr, hsplit⟩ := GlobalTheory.T.rayClassFieldHostConductor_isRayClassField hray D jE
  letI := algK D jE h
  have := nfOf hf
  let X : NTypes D.naut :=
    { D.ntypes with
      Mray := MrayC D jE
      instMray := inferInstance
      nfMray := nfOf hf
      algKM := algK D jE h
      Mray_gal := hgal
      Mray_ab := hab
      Mray_unr := hunr
      g_Mray := fun k => hsplit _ (hg k)
      iota := fun k _ w =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k)
      iota_inj := fun k _ w x y hx hy cx cy hxy =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom_inj (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) x y hx hy cx cy hxy
      Par := ParC D
      labPar := fun k σ v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut σ.1 (D.naut.plGw k v))
      labPar_monic := fun k σ v => σ.2.2.2.2 k v
      locPar := fun σ w => isoLoc D.nd D.naut σ.1 w
      locPar_dim := fun σ w => (GlobalTheory.RowPar.lpDim_isoLoc D.naut σ.1 w).trans σ.2.2.2.1
      labPar_def := fun _ _ _ => rfl
      MtPar := fun _ _ _ => ⊥
      AmbPar := fun _ _ => ⊥ }
  refine ⟨X, D.nStage_trivialCharacter_compat, D.nStage_trivialCharacter_coeff_eq, rfl, rfl, rfl, rfl, rfl, ⟨?_⟩, fun _ => ?_⟩
  · exact
      { eM := RingEquiv.refl _
        eM_K := fun _ => rfl
        eP := Equiv.refl _
        locPar_def := fun _ _ => rfl }
  · intro lam k v x
    rfl

end GlobalTheory.ParRay

end
end

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.Pst

theorem exists_bridges (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hpl : ∀ w, IsPlaceOver (pl w) w) :
    ∃ (LL : FinExt l) (br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) ↥(OL LL)),
      ∀ w hw, Induces (br w hw) := by
  have hfin : (placesOver E l).Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      simpa using (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  have := hfin.to_subtype
  choose j L0 hj hL using fun w : placesOver E l => GlobalTheory.PlaceBridge.exists_locBridge l E Ω w.1 (pl w.1) w.2 (hpl w.1)
  have := fun w => (L0 w).2
  let LL : FinExt l := ⟨⨆ w, (L0 w).1, inferInstance⟩
  choose br hb using fun w => hL w LL (le_iSup (fun w => (L0 w).1) w)
  exact ⟨LL, fun w hw => br ⟨w, hw⟩, fun w hw x => by rw [(hb _).1]; exact hj ⟨w, hw⟩ x⟩

theorem localPreds_of_isModel {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
    {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel B (resDec pl r w) L r') :
    (IsCrysW P pl br r w ↔ B.IsCrysE P L r') ∧
    (IsdRW P pl br r w ↔ B.IsdRE P L r') ∧
    (IsPotCrysW P pl br r w ↔ B.IsPotCrysE P L r') ∧
    ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' →
      (B.IsdRE P L r' → ∀ a : ℤ, a ∈ jumpsW P pl br r τ ↔ B.IsJumpE P L r' τ' a) ∧
      (B.IsdRE P L r' → ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a) := by
  have := L.2
  have := (br w hw).LL.2
  let L' : FinExt l := ⟨L.1 ⊔ (br w hw).LL.1, inferInstance⟩
  have l₁ : L.1 ≤ L'.1 := le_sup_left
  have l₂ : (br w hw).LL.1 ≤ L'.1 := le_sup_right
  have h' : IsModel (br w hw) (resDec pl r w) L' (mapRep (IntermediateField.inclusion l₁).toRingHom r') :=
    ⟨l₂, (h.enlarge l₁).2⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := local_of_isModel P hpl hbr h'
  obtain ⟨a₂, b₂, c₂, d₂⟩ := bridge_indep l P E Ω (pl w) O O' (br w hw) B (hbr w hw) hB L' l₂ m (mapRep (IntermediateField.inclusion l₁).toRingHom r')
  obtain ⟨a₃, b₃, c₃, d₃⟩ := local_ext P B l₁ r'
  have key : ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' → B.IsdRE P L r' →
      ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a := fun τ τ' hτ hd a => by
    obtain ⟨τ₁, t₁, e⟩ := d₂ τ ((IntermediateField.inclusion l₁).comp τ') hτ
    rw [(d₁ τ τ₁ t₁).2 (b₂.2 (b₃.2 hd)), e, d₃]
  refine ⟨a₁.trans (a₂.trans a₃), b₁.trans (b₂.trans b₃), c₁.trans (c₂.trans c₃), fun τ τ' hτ => ⟨fun hd a => ?_, key τ τ' hτ⟩⟩
  rw [isJumpE_iff P hd, ← key τ τ' hτ hd a, ← Multiset.count_ne_zero]
  exact Nat.cast_ne_zero.symm

theorem localPreds_of_bridge {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    (φ : O' →+* Om l) (hφ : ∀ x, φ x = ((B.toLL x : ↥B.LL.1) : Om l)) :
    (∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) O'),
      (IsCrysW P pl br (mapRep φ ρ) w ↔ B.IsCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep φ ρ) w ↔ B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep φ ρ) w ↔ B.IsPotCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1), IsInduced B τ τ' →
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep φ ρ) τ ↔ B.IsJumpW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep φ ρ) τ).count a : ℤ) = B.multW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a))) ∧
    ∀ (LL' : FinExt l), B.LL.1 ≤ LL'.1 → ∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) ↥LL'.1),
      (IsCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsPotCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced B τ τ' →
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ ↔ B.IsJumpE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ).count a : ℤ) =
            B.multE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a)) := by
  refine ⟨fun m ρ => ?_, fun LL' hL m ρ => ?_⟩
  · have h : IsModel B (resDec pl (mapRep φ ρ) w) B.LL (mapRep B.toLL (ρ.comp (Dec (F := E) (pl w)).subtype)) :=
      ⟨le_rfl, by ext g i j; exact (hφ _).symm⟩
    obtain ⟨a, b, c, d⟩ := localPreds_of_isModel P hpl hbr hw B hB h
    exact ⟨a, b, c, d⟩
  · have h : IsModel B (resDec pl (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w) LL' (ρ.comp (Dec (F := E) (pl w)).subtype) := ⟨hL, rfl⟩
    exact localPreds_of_isModel P hpl hbr hw B hB h

set_option maxHeartbeats 1000000 in

theorem nonempty_wdSide_of_tie (hB : GlobalTheory.Published.DeRhamPotSemistable) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Nonempty (WDSide D T) := by
  classical
  choose LL br hbr using fun (l : ℕ) (hl : Fact l.Prime) => exists_bridges l D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2
  let wd : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w :=
    fun l hl ι a r w => (T.e w).symm (if hw : w ∈ placesOver D.host.E l then
      wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw else GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r)
  have h1 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∈ placesOver D.host.E l), T.e w (wd l ι r w) = wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_pos hw]
  have h2 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∉ placesOver D.host.E l), T.e w (wd l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_neg hw]
  have hL := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w hw =>
    GlobalTheory.PstLaws.wdL_laws hB l (D.loc l) (D.locA l) (D.locT l) ι D.host.E D.nd.Om _ D.nd.plOm.1 (br l hl) D.nd.plOm.2 (hbr l hl) r w hw
  have hA := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : w ∉ placesOver D.host.E l) => GlobalTheory.WeilDeligne.wdOf_laws (D.nd.plOm.2 w) hw ι r
  refine ⟨{
    wdOf := wd
    wdOf_dim := fun l hl ι a r w => ?_
    wdOf_unr := fun l hl ι a r w hw hc => by rw [T.unr, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.1
    wdOf_frob := fun l hl ι a r w hw hc hu B σ hp hσ => ?_
    wdOf_ine := fun l hl ι a r w hw hc σ hσ => by rw [T.inePol _ _ σ hσ, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.1 σ hσ
    wdOf_mono0 := fun l hl ι a r w hw hc => by rw [T.mono0, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.2
    IsCrysW := fun l hl _ _ r w => IsCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsPotCrysW := fun l hl _ _ r w => IsPotCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsdRW := fun l hl _ _ r w => IsdRW (D.loc l) D.nd.plOm.1 (br l hl) r w
    jumpsW := fun l hl _ _ r τ => jumpsW (D.loc l) D.nd.plOm.1 (br l hl) r τ
    wdOf_unrL := fun l hl ι a r w hw hc hd => by rw [T.unr, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).1
    wdOf_mono0L := fun l hl ι a r w hw hc hd => by rw [T.mono0, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).2
    away := fun l hl ι a r w hw => h2 l ι r w hw
    above := fun l hl ι a r w hw => ⟨_, br l hl w hw, hbr l hl w hw, h1 l ι r w hw⟩
    loc := fun l hl ι w hw O _ _ _ Bw hj φ hφ => ⟨fun m ρ _ => ?_, fun LL' hL' m ρ _ => ?_⟩ }⟩
  · rw [← T.dim]
    by_cases hw : w ∈ placesOver D.host.E l
    · rw [h1 l ι r w hw]; exact (hL l ι r w hw).1
    · rw [h2 l ι r w hw]; exact (hA l ι r w hw).1
  · rw [T.frobEig _ _ hu, h2 l ι r w hw]
    rw [T.unr, h2 l ι r w hw] at hu
    exact ((hA l ι r w hw).2 hc).2.2.2.1 hu B σ hp hσ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).1 m ρ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).2 LL' hL' m ρ

end GlobalTheory.HeightCounting
end
end

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_wdSide : GlobalTheory.Published.DeRhamPotSemistable → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (WDSide D T) :=
  fun hB D T => nonempty_wdSide_of_tie hB D T

end GlobalTheory.HeightCounting
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TopA

def Concl (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Prop :=
  ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : SideA (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (CGTrue hL _ A.wdT) ∧ AUTrue hL _ A.wdT A.au ∧ RowTrue hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem concl_self (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (A : SideA D cf jE) (h1 : Nonempty (CGTrue hL D A.wdT))
    (h2 : AUTrue hL D A.wdT A.au) (h3 : RowTrue hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR)
    (h4 : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W)
    (h5 : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (h6 : LabConj D A.wdT) : Concl hL D cf jE rep :=
  ⟨lay0 D, ⟨D.Z_tie, D.Zgood_tie⟩, D.etaJ_tie, A, h1, h2, h3, h4, rfl, HEq.rfl, HEq.rfl, HEq.rfl, h5, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, h6⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem concl_setK (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk)
    (k1 : L.nd.PlG = D.nd.PlG) (k2 : HEq L.naut.plGw D.naut.plGw) (k3 : HEq L.ntypes.cenAmb D.ntypes.cenAmb)
    (k4 : HEq L.ntypes.cenMt D.ntypes.cenMt) (k5 : L.loc = D.loc) (k6 : HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd))
    (k7 : HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd))
    (k8 : HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd))
    (k9 : HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd))
    (h : Concl hL (setK D L hZ hη) (cfK L hZ hη cf) jE rep) : Concl hL D cf jE rep := by
  obtain ⟨L', hZ', hη', A, h1, h2, h3, h4, e1, e2, e3, e4, h5, e5, e6, e7, e8, e9, h6⟩ := h
  exact ⟨L', hZ', hη', A, h1, h2, h3, h4, e1.trans k1, e2.trans k2, e3.trans k3, e4.trans k4, h5, e5.trans k5, e6.trans k6,
    e7.trans k7, e8.trans k8, e9.trans k9, h6⟩

theorem exists_label_of_eq {g : ℕ} [Fact g.Prime] {t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ} (e : t' = t)
    (h : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (h' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t h ζ hζ)) (h1 : Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O) (h2 : LabTwLawO O) :
    ∃ O' : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t' h' ζ hζ), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O' ∧ LabTwLawO O' ∧
      ∀ r f, eSerO O' r f = eSerO O r f := by
  subst e
  exact ⟨O, h1, h2, fun _ _ => rfl⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_grp_setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 h0) (e1 : X.tg = D.ntypes.tg)
    (e2 : X.teichC = D.ntypes.teichC) (e3 : X.eSer = D.ntypes.eSer) (Γ : GrpSide D) :
    ∃ Γ' : GrpSide (setTy D hE X h1 h0), Γ'.ζ = Γ.ζ := by
  have hO := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_label_of_eq (congrFun e2 k) (D.ntypes.teichC_inj k) (X.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k) (Γ.O k) (Γ.O_equiv k) (Γ.O_tw k)
  choose O hO1 hO2 hO3 using hO
  refine ⟨{ tA := Γ.tA, tκ := Γ.tκ, teichC_def := fun k => ?_, ζ := Γ.ζ, ζ_gen := Γ.ζ_gen, O := O, eSer_def := fun k f => ?_
            kv := Γ.kv, tg_tame := fun k v => ?_, O_equiv := hO1, O_tw := hO2 }, rfl⟩
  · have := Γ.teichC_def k
    rw [← e2] at this
    exact this
  · exact ((congrFun (congrFun e3 k) f).trans (Γ.eSer_def k f)).trans (hO3 k _ f).symm
  · have := Γ.tg_tame k v
    rw [← e1] at this
    exact this

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem concl_of_au (hL : GlobalTheory.Published.LocalLanglandsGL) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : RowTrue hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (CGTrue hL D T)) (chr : CharSide D cf) (au : AUSide D) (hau : AUTrue hL D T au) : Concl hL D cf jE rep := by
  obtain ⟨Pl⟩ := GlobalTheory.HeightCounting.nonempty_plSide D
  obtain ⟨X, h1, h0, e1, e2, e3, e4, e5, ⟨par⟩, hι⟩ := GlobalTheory.ParRay.exists_types hR hC D hE jE Pl hray
  obtain ⟨Γ', hΓ⟩ := exists_grp_setTy D hE X h1 h0 e1 e2 e3 Γ
  obtain ⟨wd⟩ := GlobalTheory.HeightCounting.exists_wdSide hdR (setTy D hE X h1 h0) T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setTy D hE X h1 h0) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlab' : LabTrue (setTy D hE X h1 h0) T := by
    intro k v a
    have := hlab k v a
    rw [← e1, ← e2] at this
    exact this
  have hconj' : LabConj (setTy D hE X h1 h0) T := by
    intro k v w hw
    have := hconj k v w hw
    rw [← e1, ← e2] at this
    exact this
  have hχ' : ChiTOk (setTy D hE X h1 h0) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← e1, ← e2] at this
    exact this
  have hT' : GlobalTheory.Mem.Top.TypesTrue X cf.P cf.W :=
    ⟨hT.pl, fun k => (congrFun e2 k).trans (hT.teich k), hT.chi, fun k p => (congrFun (congrFun e3 k) p).trans (hT.ser k p)⟩
  have H : Concl hL (setTy D hE X h1 h0) cf' jE rep :=
    concl_self hL (setTy D hE X h1 h0) cf' jE rep
      { bare := hE, wdT := T, lab := hlab', chr := { chr with }, row := ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩
        pl := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩, iota := hι ⟨Γ⟩, wd := wd, grp := Γ', par := par, au := { au with }
        chiT := hχ' }
      ⟨{ cg with }⟩ hau hrow hT' (fun k => (congrFun hΓ k).trans (hζ k)) hconj'
  exact concl_setK hL D cf jE rep (lay0 (setTy D hE X h1 h0)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl (heq_of_eq e4) (heq_of_eq e5) rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem concl_of_cg (hL : GlobalTheory.Published.LocalLanglandsGL) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : RowTrue hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (CGTrue hL D T)) (chr : CharSide D cf) : Concl hL D cf jE rep := by
  obtain ⟨C, au, hau⟩ := GlobalTheory.T.exists_automorphic_side_empty_local hL D hE T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setBC D C) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have H : Concl hL (setBC D C) cf' jE rep :=
    concl_of_au hL hdR hR hC (setBC D C) hE cf' jE rep hray hT { Γ with } hζ hχ T hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow
      ⟨{ cg with }⟩ { chr with } au hau
  exact concl_setK hL D cf jE rep (lay0 (setBC D C)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem concl_of_lp (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : RowTrue hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR) :
    Concl hL D cf jE rep := by
  obtain ⟨K, hcg, ⟨chr⟩⟩ := GlobalTheory.HeightCounting.exists_cgTrue_charSide hL hA D hE T cf hT.pl
  have H : Concl hL (setCG D hE K) (cfCG hE K cf) jE rep :=
    concl_of_cg hL hdR hR hC (setCG D hE K) hE (cfCG hE K cf) jE rep hray ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩ { Γ with } hζ hχ
      (wdCG hE K T) hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow hcg chr
  exact concl_setK hL D cf jE rep (lay0 (setCG D hE K)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H

theorem exists_kv_of_eq (D : D7) {g : ℕ} [Fact g.Prime] {w w' : PlE D.host} (e : w' = w) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 w) ≃+* Formalism.CyclotomicNorms.Fbar g)
    (h : TameCoupled (D.nd.plOm.1 w) κ σ ζ) :
    ∃ κ' : IsLocalRing.ResidueField (D.nd.plOm.1 w') ≃+* Formalism.CyclotomicNorms.Fbar g, TameCoupled (D.nd.plOm.1 w') κ' σ ζ := by
  subst e
  exact ⟨κ, h⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem concl_of_grp (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (hd : RowDepth D rep) : Concl hL D cf jE rep := by
  obtain ⟨Rw, hRw⟩ := GlobalTheory.RowPar.exists_rowWD_rowTrue hL D rep hd
  obtain ⟨lab, h, A, C, tm, tg, hl, hpl, T, hlab, hconj, Rs, hp, hs⟩ := GlobalTheory.HeightCounting.exists_setAut_wdTie_labConj D hE Rw
  let cf' : CharFrame (setAut D hE lab h A C tm tg hl) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hk := fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_kv_of_eq D (hpl k v) (D.ntypes.tg k v) (Γ.ζ k) (Γ.kv k v) (Γ.tg_tame k v)
  choose kv hkv using hk
  have hχ' : ChiTOk (setAut D hE lab h A C tm tg hl) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← hpl k v] at this
    exact this
  have hrow : RowTrue hL (setAut D hE lab h A C tm tg hl) rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR := by
    have e1 : (fun σ w => T.e w (Rs.locR σ w)) = Rw.par := funext fun σ => funext fun w => hp σ w
    have e2 : Rs.satR = Rw.sat := funext fun σ => funext fun w => hs σ w
    rw [e1, e2]
    exact hRw
  have hT' : GlobalTheory.Mem.Top.TypesTrue (setAut D hE lab h A C tm tg hl).ntypes cf.P cf.W :=
    ⟨fun k v => (hpl k v).symm ▸ hT.pl k v, hT.teich, hT.chi, hT.ser⟩
  have H : Concl hL (setAut D hE lab h A C tm tg hl) cf' jE rep :=
    concl_of_lp hA hL hdR hR hC (setAut D hE lab h A C tm tg hl) hE cf' jE rep hray hT'
      { Γ with kv := kv, tg_tame := hkv } hζ hχ' T hlab hconj Rs hrow
  exact concl_setK hL D cf jE rep (lay0 (setAut D hE lab h A C tm tg hl)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl (heq_of_eq (funext fun k => funext fun v => hpl k v)) HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H

theorem exists_eq_of_heq {P P' : Fin 2 → Type} {β : Type} (e : P' = P) {f : ∀ k, P k → β} {f' : ∀ k, P' k → β} (h : HEq f' f)
    (k : Fin 2) (v : P' k) : ∃ v₀, f k v₀ = f' k v := by
  subst e
  exact ⟨v, by rw [eq_of_heq h]⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_sideA : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → RowDepth D rep → (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : SideA (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (CGTrue hL _ A.wdT) ∧ AUTrue hL _ A.wdT A.au ∧ RowTrue hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT := by
  intro hL hA hdR hG hAr hR hC D hE cf jE rep hz hT hd hray
  obtain ⟨L, hZ, hη, hE', hT', k1, k2, k3, k4, ⟨Γ, hζ⟩, hχ, k5, k6, k7, k8, k9⟩ := GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling hG hAr D hE cf hz hT
  have hd' : RowDepth (setK D L hZ hη) rep := by
    intro σ k v
    obtain ⟨v₀, e⟩ := exists_eq_of_heq k1 k2 k v
    obtain ⟨s, τ, h1, h2⟩ := hd σ k v₀
    exact ⟨s, τ, h1.trans e, h2⟩
  exact concl_setK hL D cf jE rep L hZ hη k1 k2 k3 k4 k5 k6 k7 k8 k9
    (concl_of_grp hA hL hdR hR hC (setK D L hZ hη) hE' (cfK L hZ hη cf) jE rep hray hT' Γ hζ hχ hd')

end GlobalTheory.HeightCounting.TopA

end
end
