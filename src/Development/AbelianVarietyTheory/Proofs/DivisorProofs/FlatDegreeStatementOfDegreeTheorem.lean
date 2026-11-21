import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat

section
set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HostModel

namespace GlobalTheory.HostRamif

variable {E : Type} [Field E] [NumberField E]

theorem intCast_mem_iff {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal) (hlw : (l : 𝓞 E) ∈ w) (n : ℤ) :
    (n : 𝓞 E) ∈ w ↔ (l : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hc : IsCoprime (l : ℤ) n := ((Nat.prime_iff_prime_int.mp hl).irreducible.coprime_iff_not_dvd).2 hnd
    obtain ⟨a, b, hab⟩ := hc
    apply hw.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 E) = (a : 𝓞 E) * (l : 𝓞 E) + (b : 𝓞 E) * (n : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [h1]
    exact add_mem (w.mul_mem_left _ hlw) (w.mul_mem_left _ hn)
  · rintro ⟨c, rfl⟩
    push_cast
    exact w.mul_mem_right _ hlw

theorem dvd_different_iff [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal)
    (hlw : (l : 𝓞 E) ∈ w) : w ∣ differentIdeal ℤ (𝓞 E) ↔ (l : ℤ) ∣ discr E := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hwp := hw.isPrime
  haveI : w.LiesOver (Ideal.span {(l : ℤ)}) := (Ideal.liesOver_span_iff hw.ne_top hp).mpr (by simpa using hlw)
  rw [← not_iff_not, not_dvd_differentIdeal_iff, not_dvd_discr_iff_forall_liesOver E (𝓞 E) hp]
  refine ⟨fun h P hP hPl => ?_, fun h => h w hw inferInstance⟩
  have hPp := hP.isPrime
  rw [← Ideal.ramificationIdx_eq_one_iff] at h ⊢
  rw [← h]
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) _ _ (E ≃ₐ[ℚ] E)

variable [IsCMField E]

theorem exists_coords (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    ∃ x y : ℤ, a = x + y * H.w0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 4 * k + 3 := ⟨H.d / 4, by have := H.d_mod; omega⟩
  have hsq : H.w0 ^ 2 = H.w0 - (k + 1) := by
    have h := H.rt_sq
    rw [rt_eq, hk] at h
    push_cast at h
    apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
    linear_combination h
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, y, rfl⟩ := ha
    obtain ⟨x', y', rfl⟩ := hb
    exact ⟨x + x', y + y', by push_cast; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, y, rfl⟩ := ha
    obtain ⟨x', y', rfl⟩ := hb
    exact ⟨x * x' - y * y' * (k + 1), x * y' + y * x' + y * y', by
      push_cast; linear_combination (y : 𝓞 E) * y' * hsq⟩

theorem isSquare_iff (H : Host E) {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal)
    (hlw : (l : 𝓞 E) ∈ w) (hd : l ≠ H.d) :
    IsSquare (-(H.d : ZMod l)) ↔ ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w := by
  have hwp := hw.isPrime
  haveI := Fact.mk hl
  have h1 : (1 : 𝓞 E) ∉ w := fun h => hw.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hw0 : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ _
  by_cases h2 : l = 2
  · subst h2
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 8 * k + 7 := ⟨H.d / 8, by have := H.d_mod; omega⟩
      have hsq : H.w0 * (1 - H.w0) = (k + 1) * ((2 : ℕ) : 𝓞 E) := by
        have h := H.rt_sq
        rw [rt_eq, hk] at h
        push_cast at h ⊢
        apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
        linear_combination -h
      have hm : H.w0 * (1 - H.w0) ∈ w := hsq ▸ w.mul_mem_left _ hlw
      rcases hwp.mem_or_mem hm with h | h
      · refine ⟨_, hw0, h, fun h' => h1 ?_⟩
        rw [cmHost_bar_halfIntegerGenerator] at h'
        simpa using add_mem h h'
      · refine ⟨_, sub_mem (one_mem _) hw0, h, fun h' => h1 ?_⟩
        rw [map_sub, map_one, cmHost_bar_halfIntegerGenerator] at h'
        simpa using add_mem h h'
    · generalize (-(H.d : ZMod 2)) = z
      revert z
      decide
  · have hl2 : ¬ (l : ℤ) ∣ 2 := fun h => h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by exact_mod_cast h))
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
      have hdv : (l : ℤ) ∣ -(H.d : ℤ) - s * s := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hs, sub_self]
      have hm : (H.rt - s) * (-H.rt - s) ∈ w := by
        have := (intCast_mem_iff hl hw hlw _).2 hdv
        have e : (H.rt - s) * (-H.rt - s) = -((-(H.d : ℤ) - s * s : ℤ) : 𝓞 E) := by
          push_cast
          linear_combination -H.rt_sq
        rw [e]
        exact neg_mem this
      have hnb : ¬ (H.rt - s ∈ w ∧ -H.rt - s ∈ w) := by
        rintro ⟨ha, hb⟩
        have : ((2 * s : ℤ) : 𝓞 E) ∈ w := by
          have e : ((2 * s : ℤ) : 𝓞 E) = -((H.rt - s) + (-H.rt - s)) := by push_cast; ring
          rw [e]
          exact neg_mem (add_mem ha hb)
        have hs' := (hp.dvd_or_dvd ((intCast_mem_iff hl hw hlw _).1 this)).resolve_left hl2
        have : (l : ℤ) ∣ (H.d : ℤ) := by
          have := dvd_add hdv (hs'.mul_right s)
          simpa using this
        exact hd ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 (by exact_mod_cast this))
      rcases hwp.mem_or_mem hm with h | h
      · refine ⟨_, sub_mem (rt_mem_adjoin H) (intCast_mem _ s), h, fun h' => hnb ⟨h, ?_⟩⟩
        rwa [map_sub, bar_rt, map_intCast] at h'
      · refine ⟨_, sub_mem (neg_mem (rt_mem_adjoin H)) (intCast_mem _ s), h, fun h' => hnb ⟨?_, h⟩⟩
        rwa [map_sub, map_neg, bar_rt, neg_neg, map_intCast] at h'
    · rintro ⟨a, ha, haw, hbw⟩
      obtain ⟨x, y, rfl⟩ := exists_coords H ha
      have hb : H.bar (x + y * H.w0) = x + y * (1 - H.w0) := by
        rw [map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
      rw [hb] at hbw
      have hy : ¬ (l : ℤ) ∣ y := by
        intro hy
        apply hbw
        have hyw := (intCast_mem_iff hl hw hlw _).2 hy
        have e : (x : 𝓞 E) + y * (1 - H.w0) = (x + y * H.w0) + y * (1 - 2 * H.w0) := by ring
        rw [e]
        exact add_mem haw (w.mul_mem_right _ hyw)
      have hn : (l : ℤ) ∣ (2 * x + y) ^ 2 + H.d * y ^ 2 := by
        rw [← intCast_mem_iff hl hw hlw]
        have e : (((2 * x + y) ^ 2 + H.d * y ^ 2 : ℤ) : 𝓞 E) =
            (x + y * H.w0) * (4 * (x + y * (1 - H.w0))) := by
          have h := H.rt_sq
          rw [rt_eq] at h
          push_cast
          linear_combination (y : 𝓞 E) ^ 2 * h
        rw [e]
        exact w.mul_mem_right _ haw
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hn hy
      push_cast at hn
      refine ⟨(2 * x + y) / y, ?_⟩
      field_simp
      linear_combination -hn

theorem isHostField_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    EigenvectorLieDegree.IsHostField H ↔ IsAbelianGalois ℚ E ∧ AdelicDegreeTameRamification.TameAtRamified H := by
  intro E _ _ _ H
  unfold EigenvectorLieDegree.IsHostField AdelicDegreeTameRamification.TameAtRamified
  refine and_congr_right fun hab => ⟨fun h l w hl hld hw hlw => ?_, fun h w hwd => ?_⟩
  · have hne : w ≠ ⊥ := by
      rintro rfl
      exact hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hlw))
    obtain ⟨h1, h2⟩ := h ⟨w, hw.isPrime, hne⟩ ((dvd_different_iff hl hw hlw).2 hld)
    refine ⟨h1, fun hd => ?_, fun hd => ?_⟩
    · rcases h2 l hl hlw with h3 | h3
      · exact (isSquare_iff H hl hw hlw hd).1 h3.2
      · exact absurd h3.1 hd
    · rcases h2 l hl hlw with h3 | h3
      · exact absurd hd h3.1
      · exact fun h4 => h3.2 (Ideal.dvd_span_singleton.2 h4)
  · have hw := w.isMaximal
    refine ⟨?_, fun l hl hlw => ?_⟩
    · obtain ⟨l, hl, hlw⟩ : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ w.asIdeal := by
        haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
        letI := Ideal.Quotient.field w.asIdeal
        refine ⟨ringChar (𝓞 E ⧸ w.asIdeal), CharP.char_is_prime (𝓞 E ⧸ w.asIdeal) _, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
        exact ringChar.Nat.cast_ringChar
      exact (h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw).1
    · obtain ⟨-, h2, h3⟩ := h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw
      by_cases hd : l = H.d
      · exact Or.inr ⟨hd, fun h4 => h3 hd (Ideal.dvd_span_singleton.1 h4)⟩
      · exact Or.inl ⟨hd, (isSquare_iff H hl hw hlw hd).2 (h2 hd)⟩

end GlobalTheory.HostRamif
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

theorem hasModel_of_goodAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)), 1 ≤ D.p + D.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ 𝔭 : HeightOneSpectrum (𝓞 k), HasModel o.t 𝔭 := by
  intro E _ _ _ H D l c k _ _ j o e hg hA 𝔭
  obtain ⟨Xo⟩ := Moduli.moduli_scheme_exists E H D l e
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, -⟩ := Xo.rep _ _ inferInstance o
  obtain ⟨Y⟩ := (GlobalTheory.Reg.modelAt_and_nonempty_global_model E H D l Xo c e hg hA).2
  let y : Sp k ⟶ Xo.XF c := pullback.lift f (spMap j) hf
  have hy : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  let oV : 𝓞 c.F →+* AdelicDegreeTameRamification.valRing k 𝔭 :=
    (j.comp (algebraMap (𝓞 c.F) c.F)).codRestrict (AdelicDegreeTameRamification.valRing k 𝔭) fun a =>
      𝔭.valuation_le_one (K := k) (RingOfIntegers.mapRingHom j a)
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, h⟩ := ValuativeExtension.valuation_extension E H D l Xo c _ _ Y
    (AdelicDegreeTameRamification.valRing k 𝔭) k oV j y rfl (pullback.lift_snd _ _ _)
  obtain ⟨G, ⟨n⟩⟩ := h yt
  obtain ⟨m₁, -⟩ := ObjMaps.exists_sab_cancel (g := y) Y.m0.toSABMap (hy ▸ m.toSABMap)
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp Y.m m₁
  obtain ⟨m₃, -⟩ := ObjMaps.exists_sab_cancel (g := spMap (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k)) n (hyt ▸ m₂)
  exact ⟨G.G, inferInstance, m₃.φ, G.semi, m₃.cart⟩

end GlobalTheory.FlatDegreeCompare
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_reduction_model_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)), 1 ≤ D.p + D.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ 𝔭 : HeightOneSpectrum (𝓞 k), HasModel o.t 𝔭 := by
  atlas_forward_decl GlobalTheory.FlatDegreeCompare.hasModel_of_goodAt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_weighted_log_norm_sum : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k'), ∃ (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓) ∧ ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧ (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) = (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
  first | exact @GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm | exact GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm | (intros; apply GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_sum_degree_formula : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (f : (k →+* ℂ) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  first | exact @GlobalTheory.finrank_mul_sum_embeddings_comp | exact GlobalTheory.finrank_mul_sum_embeddings_comp | (intros; apply GlobalTheory.finrank_mul_sum_embeddings_comp <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

theorem ideal_le_prime_pow_iff_le_count {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) (n : ℕ) :
    J ≤ v.asIdeal ^ n ↔ n ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  classical
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

theorem count_map_ideal_eq_mul_of_valuation_pow (k k' : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] (i : k →+* k') (J : Ideal (𝓞 k)) (𝔭 : HeightOneSpectrum (𝓞 k))
    (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ)
    (h : ∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) :
    FractionalIdeal.count k' 𝔓 ((J.map (RingOfIntegers.mapRingHom i) : Ideal (𝓞 k')) :
      FractionalIdeal (nonZeroDivisors (𝓞 k')) k') =
    ε * FractionalIdeal.count k 𝔭 (J : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  classical
  by_cases hJ : J = 0
  · subst hJ
    simp [FractionalIdeal.count_zero]
  have hv : ∀ x : 𝓞 k, 𝔓.intValuation (RingOfIntegers.mapRingHom i x) = 𝔭.intValuation x ^ ε := by
    intro x
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := k'),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := k), ← h]
    rfl
  have hinj : Function.Injective (RingOfIntegers.mapRingHom i) := by
    intro x y hxy
    apply RingOfIntegers.ext
    apply i.injective
    exact congrArg (fun t : 𝓞 k' => (t : k')) hxy
  have hJ' : J.map (RingOfIntegers.mapRingHom i) ≠ 0 := fun h0 =>
    hJ ((Ideal.map_eq_bot_iff_of_injective hinj).mp h0)
  rw [FractionalIdeal.count_coe k' 𝔓 hJ', FractionalIdeal.count_coe k 𝔭 hJ]
  set m := (Associates.mk 𝔭.asIdeal).count (Associates.mk J).factors with hm
  set m' := (Associates.mk 𝔓.asIdeal).count
    (Associates.mk (J.map (RingOfIntegers.mapRingHom i))).factors with hm'
  have hle : J ≤ 𝔭.asIdeal ^ m := (ideal_le_prime_pow_iff_le_count 𝔭 hJ m).mpr le_rfl
  have hle' : J.map (RingOfIntegers.mapRingHom i) ≤ 𝔓.asIdeal ^ m' :=
    (ideal_le_prime_pow_iff_le_count 𝔓 hJ' m').mpr le_rfl
  have hnle : ¬ J ≤ 𝔭.asIdeal ^ (m + 1) := fun h1 => by
    have := (ideal_le_prime_pow_iff_le_count 𝔭 hJ (m + 1)).mp h1
    omega
  have h1 : ε * m ≤ m' := by
    apply (ideal_le_prime_pow_iff_le_count 𝔓 hJ' _).mp
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← 𝔓.intValuation_le_pow_iff_mem, hv]
    have hx' := (𝔭.intValuation_le_pow_iff_mem x m).mpr (hle hx)
    refine (pow_le_pow_left' hx' ε).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    push_cast
    simp
  have h2 : m' ≤ ε * m := by
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnle
    have hx0 : x ≠ 0 := fun h0 => hxn (h0 ▸ zero_mem _)
    rw [← 𝔭.intValuation_le_pow_iff_mem, not_le] at hxn
    have hx' := (𝔭.intValuation_le_pow_iff_mem x m).mpr (hle hx)
    have h3 := (𝔓.intValuation_le_pow_iff_mem _ m').mpr (hle' (Ideal.mem_map_of_mem _ hx))
    rw [hv] at h3
    have hne : 𝔭.intValuation x ≠ 0 := 𝔭.intValuation_ne_zero x hx0
    rw [← WithZero.exp_log hne] at hxn hx' h3
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp] at h3
    rw [WithZero.exp_lt_exp] at hxn
    rw [WithZero.exp_le_exp] at hx'
    have h4 : WithZero.log (𝔭.intValuation x) = -(m : ℤ) := by
      push_cast at hxn
      omega
    rw [h4, nsmul_eq_mul] at h3
    have : (m' : ℤ) ≤ ε * m := by linarith
    exact_mod_cast this
  have : m' = ε * m := le_antisymm h2 h1
  rw [this]
  push_cast
  ring

theorem count_map_comp_ideal_eq_mul_of_valuation_pow : ∀ (E : Type) [Field E] [NumberField E] (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (τ : E →+* k) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → FractionalIdeal.count k' 𝔓 ((𝔞.map (RingOfIntegers.mapRingHom (i.comp τ)) : Ideal (𝓞 k')) : FractionalIdeal (nonZeroDivisors (𝓞 k')) k') = ε * FractionalIdeal.count k 𝔭 ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 k)) : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  intro E _ _ k k' _ _ _ _ i τ 𝔞 𝔭 𝔓 ε h
  have hc : RingOfIntegers.mapRingHom (i.comp τ) =
      (RingOfIntegers.mapRingHom i).comp (RingOfIntegers.mapRingHom τ) := by
    ext x
    rfl
  rw [hc, ← Ideal.map_map]
  exact count_map_ideal_eq_mul_of_valuation_pow k k' i _ 𝔭 𝔓 ε h

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_count_under_extension : ∀ (E : Type) [Field E] [NumberField E] (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (τ : E →+* k) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → FractionalIdeal.count k' 𝔓 ((𝔞.map (RingOfIntegers.mapRingHom (i.comp τ)) : Ideal (𝓞 k')) : FractionalIdeal (nonZeroDivisors (𝓞 k')) k') = ε * FractionalIdeal.count k 𝔭 ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 k)) : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  atlas_forward_decl GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.EigBasisExtend

theorem eig_rows_map {k K O : Type} [Field k] [Field K] (i : k →+* K) {m n : ℕ} {P : Matrix (Fin m) (Fin n) k}
    (hP : ∀ c, c ᵥ* P = 0 → c = 0) (A : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (h : ∀ c, (∀ a, c ᵥ* A a = χ a • c) → ∃ d, d ᵥ* P = c) (c : Fin n → K)
    (hc : ∀ a, c ᵥ* (A a).map i = i (χ a) • c) : ∃ d, d ᵥ* P.map i = c := by
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear P).exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 hP)
  have h1 : P * LinearMap.toMatrixRight' g = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear P = _
    simpa using hg
  set Q := LinearMap.toMatrixRight' g
  let := i.toAlgebra
  have key : ∀ (l : K →ₗ[k] k) {p q : ℕ} (M : Matrix (Fin p) (Fin q) k) (v : Fin p → K),
      (fun j => l ((v ᵥ* M.map i) j)) = (fun j => l (v j)) ᵥ* M := fun l p q M v => by
    funext j
    simp only [Matrix.vecMul, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [_root_.mul_comm (v s), _root_.mul_comm (l _), ← smul_eq_mul (M s j), ← map_smul, Algebra.smul_def]
    rfl
  refine ⟨c ᵥ* Q.map i, funext fun j => sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff k _).1 fun l => ?_)⟩
  obtain ⟨d, hd⟩ := h (fun j => l (c j)) fun a => by
    rw [← key, hc]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← smul_eq_mul (χ a), ← map_smul, Algebra.smul_def]
    rfl
  have e := congrFun (key l P (c ᵥ* Q.map i)) j
  rw [key, ← hd, Matrix.vecMul_vecMul d, h1, Matrix.vecMul_one, hd] at e
  rw [map_sub, e, sub_self]

theorem isEigVec_iff {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) (χ : O →+* R) {n : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e)
    {A : O → Matrix (Fin n) (Fin n) R} (hA : ∀ a j, IsLieComb (A a j) e (e j ≫ act.act a))
    {c : Fin n → R} {w : epsR R ⟶ G} (hw : IsLieComb c e w) :
    EigenvectorLieDegree.IsEigVec act χ w ↔ ∀ a, c ᵥ* A a = χ a • c := by
  let b := Serre.Lie.basis act he
  have hb : (fun j => (b j).hom) = e := funext (Serre.Lie.hom_basis he)
  clear_value b
  subst hb
  obtain rfl := (Serre.Lie.isLieComb_iff c b w).1 hw
  have hA' : ∀ a j, a • b j = ∑ s, A a j s • b s := fun a j =>
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff _ b _).1 (hA a j))
  have h1 : ∀ a, a • ∑ j, c j • b j = ∑ s, (c ᵥ* A a) s • b s := fun a => by
    simp only [Finset.smul_sum, smul_comm a, hA', Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 : ∀ a, χ a • ∑ j, c j • b j = ∑ s, (χ a • c) s • b s := fun a => by
    simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  refine (and_iff_right (Serre.Lie.isTangent _)).trans (Serre.Lie.mem_eig_iff_left.symm.trans ?_)
  rw [Serre.Lie.mem_eig_iff]
  refine forall_congr' fun a => ?_
  rw [h1, h2, ← b.equivFun_symm_apply, ← b.equivFun_symm_apply, EmbeddingLike.apply_eq_iff_eq]

theorem isEigBasis_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (χ : 𝓞 E →+* k), (∀ a, IsVecOver i n.φ (x a) (x' a)) → EigenvectorLieDegree.IsEigBasis t.act χ x → EigenvectorLieDegree.IsEigBasis t'.act (i.comp χ) x' := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' χ hx' hx
  have hi := Indep.of_eigBasis hx
  have := t.semi.smooth
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  choose e' h _ using fun j => existsUnique_isVecOver n.cart.1 (e j)
  have he' := Chart.isLieBasis_baseChange i n.cart he h
  choose P hP _ using fun s => he.2 _ (hi.1 s)
  have hP' : ∀ s, IsLieComb ((Matrix.of P).map i s) e' (x' s) := fun s =>
    (lieComb_baseChange _ _ i t.G t'.G n.φ n.cart N e (x s) (P s) e' (x' s) h (hP s)).1 (hx' s)
  choose A hA _ using fun a j => he.2 (e j ≫ t.act.act a) (Serre.Lie.isTangent (a • Serre.Lie.mk t.act (e j) (he.1 j)))
  have hA' : ∀ a j, IsLieComb ((Matrix.of (A a)).map i j) e' (e' j ≫ t'.act.act a) := fun a j =>
    (lieComb_baseChange _ _ i t.G t'.G n.φ n.cart N e _ (A a j) e' _ h (hA a j)).1 (by
      have := h j
      simp only [IsVecOver] at this ⊢
      rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  have hinj := hi.vecMul_eq_zero (P := Matrix.of P) he.1 hP
  have E1 := fun c w => isEigVec_iff t.act χ he (A := fun a => Matrix.of (A a)) hA (c := c) (w := w)
  have E2 := fun c w => isEigVec_iff t'.act (i.comp χ) he' (A := fun a => (Matrix.of (A a)).map i) hA' (c := c) (w := w)
  have tx : ∀ s, IsTangent (x' s) := fun s => (hx' s).isTangent n.cart (hi.1 s)
  refine ⟨fun s => (E2 _ _ (hP' s)).2 fun a => ?_, fun w hw => ?_⟩
  · have := (E1 _ _ (hP s)).1 (hx.1 s) a
    funext j
    have := congrArg i (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨c, hc, -⟩ := he'.2 w hw.1
    obtain ⟨d, hd⟩ := eig_rows_map i hinj (fun a => Matrix.of (A a)) χ (fun c hc => by
      obtain ⟨w, hw⟩ := ((LieComb.lieComb_algebra k t.G N e he.1).1 c).exists
      obtain ⟨d, hd, -⟩ := hx.2 w ((E1 _ _ hw).2 hc)
      exact ⟨d, (Indep.of_basis he).2 _ _ w ((comb_comb (P := Matrix.of P) he.1 hP _ _).1 hd) hw⟩) c
      ((E2 _ _ hc).1 hw)
    refine ⟨d, (comb_comb he'.1 hP' _ _).2 (hd ▸ hc), fun d' hd' => ?_⟩
    refine sub_eq_zero.1 (vecMul_map_eq_zero i hinj _ ?_)
    rw [Matrix.sub_vecMul, hd, (Indep.of_basis he').2 _ _ w ((comb_comb he'.1 hP' _ _).1 hd') hc, sub_self]

end GlobalTheory.EigBasisExtend
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (χ : 𝓞 E →+* k), (∀ a, IsVecOver i n.φ (x a) (x' a)) → EigenvectorLieDegree.IsEigBasis t.act χ x → EigenvectorLieDegree.IsEigBasis t'.act (i.comp χ) x' := by
  first | exact @GlobalTheory.EigBasisExtend.isEigBasis_extend | exact GlobalTheory.EigBasisExtend.isEigBasis_extend | (intros; apply GlobalTheory.EigBasisExtend.isEigBasis_extend <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.EigBasisExist

theorem exists_eigBasis_of_lieMult {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) (χ : O →+* k) {n : ℕ} (h : LieMult act (𝟙 (Sp k)) χ n) :
    ∃ x : Fin n → (epsR k ⟶ G), EigenvectorLieDegree.IsEigBasis act χ x := by
  obtain ⟨b⟩ := (Serre.Lie.lieMult_id_iff act χ n).1 h
  have hm : ∀ v : Serre.Lie act, v ∈ Serre.Lie.eig act χ ↔ EigenvectorLieDegree.IsEigVec act χ v.hom := fun v =>
    ⟨fun hv => ⟨v.isTangent, fun a => congrArg (fun z : Serre.Lie act => z.hom.left) (hv a)⟩,
      fun hv a => Serre.Lie.ext (Over.OverMorphism.ext (hv.2 a))⟩
  refine ⟨fun i => (b i : Serre.Lie act).hom, fun i => (hm _).1 (b i).2, fun w hw => ?_⟩
  let z : Serre.Lie.eig act χ := ⟨Serre.Lie.mk act w hw.1, (hm _).2 hw⟩
  have key : ∀ c : Fin n → k, IsLieComb c (fun i => (b i : Serre.Lie act).hom) w ↔ b.equivFun z = c := fun c => by
    rw [Serre.Lie.isLieComb_iff c (fun i => (b i : Serre.Lie act)) w, ← LinearEquiv.eq_symm_apply,
      Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact ⟨fun e => Serre.Lie.ext e, fun e => congrArg Serre.Lie.hom e⟩
  exact (existsUnique_congr key).2 existsUnique_eq'

theorem exists_eigBases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → (∃ x : Fin D.p → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j τ).comp (algebraMap (𝓞 E) E)) x) ∧ ∃ x : Fin D.q → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j (conjEmb τ)).comp (algebraMap (𝓞 E) E)) x := by
  intro E _ _ _ H D l c k _ _ j o τ hτ
  let φ : k →+* AlgebraicClosure k := algebraMap k _
  have := o.t.semi.smooth
  have d := (o.geom (AlgebraicClosure k) (spMap φ)
    (φ.comp (j.comp (IntermediateField.inclusion c.le).toRingHom))
    (by rw [spMap_comp_spMap, spMap_comp_spMap])).1
  have iff : ∀ σ : E →+* ℂ, (φ.comp ((EigenvectorLieDegree.embIn c j σ).comp (algebraMap (𝓞 E) E))) H.rt =
      (φ.comp (j.comp (IntermediateField.inclusion c.le).toRingHom)) (baseKA l).ρ ↔ σ (H.rt : E) = H.rt0 := fun σ =>
    (φ.injective.eq_iff.trans j.injective.eq_iff).trans Subtype.ext_iff
  have ne : conjEmb τ (H.rt : E) ≠ H.rt0 := fun e => by
    have e' : (starRingEnd ℂ) H.rt0 = H.rt0 := by rw [← hτ]; exact e.trans hτ.symm
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e'
    have h := H.sqrt_neg_disc_sq
    rw [hr] at h
    have h' : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg r]
  exact ⟨exists_eigBasis_of_lieMult _ _ ((LieExt.lieMult_extend_iff φ _ _ _ _).1 ((d _).1 ((iff τ).2 hτ))),
    exists_eigBasis_of_lieMult _ _ ((LieExt.lieMult_extend_iff φ _ _ _ _).1 ((d _).2 fun e => ne ((iff _).1 e)))⟩

end GlobalTheory.EigBasisExist
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_signature_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → (∃ x : Fin D.p → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j τ).comp (algebraMap (𝓞 E) E)) x) ∧ ∃ x : Fin D.q → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j (conjEmb τ)).comp (algebraMap (𝓞 E) E)) x := by
  atlas_forward_decl GlobalTheory.EigBasisExist.exists_eigBases
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.FlatDegreeCompare.ArchExists

theorem linearIndependent_of_indep {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g n : ℕ}
    (u : HolUnif A L g) (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : Indep v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun (hv.2 _ _ w h2 h2')

end GlobalTheory.FlatDegreeCompare.ArchExists
end
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

theorem isArchNormSq_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (σ : k' →+* ℂ) (N : ℝ), (∀ a, IsVecOver i n.φ (x a) (x' a)) → AdelicDegreeTameRamification.IsArchNormSq t x (σ.comp i) N → AdelicDegreeTameRamification.IsArchNormSq t' x' σ N := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' σ N hx ⟨t'', p, g, u, Hm, α, y, W, h₁, h₂, h₃⟩
  have key : ∀ (f : Sp ℂ ⟶ Sp k) (q : SABMap t'' t f), f = spMap σ ≫ spMap i →
      ∃ m' : SABMap t'' t' (spMap σ), q.φ = m'.φ ≫ n.φ := by
    rintro f q rfl
    exact ObjMaps.exists_sab_cancel n q
  obtain ⟨m', hm'⟩ := key _ p (spMap_comp_spMap i σ).symm
  refine ⟨t'', m', g, u, Hm, α, y, W, h₁, fun a => ?_, h₃⟩
  refine EllComp.isVecOver_cancel (f := i) (g := σ) (φ := n.φ) (ψ := m'.φ) (v := x a) n.cart.1 m'.cart.1 (hx a) ?_
  rw [← hm']
  exact h₂ a

end GlobalTheory.FlatDegreeCompare
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_norm_square_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (σ : k' →+* ℂ) (N : ℝ), (∀ a, IsVecOver i n.φ (x a) (x' a)) → AdelicDegreeTameRamification.IsArchNormSq t x (σ.comp i) N → AdelicDegreeTameRamification.IsArchNormSq t' x' σ N := by
  atlas_forward_decl GlobalTheory.FlatDegreeCompare.isArchNormSq_up
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_index_valuation_compat : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (em : k →+* K) (e : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → 0 < e → (∀ z : k, (IsDiscreteValuationRing.maximalIdeal V).valuation K (em z) = 𝔭.valuation k z ^ e) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (f : V →+* W) (g : K →+* L) (em' : k' →+* L) (e' d : ℕ), (∀ z : V, algebraMap W L (f z) = g (algebraMap V K z)) ∧ em'.comp i = g.comp em ∧ 0 < e' ∧ e' * ε = d * e ∧ (∀ z : k', (IsDiscreteValuationRing.maximalIdeal W).valuation L (em' z) = 𝔓.valuation k' z ^ e') ∧ ∀ y : K, (IsDiscreteValuationRing.maximalIdeal W).valuation L (g y) = (IsDiscreteValuationRing.maximalIdeal V).valuation K y ^ d := by
  first | exact @GlobalTheory.CommonValuation.exists_common_valuation | exact GlobalTheory.CommonValuation.exists_common_valuation | (intros; apply GlobalTheory.CommonValuation.exists_common_valuation <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.LocOrdUp

theorem exists_rightInverse {V K : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {m n : ℕ} (U : Matrix (Fin m) (Fin n) V)
    (h : ∀ (a : Fin n → V) (c : Fin m → K), c ᵥ* U.map (algebraMap V K) = (fun j => algebraMap V K (a j)) →
      ∃! b, b ᵥ* U = a) : ∃ R : Matrix (Fin n) (Fin m) V, U * R = 1 := by
  have inj : Function.Injective (Matrix.vecMulLinear U) := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun b hb => ?_)
    exact (h 0 0 (by ext j; simp)).unique hb (Matrix.zero_vecMul _)
  have tf : Module.IsTorsionFree V ((Fin n → V) ⧸ LinearMap.range (Matrix.vecMulLinear U)) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r y hy => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨b, hb⟩ := hy
    rw [or_iff_not_imp_left]
    intro hr
    rw [Submodule.Quotient.mk_eq_zero]
    have hr' : algebraMap V K r ≠ 0 := fun e => hr (IsFractionRing.injective V K (e.trans (map_zero _).symm))
    obtain ⟨b', hb', -⟩ := h a ((algebraMap V K r)⁻¹ • fun i => algebraMap V K (b i)) (by
      rw [Matrix.smul_vecMul]
      ext j
      have e : ((fun i => algebraMap V K (b i)) ᵥ* U.map (algebraMap V K)) j = algebraMap V K ((b ᵥ* U) j) :=
        (RingHom.map_vecMul (algebraMap V K) U b j).symm
      have e' : b ᵥ* U = r • a := hb
      rw [Pi.smul_apply, e, e', Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, inv_mul_cancel_left₀ hr'])
    exact ⟨b', hb'⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range (Matrix.vecMulLinear U)).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have ex : Function.Exact (Matrix.vecMulLinear U) (LinearMap.range (Matrix.vecMulLinear U)).mkQ :=
    LinearMap.exact_map_mkQ_range _
  have hs' : ∃ l, (LinearMap.range (Matrix.vecMulLinear U)).mkQ ∘ₗ l = LinearMap.id := ⟨s, hs⟩
  have hg' : ∃ l, l ∘ₗ Matrix.vecMulLinear U = LinearMap.id :=
    ((ex.split_tfae inj (Submodule.mkQ_surjective _)).out 0 1).1 hs'
  obtain ⟨g, hg⟩ := hg'
  refine ⟨LinearMap.toMatrixRight' g, ?_⟩
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
  change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear U = _
  simpa using hg

theorem existsUnique_of_rightInverse {W L : Type} [CommRing W] [CommRing L] (φ : W →+* L) (hφ : Function.Injective φ)
    {m n : ℕ} {U : Matrix (Fin m) (Fin n) W} {R : Matrix (Fin n) (Fin m) W} (h : U * R = 1)
    (a : Fin n → W) (c : Fin m → L) (hc : c ᵥ* U.map φ = fun j => φ (a j)) : ∃! b, b ᵥ* U = a := by
  have h2 : U.map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : c = fun i => φ ((a ᵥ* R) i) := by
    rw [← Matrix.vecMul_one c, ← h2, ← Matrix.vecMul_vecMul, hc]
    exact funext fun i => (RingHom.map_vecMul φ R a i).symm
  refine ⟨a ᵥ* R, funext fun j => hφ ?_, fun b hb => ?_⟩
  · rw [RingHom.map_vecMul, ← congrFun hc j, h3]; rfl
  · rw [← hb, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem isLocOrd_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (r : ℝ), Indep x → (∀ a, IsVecOver i n.φ (x a) (x' a)) → (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → EigenvectorLieDegree.IsLocOrd t.G x 𝔭 r → EigenvectorLieDegree.IsLocOrd t'.G x' 𝔓 (ε * r) := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' 𝔭 𝔓 ε r hx hxx hval hr
  obtain ⟨V, K, _, _, _, _, _, _, em, e₀, G, _, A, _, φ, ψ, v, u, u', M, ν, he₀, hv, hG, hφ, hψ, hxv, hu, hb, hM, hν,
    rfl⟩ := hr
  obtain ⟨W, L, _, _, _, _, _, _, f, g, em', e₂, d, hfg, hem, he₂, hd, hv', hvg⟩ :=
    GlobalTheory.T.ramification_index_valuation_compat k k' i 𝔭 𝔓 ε V K em e₀ hval he₀ hv
  have hf' : (algebraMap W L).comp f = g.comp (algebraMap V K) := RingHom.ext hfg
  obtain ⟨G₁, _, χ, h', hG₁⟩ : ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁) (χ : G₁.left ⟶ G.left),
      IsGrpPullback G₁ G (spMap f) χ ∧ IsSemiAbelian G₁ :=
    ⟨_, _, _, isGrpPullback_pullback G (spMap f), IsSemiAbelian.pullback _ G hG⟩
  obtain ⟨A₁, _, ω, hω⟩ : ∃ (A₁ : Over (Sp L)) (_ : GrpObj A₁) (ω : A₁.left ⟶ A.left),
      IsGrpPullback A₁ A (spMap g) ω := ⟨_, _, _, isGrpPullback_pullback A (spMap g)⟩
  have := hG.comm
  have := hG₁.comm
  have := hG.smooth
  have := hG₁.smooth
  have := PolPull.isCommMonObj_of_isGrpPullback hφ
  have := PolPull.isCommMonObj_of_isGrpPullback hω
  have n' : IsGrpPullback A₁ G (spMap (algebraMap W L) ≫ spMap f) (ω ≫ φ) :=
    (hω.comp hφ).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hf']) rfl
  have w : (ω ≫ φ) ≫ G.hom = (A₁.hom ≫ spMap (algebraMap W L)) ≫ spMap f :=
    n'.1.w.trans (Category.assoc _ _ _).symm
  have q := h'.1.lift_fst _ _ w
  have hφ₁ := h'.cancel (n'.congr rfl q.symm) (h'.1.lift_snd _ _ w)
  have n'' : IsGrpPullback A₁ t.G (spMap em' ≫ spMap i) (ω ≫ ψ) :=
    (hω.comp hψ).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hem]) rfl
  have w' : (ω ≫ ψ) ≫ t.G.hom = (A₁.hom ≫ spMap em') ≫ spMap i :=
    n''.1.w.trans (Category.assoc _ _ _).symm
  have q' := n.cart.1.lift_fst _ _ w'
  have hψ₁ := n.cart.cancel (n''.congr rfl q'.symm) (n.cart.1.lift_snd _ _ w')
  have tv : ∀ a, IsTangent (v a) := fun a => (hxv a).isTangent hψ (hx.1 a)
  obtain ⟨N, e, e', -, he, he', h, -⟩ := exists_frame hG hφ tv
  choose e₁ h₁ _ using fun j => existsUnique_isVecOver h'.1 (e j)
  have he₁ := Chart.isLieBasis_baseChange f h' he h₁
  choose e₁' h₂ _ using fun j => existsUnique_isVecOver hω.1 (e' j)
  have h₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (h₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (h j) (h₂ j))
  have he₁' := Chart.isLieBasis_baseChange _ hφ₁ he₁ h₃
  choose u₁ k₁ _ using fun j => existsUnique_isVecOver h'.1 (u j)
  choose u₁' k₂ _ using fun j => existsUnique_isVecOver hω.1 (u' j)
  have k₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (k₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (hu j).2.1 (k₂ j))
  choose v₁ l₂ _ using fun j => existsUnique_isVecOver hω.1 (v j)
  have l₃ := fun j => EllComp.isVecOver_cancel n.cart.1 hψ₁.1 (hxx j)
    (by rw [q', hem]; exact EllComp.isVecOver_comp (hxv j) (l₂ j))
  choose U₀ hU₀ _ using fun a => he.2 _ (hu a).1
  let U : Matrix (Fin m) (Fin N) V := U₀
  have hU : ∀ a, IsLieComb (U a) e (u a) := hU₀
  have hU' : ∀ a, IsLieComb (U.map (algebraMap V K) a) e' (u' a) := fun a =>
    (lieComb_baseChange _ _ _ G A φ hφ N e (u a) (U a) e' (u' a) h (hU a)).1 (hu a).2.1
  have hU₁ : ∀ a, IsLieComb (U.map f a) e₁ (u₁ a) := fun a =>
    (lieComb_baseChange _ _ _ G G₁ χ h' N e (u a) (U a) e₁ (u₁ a) h₁ (hU a)).1 (k₁ a)
  have hU₁' : ∀ a, IsLieComb ((U.map f).map (algebraMap W L) a) e₁' (u₁' a) := fun a =>
    (lieComb_baseChange _ _ _ G₁ A₁ _ hφ₁ N e₁ (u₁ a) (U.map f a) e₁' (u₁' a) h₃ (hU₁ a)).1 (k₃ a)
  choose C₀ hC₀ using fun a => (hu a).2.2
  let C : Matrix (Fin m) (Fin m) K := C₀
  have hC : ∀ a, IsLieComb (C a) v (u' a) := hC₀
  have hM₁ : ∀ a, IsLieComb (M.map g a) u₁' (v₁ a) := fun a =>
    (lieComb_baseChange _ _ g A A₁ ω hω m u' (v a) (M a) u₁' (v₁ a) k₂ (hM a)).1 (l₂ a)
  have tu₁ : ∀ a, IsTangent (u₁ a) := fun a => (k₁ a).isTangent h' (hu a).1
  have tu₁' : ∀ a, IsTangent (u₁' a) := fun a => (k₃ a).isTangent hφ₁ (tu₁ a)
  obtain ⟨R, hR⟩ := exists_rightInverse (K := K) U fun a c hc => by
    obtain ⟨a₁, a₂, -⟩ := LieComb.lieComb_algebra _ G N e he.1
    obtain ⟨y, hy⟩ := (a₁ a).exists
    obtain ⟨z, hz, -⟩ := existsUnique_isVecOver hφ.1 y
    have hz' := (lieComb_baseChange _ _ _ G A φ hφ N e y a e' z h hy).1 hz
    rw [← hc, ← comb_comb he'.1 hU', comb_comb tv hC] at hz'
    refine (existsUnique_congr fun b => ?_).1 (hb y z (a₂ _ _ hy) hz ⟨_, hz'⟩)
    rw [comb_comb he.1 hU]
    exact ⟨fun hb => (Indep.of_basis he).2 _ _ y hb hy, fun hb => hb ▸ hy⟩
  have hR₁ : U.map f * R.map f = 1 := by
    rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, em', _,
    G₁, inferInstance, A₁, inferInstance, _, _, v₁, u₁, u₁', M.map g, d * ν, he₂, hv', hG₁, hφ₁, hψ₁, l₃,
    fun a => ⟨tu₁ a, k₃ a, _, (lieComb_baseChange _ _ g A A₁ ω hω m v (u' a) (C a) v₁ (u₁' a) l₂ (hC a)).1 (k₂ a)⟩,
    fun y z hy hz ⟨c, hc⟩ => ?_, hM₁, ?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := he₁.2 y hy
    have hz' := (lieComb_baseChange _ _ _ G₁ A₁ _ hφ₁ N e₁ y a e₁' z h₃ ha).1 hz
    rw [comb_comb tu₁' hM₁, comb_comb he₁'.1 hU₁'] at hc
    refine (existsUnique_congr fun b => ?_).1 (existsUnique_of_rightInverse (algebraMap W L)
      (IsFractionRing.injective W L) hR₁ a _ ((Indep.of_basis he₁').2 _ _ z hc hz'))
    rw [comb_comb he₁.1 hU₁]
    exact ⟨fun hb => hb ▸ ha, fun hb => (Indep.of_basis he₁).2 _ _ y hb ha⟩
  · have : (M.map g).det = g M.det := (RingHom.map_det g M).symm
    rw [this, hvg, hν, ← WithZero.exp_nsmul]
    congr 1
    simp
  · have a₁ : (e₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he₀.ne'
    have a₃ := congrArg (Nat.cast : ℕ → ℝ) hd
    have a₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he₂.ne'
    push_cast at a₃ ⊢
    rw [← mul_div_assoc, div_eq_div_iff a₁ a₂]
    linear_combination (ν : ℝ) * a₃

end GlobalTheory.LocOrdUp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonarchimedean_norm_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (r : ℝ), Indep x → (∀ a, IsVecOver i n.φ (x a) (x' a)) → (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → EigenvectorLieDegree.IsLocOrd t.G x 𝔭 r → EigenvectorLieDegree.IsLocOrd t'.G x' 𝔓 (ε * r) := by
  atlas_forward_decl GlobalTheory.LocOrdUp.isLocOrd_up
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Degree

variable {k : Type} [Field k] [NumberField k]

def ordOf (a : HeightOneSpectrum (𝓞 k) → k) (𝔭 : HeightOneSpectrum (𝓞 k)) : ℝ :=
  (WithZero.log (𝔭.valuation k (a 𝔭)) : ℤ)

theorem finite_support_ordTwist (τ : E →+* k) : (Function.support (EigenvectorLieDegree.ordTwist H τ)).Finite := by
  have f : ∀ 𝔞, {𝔭 | ¬ EigenvectorLieDegree.ordIdeal τ 𝔞 𝔭 = 0}.Finite := fun 𝔞 =>
    Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  refine ((f (differentIdeal ℤ (𝓞 E))).union (f (Ideal.span {H.rt}))).subset fun 𝔭 h => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact h (by rw [EigenvectorLieDegree.ordTwist, hc.1, hc.2]; rfl)

end Degree

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl

open GlobalTheory.KeyPow GlobalTheory.KeyKa GlobalTheory.KeyEq GlobalTheory.KeyIsoNormal in
theorem isArchSq_iff (σ : k →+* ℂ) (N : ℝ) : EigenvectorLieDegree.IsArchSq t.G t.PP.L x σ N ↔ AdelicDegreeTameRamification.IsArchNormSq t x σ N := by
  constructor
  · rintro ⟨A, _, φ, g, u', Hm, χ, v, W, hφ, hA, hv, h0, hN⟩
    obtain ⟨t', ⟨n⟩⟩ := exists_sab (spMap σ) t
    obtain ⟨e, he, hφ'⟩ := grpPullback_iso hφ n.cart
    have hL : LBIso t'.PP.L (t.PP.L.pull n.cm.F) := by
      obtain ⟨w, hw, -⟩ := n.lin
      exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ : LBIso (t.PP.L.pull φ) (t'.PP.L.pull e.hom.left) := hφ' ▸ EllComp.lbIso_pull_comp hL.symm _
    have hL' := pull_isLB t.PP.isLB φ
    obtain ⟨u, hex, hΛ, hfr⟩ := exists_push t'.PP.isLB hL' e.hom (isGrpPullback_of_iso e) w ((isGen_iff w).1 hw) u'
    refine ⟨t', n, g, u, Hm, fun l => χ ⟨l.1, hΛ ▸ l.2⟩, fun i => v i ≫ e.hom, W,
      ⟨hA.1, hA.2.1, fun l => hA.2.2.1 _, fun l j z hz => ?_⟩, fun i => ?_, fun i U hU f => ?_, hN, h0⟩
    · rw [hex] at hz
      have hj : e.hom.left ((u'.ex z).left pt) ∈ t'.PP.L.U j := (top_le_preimage_iff_mem _ _).1 hz
      obtain ⟨c, hc⟩ := exists_chart hL' ((u'.ex z).left pt)
      have hl : u'.ex (z + l.1) = u'.ex z := by
        rw [u'.ex_add, (u'.ker l.1).2 (hΛ ▸ l.2), _root_.mul_one]
      have a := hA.2.2.2 ⟨l.1, hΛ ▸ l.2⟩ c z ((top_le_preimage_iff_mem _ _).2 hc)
      rw [hfr j c z hj hc, hfr j c (z + l.1) (hl ▸ hj) (hl ▸ hc), hl, a]
      ring
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ').trans (hv i).1
    · have := (hv i).2 (e.hom.left ⁻¹ᵁ U) hU ((e.hom.left.app U).hom f)
      simp only [valAt'_comp, ← hex] at this
      rw [← this]
      congr 2
  · rintro ⟨t', n, g, u, Hm, χ, v, W, hA, hv, hW, hN, h0⟩
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨t'.G, inferInstance, n.φ, g, TorsionTauCompare.transport t'.PP.isLB (pull_isLB t.PP.isLB _) hw u, Hm, χ, v, W,
      n.cart, TorsionTauCompare.isAH_transport _ _ hw u hA, fun i => ⟨hv i, hW i⟩, h0, hN⟩

end Lie

section Point

variable {k : Type} [Field k] [NumberField k]

def IsEigData (t : SAB H (Sp k)) (τ : E →+* k) (m : ℕ) (r : HeightOneSpectrum (𝓞 k) → ℝ) (N : (k →+* ℂ) → ℝ) : Prop :=
  ∃ v : Fin m → (epsR k ⟶ t.G), EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) v ∧
    (∀ 𝔭, EigenvectorLieDegree.IsLocOrd t.G v 𝔭 (r 𝔭)) ∧ ∀ σ, EigenvectorLieDegree.IsArchSq t.G t.PP.L v σ (N σ)

def ClaimOrd (x : ℝ) (t : SAB H (Sp k)) (τ τ' : E →+* k) (p q : ℕ) : Prop :=
  ∀ r N r' N', IsEigData t τ p r N → IsEigData t τ' q r' N' →
    (Function.support r).Finite ∧ (Function.support r').Finite ∧
    EigenvectorLieDegree.adDeg r N - EigenvectorLieDegree.adDeg r' N' = ((p : ℝ) - q) / 2 * x ∧
    EigenvectorLieDegree.adDeg (fun 𝔭 => r 𝔭 - r' 𝔭 - q * (EigenvectorLieDegree.ordTwist H τ 𝔭 : ℝ)) (fun σ => N σ / N' σ) =
      -EigenvectorLieDegree.cOne H p q x ∧
    |EigenvectorLieDegree.cOne H p q x + ((p : ℝ) - q) * x / 2| ≤ q * Real.log (rootDiscr E)

variable {t : SAB H (Sp k)} {τ τ' : E →+* k} {p q : ℕ}

end Point

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

structure IsUnder (i : k →+* k') (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k))
    (ε : HeightOneSpectrum (𝓞 k') → ℕ) : Prop where
  val : ∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓
  sum : ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧
    (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal)

theorem exists_isUnder (i : k →+* k') : ∃ π ε, IsUnder i π ε :=
  let ⟨π, ε, a, b⟩ := GlobalTheory.T.ramification_weighted_log_norm_sum k k' i
  ⟨π, ε, a, b⟩

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

theorem IsUnder.pos (h : IsUnder i π ε) (𝔓 : HeightOneSpectrum (𝓞 k')) : 0 < ε 𝔓 :=
  Nat.pos_of_ne_zero fun e => by simpa [e] using h.val 𝔓 0

theorem IsUnder.surjective (h : IsUnder i π ε) : Function.Surjective π := fun 𝔭 =>
  let ⟨_, hs, ⟨𝔓, h𝔓⟩, _⟩ := h.sum 𝔭
  ⟨𝔓, (hs 𝔓).1 h𝔓⟩

def up (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ)
    (r : HeightOneSpectrum (𝓞 k) → ℝ) (𝔓 : HeightOneSpectrum (𝓞 k')) : ℝ := ε 𝔓 * r (π 𝔓)

theorem IsUnder.finite_of_up (h : IsUnder i π ε) {r : HeightOneSpectrum (𝓞 k) → ℝ}
    (hr : (Function.support (up π ε r)).Finite) : (Function.support r).Finite :=
  (hr.image π).subset fun 𝔭 h𝔭 => by
    obtain ⟨𝔓, rfl⟩ := h.surjective 𝔭
    exact ⟨𝔓, mul_ne_zero (Nat.cast_ne_zero.2 (h.pos 𝔓).ne') h𝔭, rfl⟩

theorem IsUnder.adDeg_up (h : IsUnder i π ε) {r : HeightOneSpectrum (𝓞 k) → ℝ} (hr : (Function.support r).Finite)
    (N : (k →+* ℂ) → ℝ) : EigenvectorLieDegree.adDeg (up π ε r) (fun σ => N (σ.comp i)) = EigenvectorLieDegree.adDeg r N := by
  classical
  choose s hs _ hsum using h.sum
  have n0 : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have n0' : (Module.finrank ℚ k' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have a := GlobalTheory.T.embedding_sum_degree_formula k k' i fun σ => Real.log (N σ)
  have b : (Module.finrank ℚ k : ℝ) * ∑ᶠ 𝔓, up π ε r 𝔓 * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * ∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
    rw [finsum_eq_sum_of_support_subset (s := hr.toFinset.biUnion s), finsum_eq_sum_of_support_subset (s := hr.toFinset),
      Finset.sum_biUnion, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun 𝔭 _ => ?_
      rw [mul_left_comm, ← hsum, mul_left_comm, Finset.mul_sum (s 𝔭) _ (r 𝔭)]
      congr 1
      refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
      rw [up, (hs _ _).1 h𝔓]; ring
    · intro 𝔭 _ 𝔮 _ e
      exact Finset.disjoint_left.2 fun 𝔓 u v => e (((hs _ _).1 u).symm.trans ((hs _ _).1 v))
    · intro 𝔭 h𝔭
      simpa using left_ne_zero_of_mul h𝔭
    · intro 𝔓 h𝔓
      have := right_ne_zero_of_mul (left_ne_zero_of_mul h𝔓)
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨π 𝔓, this, (hs _ _).2 rfl⟩
  rw [EigenvectorLieDegree.adDeg, EigenvectorLieDegree.adDeg, div_eq_div_iff n0' n0]
  linear_combination b - 1 / 2 * a

theorem IsUnder.ordTwist (h : IsUnder i π ε) (τ : E →+* k) (𝔓 : HeightOneSpectrum (𝓞 k')) :
    EigenvectorLieDegree.ordTwist H (i.comp τ) 𝔓 = ε 𝔓 * EigenvectorLieDegree.ordTwist H τ (π 𝔓) := by
  have e : ∀ 𝔞, EigenvectorLieDegree.ordIdeal (i.comp τ) 𝔞 𝔓 = ε 𝔓 * EigenvectorLieDegree.ordIdeal τ 𝔞 (π 𝔓) := fun 𝔞 =>
    GlobalTheory.T.ideal_count_under_extension E k k' i τ 𝔞 _ _ _ (h.val 𝔓)
  simp only [EigenvectorLieDegree.ordTwist, e]
  ring

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

theorem IsEigData.up (h : IsUnder i π ε) (n : SABMap t' t (spMap i)) {τ : E →+* k} {m : ℕ}
    {r : HeightOneSpectrum (𝓞 k) → ℝ} {N : (k →+* ℂ) → ℝ} (hd : IsEigData t τ m r N) :
    IsEigData t' (i.comp τ) m (up π ε r) fun σ => N (σ.comp i) := by
  obtain ⟨x, hx, hr, hN⟩ := hd
  choose x' hx' _ using fun a => existsUnique_isVecOver n.cart.1 (x a)
  have h₁ := GlobalTheory.T.eigenbasis_base_change E H k k' i t t' n m x x' _ hx' hx
  have h₂ := fun 𝔓 => GlobalTheory.T.nonarchimedean_norm_base_change E H k k' i t t' n m x x' (π 𝔓) 𝔓 (ε 𝔓) (r (π 𝔓)) (Indep.of_eigBasis hx) hx' (h.val 𝔓) (hr _)
  have h₃ := fun σ : k' →+* ℂ => (isArchSq_iff σ _).2
    (GlobalTheory.T.archimedean_norm_square_base_change E H k k' i t t' n m x x' σ (N (σ.comp i)) hx' ((isArchSq_iff (σ.comp i) _).1 (hN _)))
  exact ⟨x', h₁, h₂, h₃⟩

theorem ClaimOrd.down (n : SABMap t' t (spMap i)) {x : ℝ} {τ τ' : E →+* k} {p q : ℕ}
    (c : ClaimOrd x t' (i.comp τ) (i.comp τ') p q) : ClaimOrd x t τ τ' p q := by
  obtain ⟨π, ε, h⟩ := exists_isUnder i
  intro r N r' N' h₁ h₂
  obtain ⟨f₁, f₂, d₁, d₂, b⟩ := c _ _ _ _ (h₁.up h n) (h₂.up h n)
  have g₁ := h.finite_of_up f₁
  have g₂ := h.finite_of_up f₂
  rw [h.adDeg_up g₁, h.adDeg_up g₂] at d₁
  refine ⟨g₁, g₂, d₁, Eq.trans ?_ d₂, b⟩
  rw [← h.adDeg_up]
  · congr 1
    funext 𝔓
    simp only [FlatDegreeCompare.up, h.ordTwist]
    push_cast
    ring
  · refine ((g₁.union g₂).union (finite_support_ordTwist (H := H) τ)).subset fun 𝔭 h𝔭 => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact h𝔭 (by simp [hc.1.1, hc.1.2, hc.2])

end Extension

end GlobalTheory.FlatDegreeCompare
end
end
