import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaC

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FpDegCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite,
    haveI := (D.s.atP p).ellPrime
    ¬ (Loc.resChar p ∣ Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem memO_iff {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K), map_one]

theorem iotaF_mem_cof (D : Formalism.BasicNotions.D7) (x : D.host.F) :
    ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιF x ∈ 𝒪[(D.s.atP p).Fp] := by
  have hfin := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 D.host.F) x
  refine hfin.eventually_cofinite_notMem.mono fun p hp => ?_
  rw [memO_iff, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one]
  exact not_lt.mp hp

theorem exists_theta (D : Formalism.BasicNotions.D7) :
    ∃ θ : D.host.E, IsIntegral ℤ θ ∧ θ ∉ (algebraMap D.host.F D.host.E).range := by
  haveI := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hc : (NumberField.InfinitePlace.mk φ).IsComplex := NumberField.IsTotallyComplex.isComplex _
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal φ := by
    rwa [← NumberField.InfinitePlace.isReal_mk_iff, NumberField.InfinitePlace.not_isReal_iff_isComplex]
  obtain ⟨x, hx⟩ : ∃ x, star (φ x) ≠ φ x := by
    by_contra h
    push_neg at h
    exact hnr (RingHom.ext h)
  have hxF : x ∉ (algebraMap D.host.F D.host.E).range := by
    rintro ⟨f, rfl⟩
    exact hx ((NumberField.mem_maximalRealSubfield_iff _).1 f.2 φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  by_cases ha : algebraMap (𝓞 D.host.E) D.host.E a ∈ (algebraMap D.host.F D.host.E).range
  · refine ⟨algebraMap (𝓞 D.host.E) D.host.E b, NumberField.RingOfIntegers.isIntegral_coe b, fun hbF => hxF ?_⟩
    obtain ⟨f1, hf1⟩ := ha
    obtain ⟨f2, hf2⟩ := hbF
    exact ⟨f1 / f2, by rw [map_div₀, hf1, hf2]⟩
  · exact ⟨algebraMap (𝓞 D.host.E) D.host.E a, NumberField.RingOfIntegers.isIntegral_coe a, ha⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end
