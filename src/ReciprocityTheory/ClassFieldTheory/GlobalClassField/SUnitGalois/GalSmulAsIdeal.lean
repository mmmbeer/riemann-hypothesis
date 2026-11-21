import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField.SUnit

open scoped Pointwise in

instance galSmul (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ v :=
    { asIdeal := σ • v.asIdeal
      isPrime := Ideal.IsPrime.smul σ
      ne_bot := by
        rw [Ideal.pointwise_smul_def, ne_eq,
          Ideal.map_eq_bot_iff_of_injective (MulAction.injective σ)]
        exact v.ne_bot }
  one_smul v := HeightOneSpectrum.ext (one_smul _ v.asIdeal)
  mul_smul σ τ v := HeightOneSpectrum.ext (mul_smul σ τ v.asIdeal)
