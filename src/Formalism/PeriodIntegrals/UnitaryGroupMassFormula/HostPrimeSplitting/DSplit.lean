import Formalism.PeriodIntegrals.EtaHostFacts

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Ideal
open scoped Pointwise

namespace PI.UnitaryGroupMassFormula.HostPrimeFacts

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

abbrev cE : H.E ≃ₐ[ℚ] H.E := H.conj

theorem cE_inv_fix (x : 𝓞 H.F) :
    (cE H)⁻¹ • algebraMap (𝓞 H.F) (𝓞 H.E) x = algebraMap (𝓞 H.F) (𝓞 H.E) x := by
  have hfix : H.conj ((x : H.F) : H.E) = ((x : H.F) : H.E) := (H.der.mem_F _).mp (x : H.F).2
  apply RingOfIntegers.ext
  show (cE H)⁻¹ ((x : H.F) : H.E) = ((x : H.F) : H.E)
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
  exact hfix.symm

def conjPrime (P : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) where
  asIdeal := cE H • P.asIdeal
  isPrime := by have := P.isPrime; infer_instance
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [← inv_smul_smul (cE H) P.asIdeal, h, Ideal.smul_bot]

theorem conjPrime_under (P : HeightOneSpectrum (𝓞 H.E)) :
    (conjPrime H P).under (𝓞 H.F) = P.under (𝓞 H.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ cE H • P.asIdeal ↔ algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ P.asIdeal
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, cE_inv_fix]

end PI.UnitaryGroupMassFormula.HostPrimeFacts
