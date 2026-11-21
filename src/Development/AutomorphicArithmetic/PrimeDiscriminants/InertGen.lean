import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycBasic

open NumberField IntermediateField

noncomputable section

namespace UpperTheory.InertGen

open Formalism.HC Formalism.FrobeniusOrbits Formalism.BasicNotions

section Raw

variable {φ : Frame} (H : HostRaw φ)

end Raw

variable {R : Ranks} (H : Host R)

theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have hnd : ¬ H.q ∣ H.QS * H.d := by
    intro hd
    have h1 : H.q ∣ Nat.gcd (H.QS * H.d) H.q := Nat.dvd_gcd hd dvd_rfl
    rw [H.coprime_QSd_q.gcd_eq_one] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
  have hc : H.condN = (H.QS * H.d) * H.q := by
    unfold Formalism.HC.HostRaw.condN
    ring
  rw [hc, Nat.ordCompl_mul, Nat.factorization_eq_zero_of_not_dvd hnd, hq.factorization_self]
  simp [hq.pos]

theorem ordCompl_d : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hN : H.condN = H.d ^ 1 * (H.QS * H.q) := by unfold HostRaw.condN; ring
  rw [hN]
  exact Nat.ordCompl_pow_mul_of_not_dvd 1 H.d_prime H.d_not_dvd_QSq

end UpperTheory.InertGen

end
