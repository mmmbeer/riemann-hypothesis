import Mathlib
import Formalism.PeriodIntegrals.MiracleFlat

universe u

namespace PI.UnitaryGroupMassFormula.MF

open RingTheory.Sequence IsLocalRing

def RegSeqGen : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
    ∃ xs : List A, IsRegular A xs ∧ Ideal.ofList xs = maximalIdeal A ∧ (xs.length : WithBot ℕ∞) = ringKrullDim A

def CMSop : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B],
    (∃ rs : List B, IsRegular B rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ (rs.length : WithBot ℕ∞) = ringKrullDim B) →
    ∀ xs : List B, (∀ x ∈ xs, x ∈ maximalIdeal B) →
      ringKrullDim B = (xs.length : WithBot ℕ∞) + ringKrullDim (B ⧸ Ideal.ofList xs) → IsRegular B xs

def FlatOfReg : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (xs : List A), IsRegular A xs → Ideal.ofList xs = maximalIdeal A →
    IsRegular B (xs.map (algebraMap A B)) → Module.Flat A B

def Assembly : Prop := RegSeqGen.{u} → CMSop.{u} → FlatOfReg.{u} → PI.MiracleFlat.{u}

end PI.UnitaryGroupMassFormula.MF
