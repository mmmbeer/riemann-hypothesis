import Formalism.FrobeniusContraction.Statement
import Formalism.FrobeniusContraction.StatementTop

noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.V2

open Formalism.WachCohomologyFacts

def Sat : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (ι : Type) [Fintype ι]
    (ℓ f f' : A), IsRelPrime ℓ (f * f') →
    ∀ x : ι → FractionRing A,
      (∀ i, ∃ a : A, algebraMap A (FractionRing A) f' * x i = algebraMap A (FractionRing A) a) →
      (∃ k : ℕ, ∀ i, ∃ a : A,
        algebraMap A (FractionRing A) (ℓ ^ k) * x i = algebraMap A (FractionRing A) (f * a)) →
      ∀ i, ∃ a : A, x i = algebraMap A (FractionRing A) (f * a)

def sgN (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def InWinN (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 1 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ (h : ℤ) - 1

def ClN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (fun x => ¬ InWinN G h η x)

def ResidueAvoidance (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ ClN G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)

def HighestWeightResidueAvoids : Prop :=
  (∀ (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ), 0 ≤ σ →
    (∀ x ∈ U, 0 ≤ x ∧ x ≤ h) → (h : ℤ) + 2 * σ + η + 5 < ℓ →
    (∀ x ∈ ClN G h η U, (η : ℤ) + 2 * σ + 3 < (if G then x else (h : ℤ) - x)) →
    ResidueAvoidance ℓ G h η σ U) ∧
  (∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), (∀ i, h i + 2 < ℓ) → ∀ i, sgN f ℓ h i = 0)

end Formalism.WachCohomologyFacts.V2
