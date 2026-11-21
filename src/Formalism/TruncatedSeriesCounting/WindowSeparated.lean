import Mathlib
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids

noncomputable section

open Classical

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

open Formalism.WachCohomologyFacts

def LowN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (V2.InWinN G h η)

def WindowSmall (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def WindowSeparated (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ LowN G h η U, ∀ y ∈ Top.GlobalTheory w t, σ + 2 < |x - y|

def Slot (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  0 ≤ σ ∧ 1 ≤ t ∧ (∀ x ∈ U, 1 ≤ x ∧ x ≤ (h : ℤ) - 1) ∧ w + t ≤ h ∧
    1 ≤ w ∧ (G = true → w + t - 1 ≤ η) ∧ (G = false → (h : ℤ) - η ≤ w) ∧
    WindowSmall ℓ η σ ∧ WindowSeparated G h η w t σ U ∧ V2.ResidueAvoidance ℓ G h η σ U

def resCount (ℓ : ℕ) (U : Multiset ℤ) (x : ZMod ℓ) : ℕ := U.countP (fun u => ((u : ℤ) : ZMod ℓ) = x)

def CountBd : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ false h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      (∀ x, S x ≠ 0 → ∃ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) ∧ x = ((u : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.Icc (w : ℤ) (h : ℤ), S ((n : ℤ) : ZMod ℓ) =
        Multiset.card U - U.countP (fun u => u < (w : ℤ))

def Close : Prop :=
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (KK L N : Submodule k V) (r d : ℕ),
      L ≤ KK ⊓ N → Module.finrank k KK - Module.finrank k L ≤ r →
      Module.finrank k ↥(KK ⊓ N) - Module.finrank k L = r - d → d ≤ r →
      Module.finrank k KK - Module.finrank k ↥(KK ⊓ N) ≤ d) ∧
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (Hf adm : Submodule k V), Hf ≤ adm → Module.finrank k adm ≤ Module.finrank k Hf →
      adm = Hf)

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo
