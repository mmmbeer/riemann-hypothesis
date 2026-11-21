import Mathlib

noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.Top

def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i - ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def InWin (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 0 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ h

def Low (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (InWin G h η)

def Cl (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U - Low G h η U

def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)

def T1 (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def T2 (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ Low G h η U, ∀ y ∈ GlobalTheory w t, σ + 2 < |x - y|

def LemmaS : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ t M : ℕ) (h w η σ : ZMod f → ℕ) (G : ZMod f → Bool)
    (k : ℕ → ℕ → ZMod f → ℤ),
    1 ≤ t → 1 ≤ M → (∀ i, w i + t - 1 ≤ h i) →
    (∀ i, G i = true → w i + t - 1 ≤ η i) → (∀ i, G i = false → (h i : ℤ) - η i ≤ w i) →
    (∀ i, η i + 4 * σ i + 6 < ℓ) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → |k c μ i| ≤ σ i) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M →
      0 ≤ (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i + 1) - k c μ i ∧
      (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i + 1) - k c μ i ≤ h i) →
    (∀ i, (Finset.Icc 1 t ×ˢ Finset.Icc 1 M).val.map
        (fun cμ : ℕ × ℕ => (((w i : ℤ) + cμ.1 - 1 - k cμ.1 cμ.2 i : ℤ) : ZMod ℓ)) =
      M • (Finset.Icc 1 t).val.map (fun c : ℕ => (((w i : ℤ) + c - 1 : ℤ) : ZMod ℓ))) →
    ∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → k c μ i = 0

end Formalism.WachCohomologyFacts.Top
