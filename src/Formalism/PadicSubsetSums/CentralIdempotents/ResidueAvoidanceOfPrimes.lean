import Mathlib

noncomputable section

open Classical

namespace Formalism.IrreducibleCountingLemmas.TOP

def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def InWinN (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 1 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ (h : ℤ) - 1

def ClN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (fun x => ¬ InWinN G h η x)

def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)

def ResidueAvoidance (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ ClN G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)

def SgLe : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (H : ℕ), 2 ≤ ℓ → (∀ j, h j ≤ H) →
    ∀ i, (sg f ℓ h i : ℝ) ≤ H / ((ℓ : ℝ) - 1)

def SgRange : Prop :=
  ∀ (ℓ : ℕ) (ℓs b H : ℝ), 0 ≤ H → 1 < ℓs → ℓs < ℓ → H * ℓs ≤ 2 * b * (ℓs - 1) →
    H / ((ℓ : ℝ) - 1) ≤ 2 * b / ℓs

def LowN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (InWinN G h η)

def WindowSmall (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def WindowSeparated (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ LowN G h η U, ∀ y ∈ GlobalTheory w t, σ + 2 < |x - y|

def Slot (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  0 ≤ σ ∧ 1 ≤ t ∧ (∀ x ∈ U, 1 ≤ x ∧ x ≤ (h : ℤ) - 1) ∧ w + t ≤ h ∧
    1 ≤ w ∧ (G = true → w + t - 1 ≤ η) ∧ (G = false → (h : ℤ) - η ≤ w) ∧
    WindowSmall ℓ η σ ∧ WindowSeparated G h η w t σ U ∧ ResidueAvoidance ℓ G h η σ U

def Close : Prop :=
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (KK L N : Submodule k V) (r d : ℕ),
      L ≤ KK ⊓ N → Module.finrank k KK - Module.finrank k L ≤ r →
      Module.finrank k ↥(KK ⊓ N) - Module.finrank k L = r - d → d ≤ r →
      Module.finrank k KK - Module.finrank k ↥(KK ⊓ N) ≤ d) ∧
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (Hf adm : Submodule k V), Hf ≤ adm → Module.finrank k adm ≤ Module.finrank k Hf →
      adm = Hf)

def Ord {k : Type} [Field k] (j : ℤ) (x : LaurentSeries k) : Prop := ∀ i < j, x.coeff i = 0

def vv (k : Type) [Field k] : LaurentSeries k := HahnSeries.single 1 1

def IsUnitR {k : Type} [Field k] (x : LaurentSeries k) : Prop := Ord 0 x ∧ x.coeff 0 ≠ 0

structure FrobeniusGammaData (k : Type) [Field k] (ℓ : ℕ) where
  φ : LaurentSeries k →ₐ[k] LaurentSeries k
  γ : LaurentSeries k →ₐ[k] LaurentSeries k
  ψ : LaurentSeries k →+ LaurentSeries k
  u : LaurentSeries k
  c : LaurentSeries k
  c₀ : k
  hu : IsUnitR u
  φ_v : φ (vv k) = u * vv k ^ ℓ
  φ_ord : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x → Ord (ℓ * j) (φ x)
  hc : IsUnitR c
  γ_v : γ (vv k) = vv k + c * vv k ^ 2
  γ_bij : Function.Bijective γ
  γ_φ : ∀ x, γ (φ x) = φ (γ x)
  hc₀ : c₀ ≠ 0
  γ_lead : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x →
    Ord (j + 1) (γ x - x) ∧ Ord (j + 2) (γ x - x - ((j : k) * c₀) • (vv k * x))
  ψ_φ : ∀ a x, ψ (φ a * x) = a * ψ x
  ψ_one : ψ 1 = 1
  ψ_γ : ∀ x, ψ (γ x) = γ (ψ x)

def ResidueAvoidanceOfPrimes : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ sp : ℤ) (U : Multiset ℤ) (Sz : Finset ℤ),
    (∀ x ∈ ClN G h η U, ∃ W ∈ Sz, 0 ≤ (if G then x else (h : ℤ) - x) - W ∧
      (if G then x else (h : ℤ) - x) - W ≤ sp) →
    (∀ W ∈ Sz, ∀ j ∈ Finset.Icc (-2 * σ - 2 - sp) ((η : ℤ) + 2 * σ + 3), W - j ≠ 0) →
    (¬ ∃ W ∈ Sz, ∃ j ∈ Finset.Icc (-2 * σ - 2 - sp) ((η : ℤ) + 2 * σ + 3),
      W - j ≠ 0 ∧ (ℓ : ℤ) ∣ W - j) →
    ResidueAvoidance ℓ G h η σ U

end Formalism.IrreducibleCountingLemmas.TOP
