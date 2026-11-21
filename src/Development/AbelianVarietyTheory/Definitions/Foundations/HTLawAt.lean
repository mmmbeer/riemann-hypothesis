import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def htv (j : Ω →+* Qbar l) (ζ : Ω) {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (b : ℕ) : Qbar l :=
  ∑ i, o i * j (ζ ^ b * (Polynomial.derivative (P i)).eval (ζ ^ b) / (P i).eval (ζ ^ b))

def HTPres (A : ValuationSubring Ω) (c : Coef l) (m : ℕ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (ζ : Ω) {ι : Type}
    [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ m) ∧ (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧
    GlobalTheory.Col.KumPres A m m ζ (Z m) (fun i => (P i).eval ζ) o

def tval (L : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : Qbar l := ∑ n ∈ Finset.range N, L.coeff n * (z - 1) ^ n

def mass (L : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) (x : ℕ) : Qbar l :=
  ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval L (l ^ (3 * r)) (ξ ^ k)

def HTLawAt (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∀ m, m₀ ≤ m → ∃ (ζ : Ω) (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPres A c m Z ζ P o ∧
    ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j ζ P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j ζ))

end GlobalTheory.KZ
