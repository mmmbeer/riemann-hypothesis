import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

section
noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsCyc (T : Tower p Ω) (k : ℕ) (χ : Gal p Ω → ZMod (p ^ k)) : Prop :=
  ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val

end GlobalTheory.K5
end
end

section
noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IntegralLocallyConstCochainModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, IsInt p (w g)) ∧ ∀ g ∈ H, ∃ S : Finset Ω, ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong p k (w h) (w g)

def IsTwistedOneCocycle (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, Cong p k (c (g * h)) (c g + ((χ g).val : Ω) ^ j * g (c h))

def IsTwistedOneCoboundary (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt p x ∧ ∀ g ∈ H, Cong p k (c g) (((χ g).val : Ω) ^ j * g x - x)

variable (p) in

def plogQ (m k a : ℕ) : ZMod (p ^ k) :=
  ∑ i ∈ Finset.Icc 1 (2 * k + 2), (-1 : ZMod (p ^ k)) ^ (i + 1) *
    (p : ZMod (p ^ k)) ^ (m * (i - 1) - padicValNat p i) *
    ((i / p ^ padicValNat p i : ℕ) : ZMod (p ^ k))⁻¹ * (a : ZMod (p ^ k)) ^ i

end GlobalTheory.K5
end
end
