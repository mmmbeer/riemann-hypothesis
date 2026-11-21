import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def badInt (E : Type) [Field E] [NumberField E] : ℕ := 2 * (NumberField.discr E).natAbs

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def GoodPlace (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (ℓ N : ℕ) : Prop :=
  ℓ.Prime ∧ (ℓ : 𝓞 c.F) ∈ la.asIdeal ∧ Nat.Coprime ℓ l.M ∧ Nat.Coprime ℓ (badInt E) ∧ Nat.Coprime N ℓ

end

example (E : Type) [Field E] [NumberField E] (n k : ℕ) : GenLat.TrivAt (⟨stdLat E n⟩ : GenLat E n) k :=
  ⟨1, Nat.coprime_one_left k, by simp, by simp⟩

example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (la : HeightOneSpectrum (𝓞 c.F)) (ℓ N : ℕ) (h : GoodPlace c la ℓ N) : ℓ ≠ 2 := by
  rintro rfl
  have := h.2.2.2.1
  exact absurd (Nat.Coprime.eq_one_of_dvd this (Dvd.intro _ rfl)) (by decide)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces
