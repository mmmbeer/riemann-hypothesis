import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices

open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lat

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

def blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) where
  La := Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))

theorem mem_blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (v : Fin (n₁ + n₂) → E) :
    v ∈ (blockLat Λ₁ Λ₂).La ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ Λ₁.La ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ Λ₂.La := Iff.rfl

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def LatOK {n : ℕ} (bad M : ℕ) (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt M

def blockDat {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F) :
    (Fin (n₁ + n₂) → LevQ Dw l) → c.F :=
  fun q => w₁ (fun b => q (Fin.castAdd n₂ b)) * w₂ (fun b => q (Fin.natAdd n₁ b))

def BlockBeta (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  KPsiIn (Dw := Dw) c →
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
      (∃ ζ : c.F, (∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) ∧
        betaH (Dw := Dw) c (blockLat Λ₁ Λ₂) = ζ * (betaH (Dw := Dw) c Λ₁ * betaH (Dw := Dw) c Λ₂)) ∧
      (Λ₁.La = stdLat E n₁ → betaH (Dw := Dw) c (blockLat Λ₁ Λ₂) = betaH (Dw := Dw) c Λ₂)

end GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices
