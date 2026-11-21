import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def column {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) : Lt1 Dw →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

@[simp] theorem column_apply {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) (ℓ : Lt1 Dw) :
    column m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩ := rfl

section Value

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def canGerm (C : ChartAt Xo c y) (k : ℕ) (f : Germ.PS S 1 C.d) : Germ.PS S 1 C.d :=
  f * Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)

def colVal (C : ChartAt Xo c y) (k : ℕ) (f : Germ.PS S 1 C.d) (α : Lt1 Dw →₀ ℕ) : S :=
  MvPowerSeries.constantCoeff (Germ.DmonOf C.B.G.F C.uvec α (canGerm C k f))

def chartVal (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F)
    (f : Fin n → Germ.PS S 1 C.d) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, colVal C k (f b) (column m b)

example (C : ChartAt Xo c y) (k n : ℕ) (f : Fin n → Germ.PS S 1 C.d) :
    chartVal C k (0 : MvPolynomial (LtN Dw n) c.F) f = 0 := by
  simp [chartVal]

end Value

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms
