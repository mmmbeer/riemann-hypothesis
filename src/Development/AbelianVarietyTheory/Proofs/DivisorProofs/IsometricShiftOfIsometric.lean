import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.HermLB

namespace GlobalTheory.CovTest.GeoSwap

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

end GlobalTheory.CovTest.GeoSwap
