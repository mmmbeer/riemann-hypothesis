import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundOddRamifiedOfCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.PullbackSections

section Types

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
variable (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F))

def placeOf (τ : E →+* ℂ) : Ideal (𝓞 E) :=
  la.asIdeal.comap (RingOfIntegers.mapRingHom (embF c τ))

def placePair (τ : E →+* ℂ) : Sym2 (Ideal (𝓞 E)) :=
  s(placeOf c la τ, placeOf c la (ComplexEmbedding.conjugate τ))

abbrev Pairs : Type := Set.range (placePair c la)

instance : Fintype (Pairs c la) := by classical exact Set.fintypeRange _

instance : DecidableEq (Pairs c la) := Classical.decEq _

end Types

section Parts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Germ.PS T.Fr n (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P

end Parts

end GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts
