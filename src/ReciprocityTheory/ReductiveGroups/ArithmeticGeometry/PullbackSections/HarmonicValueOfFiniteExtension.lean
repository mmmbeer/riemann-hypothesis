import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory


theorem vLa_natCast_inv_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {M : ℕ}
    (hM : (M : 𝓞 K) ∉ la.asIdeal) (d : ℕ) : vLa la (((M : K) ^ d)⁻¹) = 0 := by
  have e : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
  have h1 : la.valuation K (M : K) = 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  simp [vLa, map_inv₀, map_pow, h1]

def FFVMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr), P.map io ∈ FFV (Dw := Dw) T a n

end ReciprocityTheory.ChartRestriction.G.PullbackSections
