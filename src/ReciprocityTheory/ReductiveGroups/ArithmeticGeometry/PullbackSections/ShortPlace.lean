import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def ShortPlaceASt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1, (T.dδ j w.n).pd} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) → 0 ≤ vAtV y g

def ShortSeriesRamifiedPlaceTwo : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceBqdSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (p : ℕ),
      p ∈ ({D.host.q, D.host.d} : Finset ℕ) → ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

end ReciprocityTheory.ChartRestriction.G.PullbackSections
