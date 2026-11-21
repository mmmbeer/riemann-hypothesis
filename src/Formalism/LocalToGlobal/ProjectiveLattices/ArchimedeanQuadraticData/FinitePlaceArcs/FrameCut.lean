import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FinAtOfStatement

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def arcDetR (Dw : Datum H) (V : Type) [CommRing V] : MvPolynomial (ArcLt Dw) (PowerSeries V) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))

abbrev ArcSR (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) : Type :=
  Localization.Away (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)

variable {D : D7} {T : Core D} {j : ℕ}

structure DvrFrame {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] (d : ArcDatumAt T j K₁) (w : HeightOneSpectrum (𝓞 K₁))
    (Z : FinSite K₁ w) where
  Tv : CDVR
  io : K₁ →+* Tv.Fr
  ιT : Tv.Fr →+* Z.K
  ιT_io : ιT.comp io = Z.ι
  norm_le : ∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1
  ϖ : Tv.V
  ϖ_irr : Irreducible ϖ
  norm_ϖ : ‖ιT (algebraMap Tv.V Tv.Fr ϖ)‖ < 1
  [algR : Algebra T.Q.c.F (ArcSR (T.Q.Dw j) Tv.V ϖ)]
  [algW : Algebra T.Q.c.F (ArcS (T.Q.Dw j) Tv.Fr)]
  algW_eq : ∀ r : T.Q.c.F, algebraMap T.Q.c.F (ArcS (T.Q.Dw j) Tv.Fr) r =
    arcι (T.Q.Dw j) Tv.Fr (PowerSeries.C (R := Tv.Fr) (io (algebraMap T.Q.c.F K₁ r)))
  yR : FrPt (T.Q.Xo j) T.Q.c (ArcSR (T.Q.Dw j) Tv.V ϖ)

attribute [instance] DvrFrame.algR DvrFrame.algW

variable {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)]
  {d : ArcDatumAt T j K₁} {w : HeightOneSpectrum (𝓞 K₁)} {Z : FinSite K₁ w}

end Formalism.L2.Pj.QAt
