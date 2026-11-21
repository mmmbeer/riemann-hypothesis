import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData

section ColVal
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def colExp {κ : Type} [Fintype κ] {n : ℕ} (a : κ × Fin n →₀ ℕ) (i : Fin n) : κ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => a (l, i)

def colValOf (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O) (m : ℕ)
    {κ : Type} [Fintype κ] (u : κ → Fin d → k) {n : ℕ} (P : MvPolynomial (κ × Fin n) k) (f : Fin n → PS k 1 d) : k :=
  ∑ a ∈ P.support, P.coeff a * ∏ i, B.nabVal k h w0 m (f i) u (MvPolynomial.monomial (colExp a i) 1)

end ColVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}

structure PtData (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] where

  complete : IsAdicComplete (maximalIdeal V) V

  tors : P.TorsionIso

  ϖ : V
  irr : Irreducible ϖ

  Q_vw : P.D.toPre.X → ℤ
  isQ : DVR.QForm.IsQ P.D.toPre ϖ Q_vw
  algClosed : IsAlgClosed F

  v_vw : AddValuation F (WithTop ℚ)
  valOver : DVR.ValOver ϖ F v_vw

  d : ℕ
  x : GlobalTheory.JetSer.Fam t.G (Fin d)
  chart : Chart.IsUnivChart t.G d x

  j : t.PP.L.ι
  hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j

  u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb t.PP.L (Out.rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) Out.rosatiε)
  u_norm : ∀ a, GlobalTheory.JetSer.IsNormRos t.PP.L _ _ (u a)

  ρ : LB.Gen (LB.LinComb t.PP.L (GlobalTheory.JetSer.primφ (t.act.act H.w0)) GlobalTheory.JetSer.primε)
  ρ_gen : ρ.IsGen
  ρ_rig : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig

  B : letI := H.starRing; FB V d (𝓞 E)
  isFB : letI := H.starRing; GlobalTheory.JetSer.IsFBOf t.PP t.cub t.act u x j B

namespace PtData
variable {P : PELUnif (maximalIdeal V) t} {F : Type} [Field F] [CharZero F] [Algebra (FractionRing V) F]
  (D : PtData P F)

end PtData

section Basic₂
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]



end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
