import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalActionLiftPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS pt ev comp1 addOf FB)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Scalar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def nn (Dw : Datum H) {l : Level H} (c : Coeff l) (α : 𝓞 E) (a : (E →+* ℂ) × ℕ → ℕ) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ (∑ i : Fin (Dw.mult τ), a (τ, i))

example (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) : nn Dw c 1 a = 1 := by
  simp [nn]

example (Dw : Datum H) {l : Level H} (c : Coeff l) (α β : 𝓞 E) (a : (E →+* ℂ) × ℕ → ℕ) :
    nn Dw c (α * β) a = nn Dw c α a * nn Dw c β a := by
  simp [nn, mul_pow, Finset.prod_mul_distrib]

end Scalar

section Gauge

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

structure IsBalancedGauge (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, FB.toK k (B.ad a) = FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
    ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

end Gauge

section Alpha

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

end Alpha

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O]

def IsDiagAct {D' D : DegPre R} {n : ℕ} (pD : IsPowDeg D' D n) [Module O D'.X] [Module O D.X]
    (oa' : D'.OAct O) (oa : D.OAct O) : Prop :=
  (∀ (a : O) (x : D'.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧
    ∀ (a : O) (i : Fin n), oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a

end Deg

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalActionLiftPull
