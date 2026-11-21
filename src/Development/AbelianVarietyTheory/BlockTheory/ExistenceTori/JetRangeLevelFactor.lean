import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def totalDeg (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def RowsDominant (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, Antitone fun i : Fin (Dw.mult τ) => a (τ, i)

def IsLevelFactor (l : Level H) (al : 𝓞 E) (q : ℕ) : Prop :=
  al ∈ Algebra.adjoin ℤ {H.w0} ∧ al * H.bar al = (q : 𝓞 E) ∧ Odd q ∧ q ∣ l.M ∧ IsCoprime al (H.bar al) ∧
    l.Mb ≤ Ideal.span {H.bar al}

def InJetRange (Dw : Datum H) (l : Level H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ) : Prop :=
  RowsDominant Dw a ∧ Dw.p + Dw.q ≤ n ∧ IsLevelFactor l al q ∧ totalDeg Dw a + 2 ≤ q

section Rig

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

end Rig

variable {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def NoCommonZero (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ), InJetRange Dw l a n al q →
    ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)),
      ∃ (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n ∧
        (∀ b, KilledBy Xo (Ideal.span {H.bar al}) (levPt Xo y.x (x b))) ∧
        (∃ v, ThValAt Xo c nab y x P v) ∧ ∀ v, ThValAt Xo c nab y x P v → v ≠ 0

end GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
