import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible

noncomputable section

namespace Formalism.MainNotions.IsotypicCorollary

open Formalism.BasicNotions Formalism.BasicNotions.DV

section TypeMultiplicityNumbers₂

variable (D : D7)

def TypeMultiplicityNumbers : Prop :=
  ∃ X : WeightDegreeSizes.LocE D, WeightDegreeSizes.SmallLevelExtremalVectors D X ∧ WeightDegreeSizes.HolomorphicLowestVectors D X ∧ WeightDegreeSizes.MultiplicityTransfer D X

def IsotypicPartsInternal : Prop := Rows.IsotInternal D.what₂

def GoodPartRankSmallLevel (C : NChoice D) : Prop :=
  ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool, ThetaNormsAndLinks.dG D (C.twI w) j b = D.what₂.D0

def Stmt : Prop := TypeMultiplicityNumbers D ∧ IsotypicPartsInternal D ∧ ∀ C : NChoice D, GoodPartRankSmallLevel D C


end TypeMultiplicityNumbers₂

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def KudlaFamilyStatement : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Stmt (Fm.D x i)

end Family

section Part₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.ThetaNormsAndLinks

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

end Part₂

section PartDep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.PDVN

variable {D : D7} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

end PartDep

section ThetaIntegrality₂

open NumberField Classical Formalism.MainNotions.CanonicalTranslateJets

def ThetaIntegrality (D : D7) (X : DivX D) (G : CanonicalTranslateJets.Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La,
    G.Th j w y La ∈ G.intS j w y La ∧
    (∀ s ∈ G.intS j w y La, ∀ b (γ : G.TG j w y La b),
      G.act j w y La b γ (G.pull j w y La s) ∈ G.intSG j w y La) ∧
    (∀ h ∈ G.intSG j w y La, ∀ Dg P, P ∈ G.intP j w → HarmHom G j Dg P →
      (∑ τ, Dg τ) + 1 < D.host.g i → ‖G.jetG j w y La h P‖ ≤ 1)

end ThetaIntegrality₂

section PartDV20

open Formalism.BasicNotions.TH NumberField IsDedekindDomain Finset MeasureTheory Classical Formalism.MainNotions.InnerProductFormulaField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end PartDV20

section ThetaPathData

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.AbsolutelyIrreducibleSpan

end ThetaPathData

section ThetaCommutingSquare₂

open Formalism.MainNotions.DIV

def ThetaCommutingSquare {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) : Prop :=
  ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ h i, Formalism.MainNotions.AbsolutelyIrreducibleSpan.IsPath D.R.m h → Formalism.MainNotions.AbsolutelyIrreducibleSpan.Flippable D.R.m h i →
    4 * D.R.m + 2 < D.R.t + X.s → 2 * D.R.m + 1 < D.R.r + h i * D.R.t + i * X.s →
    (∀ τ (hj : h i < D.R.m), ((2 * (D.R.r + h i * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) <
      2 * ((D.hc τ).e ⟨h i, hj⟩ + X.cInf (D.R.m - i) τ)) →
    ∃ Q : SqSett T Lc X μ i (h i), Q.SeeSaw h

end ThetaCommutingSquare₂

end Formalism.MainNotions.IsotypicCorollary
