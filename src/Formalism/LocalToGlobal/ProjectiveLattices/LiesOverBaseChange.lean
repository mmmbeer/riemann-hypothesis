import Formalism.LocalToGlobal.ProjectiveLattices.BetaAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure LatB (E : Type) [Field E] [NumberField E] where
  Y : Type
  [add : AddCommGroup Y]
  [free : Module.Free ℤ Y]
  [fin : Module.Finite ℤ Y]
  [md : Module (𝓞 E) Y]
  beta : Y → Y → ℝ

attribute [instance] LatB.add LatB.free LatB.fin LatB.md

section
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

def DatAt.toLatB (A : DatAt Y P) : LatB E := ⟨A.Ylat, A.beta⟩

end

open PointsOfFlagModel

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}

def N3Tower (T : Tower p Xo c) : Prop := (∀ v, N3AtPoints (T.Y v) p) ∧ ∀ n w, N3AtPoints (T.YN n w) p

def AddTow (T : Tower p Xo c) : Prop := (∀ v, BetaAdd (T.Y v) p) ∧ ∀ n w, BetaAdd (T.YN n w) p

def BalTow (T : Tower p Xo c) (cj : E → E) : Prop := (∀ v, BetaBal (T.Y v) p cj) ∧ ∀ n w, BetaBal (T.YN n w) p cj

def PosDefTow (T : Tower p Xo c) : Prop := (∀ v, BetaPosDef (T.Y v) p) ∧ ∀ n w, BetaPosDef (T.YN n w) p

def RankTow (T : Tower p Xo c) (r j : ℕ) : Prop := (∀ v, YlRank (T.Y v) p r j) ∧ ∀ n w, YlRank (T.YN n w) p r j

variable {T : Tower p Xo c}

def lattice₂ (hN : N3Tower T) : ∀ {Z : MdlC}, Pt T Z → LatB E
  | .xm, y => (Classical.choice (hN.1 y.1 y.2.1 y.2.2)).toLatB
  | .yy, y => (Classical.choice (hN.1 y.1 y.2.1 y.2.2.1)).toLatB
  | .xn n, y => (Classical.choice (hN.2 n y.1 y.2.1 y.2.2)).toLatB

abbrev YlatP (hN : N3Tower T) {Z : MdlC} (y : Pt T Z) : Type := (lattice₂ hN y).Y

theorem latticeAt_cases (hN : N3Tower T) (Q : LatB E → Prop)
    (hb : ∀ v (C : SCF p) (P : PtC (T.Y v) C) (A : DatAt (T.Y v) P), Q A.toLatB)
    (hd : ∀ n w (C : SCF p) (P : PtC (T.YN n w) C) (A : DatAt (T.YN n w) P), Q A.toLatB) :
    ∀ {Z : MdlC} (y : Pt T Z), Q (lattice₂ hN y)
  | .xm, y => hb y.1 y.2.1 y.2.2 _
  | .yy, y => hb y.1 y.2.1 y.2.2.1 _
  | .xn n, y => hd n y.1 y.2.1 y.2.2 _

theorem latticeAt_form_add_left (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) (a a' b : YlatP hN y) :
    (lattice₂ hN y).beta (a + a') b = (lattice₂ hN y).beta a b + (lattice₂ hN y).beta a' b :=
  latticeAt_cases hN (fun L => ∀ a a' b : L.Y, L.beta (a + a') b = L.beta a b + L.beta a' b)
    (fun v C P A => hA.1 v C P A) (fun n w C P A => hA.2 n w C P A) y a a' b

theorem latticeAt_form_symm (hN : N3Tower T) {Z : MdlC} (y : Pt T Z) (a b : YlatP hN y) :
    (lattice₂ hN y).beta a b = (lattice₂ hN y).beta b a :=
  latticeAt_cases hN (fun L => ∀ a b : L.Y, L.beta a b = L.beta b a)
    (fun _ _ _ A a b => betaAt_symm _ _ _ a b) (fun _ _ _ _ A a b => betaAt_symm _ _ _ a b) y a b

theorem latticeAt_form_add_right (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) (a b b' : YlatP hN y) :
    (lattice₂ hN y).beta a (b + b') = (lattice₂ hN y).beta a b + (lattice₂ hN y).beta a b' := by
  rw [latticeAt_form_symm, latticeAt_form_add_left hN hA, latticeAt_form_symm hN y b a, latticeAt_form_symm hN y b' a]

def beP (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) : YlatP hN y →ₗ[ℤ] YlatP hN y →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => (lattice₂ hN y).beta a b)
      (fun b b' => latticeAt_form_add_right hN hA y a b b')).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [latticeAt_form_add_left hN hA y a a' b])).toIntLinearMap






end Formalism.L2.Pj
end
end

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def lamOf (la : HeightOneSpectrum (𝓞 c.F)) : PointsOfFlagModel.abelian₂ (Formalism.MainNotions.WeightAlgebra.resCh la) c :=
  ⟨la, by
    have h : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F ⧸ la.asIdeal) = 0 := by
      unfold Formalism.MainNotions.WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)⟩

def LiesOverBaseChange (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (η : PointsOfFlagModel.Pt Tw .yy) : Prop :=
  letI := io.toAlgebra
  η.1 = lamOf la ∧ ∃ eF : T.Fr →+* ↥η.2.1.S,
    eF.comp io = η.2.2.1.fK ∧
    (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧
    (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧
    η.2.2.1.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x ∧
    ∀ τ i, ∃ u' : Sp (DualNumber ↥η.2.1.S) ⟶ (Tw.Y η.1).oF.t.G.left,
      u' ≫ (Tw.Y η.1).m.φ = (η.2.2.2.u τ i).left ∧
      u' ≫ (Tw.Y η.1).m0.toSABMap.φ = spMap (dualMap eF) ≫ y.1.u τ i

end Formalism.L2.Pj
end
end
