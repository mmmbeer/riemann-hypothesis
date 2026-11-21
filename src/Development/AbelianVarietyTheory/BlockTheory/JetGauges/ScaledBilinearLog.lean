import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledBilinearLog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

section Bilinear

variable {S : Type} [CommRing S] {d : ℕ}

def IsLog (G : Germ.FGLaw S d) (ℓ : Germ.Pt S 1 d) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) ∧ TB.dLin ℓ = 1 ∧
    Germ.comp1 ℓ (G.add (Germ.pt S (n := 2) d 0) (Germ.pt S (n := 2) d 1)) =
      Germ.comp1 ℓ (Germ.pt S (n := 2) d 0) + Germ.comp1 ℓ (Germ.pt S (n := 2) d 1)

example [Algebra ℚ S] (h : TB.LogSt) (G : Germ.FGLaw S d) : ∃ ℓ, IsLog G ℓ := h S d G

def bilLog (ℓ : Germ.Pt S 1 d) (c : Matrix (Fin d) (Fin d) S) {n : ℕ} (P Q : Germ.Pt S n d) : Germ.PS S n d :=
  ∑ i : Fin d, ∑ j : Fin d, MvPowerSeries.C (c i j) * Germ.comp1 ℓ P i * Germ.comp1 ℓ Q j

def IsSymBal {O : Type} (act : O → Germ.Pt S 1 d) (bar : O → O) (c : Matrix (Fin d) (Fin d) S) : Prop :=
  (∀ u v : Fin d → S, dotProduct u (c.mulVec v) = dotProduct v (c.mulVec u)) ∧
  ∀ (a : O) (u v : Fin d → S),
    dotProduct ((TB.dLin (act a)).mulVec u) (c.mulVec v) =
      dotProduct u (c.mulVec ((TB.dLin (act (bar a))).mulVec v))

example (ℓ : Germ.Pt S 1 d) {n : ℕ} (P Q : Germ.Pt S n d) : bilLog ℓ 0 P Q = 0 := by
  simp [bilLog]

example {O : Type} (act : O → Germ.Pt S 1 d) (bar : O → O) : IsSymBal act bar 0 := by
  simp [IsSymBal]

end Bilinear

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]

def IsScaledBy (y : FrPt Xo c S) (C : ChartAt Xo c y) (ℓ : Germ.Pt S 1 C.d)
    (b : ℕ → Matrix (Fin C.d) (Fin C.d) S)
    (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
    (u : Jet S (Fin 2 × Fin C.d) m) =
      psJet m (Germ.FB.expS S (-(bilLog ℓ (b m) (Germ.pt S (n := 2) C.d 0) (Germ.pt S (n := 2) C.d 1)))) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m)
      (Formalism.L2.Pj.scaleGen (cφ ![jpt y C.d C.x m (0 : Fin 2), jpt y C.d C.x m (1 : Fin 2)]) (cε 2)
        (unitΓ u) (C.e m))

def SameFamilies (y : FrPt Xo c S) (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e'

def KeepsRig (y : FrPt Xo c S) (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)

def withFrames (y : FrPt Xo c S) (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m)
    (hf : SameFamilies y C e') (hr : KeepsRig y C e') : ChartAt Xo c y where
  d := C.d
  B := C.B
  uvec := C.uvec
  x := C.x
  e := e'
  wP := C.wP
  h := C.h
  chart := C.chart
  frame := hf
  prim := C.prim
  gauge := C.gauge
  rig0 := hr

example (y : FrPt Xo c S) (C : ChartAt Xo c y) : withFrames y C C.e C.frame C.rig0 = C := rfl

end Twist

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledBilinearLog
