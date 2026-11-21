import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidNormaliserGenerators

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt comp1 addOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Ops

variable {S : Scheme.{0}}

variable (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsRigPull (φ : A ⟶ A) (k N : ℤ) {T : Over S} (s : LB.Sec (LPow A L.L k T)) (s' : LB.Sec (LPow A L.L N T)) :
    Prop :=
  ∃ α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![N, -k]),
    α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α (ptSecT A (1 : T ⟶ A)).left) (rigT A L.L L.rig T (N - k)) ∧
    IsTwistPull A L.L (T ◁ φ) (snd T A ≫ φ) (whiskerLeft_snd _ _) N k α s s'

def HasFinOrder {k : ℤ} {T : Over S} (ga : ThetaGrp A L.L k T) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ga.pt ^ M = 1 ∧
    LB.Gen.Corr L.L _ _ _ _ (ReciprocityTheory.ChartRestriction.G.Out.powGen A L.L k ga M) (LB.oneGen L.L)

end Ops

section Two

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R)))
  (F : Type) [Field F] [Algebra (FractionRing R) F]

def cmp : (UnifPre.GF (R := R) (G := G) F).left ⟶ (TF (R := R) F ⊗ G).left :=
  pullback.lift (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (UnifPre.gFK (R := R) (G := G) F) (by
    have h : (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ jFK (R := R) F =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.snd G.hom (jK R) :=
      pullback.condition
    show _ ≫ jFK (R := R) F ≫ jK R = (_ ≫ pullback.fst G.hom (jK R)) ≫ G.hom
    rw [← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])

theorem cmp_snd : cmp G F ≫ (snd (TF (R := R) F) G).left = UnifPre.gFK (R := R) (G := G) F :=
  pullback.lift_snd _ _ _

variable {G} {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  [GrpObj G] [IsCommMonObj G]

def SameSec (U : UnifPre I D A G) (k : ℕ) (σ : LB.Sec (LPow G U.LG.L (k : ℤ) (TF (R := R) F)))
    (σ' : U.SecGF F k) : Prop :=
  GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => UnifPre.gFK (R := R) (G := G) F) (fun _ => (k : ℤ)) σ'
    (fun _ : Fin 1 => (snd (TF (R := R) F) G).left) (fun _ => (k : ℤ)) σ (cmp G F) 1

end Two

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def normaliser (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ ∑ i : Fin (Dw.mult τ), a (τ, i)

example (α : 𝓞 E) : normaliser Dw c 0 α = 1 := by simp [normaliser]

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable (Xo c) in

def IsThetaValue (nab : NabV Xo c) (y : IntFr Xo c T io) {n : ℕ} (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (w : T.Fr) : Prop :=
  letI := io.toAlgebra
  ThValAt Xo c nab y.1 x P w ∧ ∀ f : Rul Xo c, IsThRule Xo c nab x P f → evI y f = w

end Val

structure IsBalancedGauge {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : Germ.FB.toK k B.ph1 = Germ.FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h +
    ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : Germ.FB.toK k B.ph2 = Germ.FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h +
    ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, Germ.FB.toK k (B.ad a) = Germ.FB.expS k
    (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

end GlobalTheory.IndefiniteRowSideFullHecke.RigidNormaliserGenerators
