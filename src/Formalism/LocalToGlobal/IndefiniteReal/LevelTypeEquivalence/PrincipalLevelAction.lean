import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def principalLevelAction (g : G) : (GA D (Yc D 0) → ℂ) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)

def actYt (t : T) (j : ℕ) (g : G) : (GA D (Yc D j) → ℂ) →ₗ[ℂ] (GA D (Yc D j) → ℂ) :=
  actL (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.eG g)

def actX (t : T) (g : G) : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) := actL D.sp.X' R.βX (R.datXt t) (R.eG g)

def actW (i : Fin D.R.m) (g : G) : (GA D (Wc D i) → ℂ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)

def fX (t : T) : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def LiftsAll : Prop :=
  LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) ∧
    (∀ t j, j < D.R.m → LiftsExist (Yc D j) (R.βY j) (R.datYt t j R.triv)) ∧
    (∀ t, LiftsExist D.sp.X' R.βX (R.datXt t)) ∧
    (∀ i, LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)) ∧
    (∀ i t, LiftsExist (Vc D i) (R.βV i) (R.datVt i t))

variable {R} in

def IrrX (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop := ∀ χ ∈ A.X, IsAbsIrrChar χ

def ActTieX : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), fX R t (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) = actX R t g ∘ₗ fX R t (R.jX t x)

def EquivIoY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ (g : G) (F F' : R.CC t (k + 1)),
    (F' : SmT (R.MY (k + 1)) →ₗ[ℂ] (GA D (Yc D (k + 1)) → ℂ)) =
        actYt R t (k + 1) g ∘ₗ (F : SmT (R.MY (k + 1)) →ₗ[ℂ] (GA D (Yc D (k + 1)) → ℂ)) →
      ((R.ioY t k F' : R.CC t k) : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ)) =
        actYt R t k g ∘ₗ ((R.ioY t k F : R.CC t k) : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ))

def ThFEquiv : Prop :=
  ∀ i t (g : G) (x : A.fam.amb.FL i t),
    R.thF i t (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) = postOn (R.MW i (sg0 D A)) (actW R i g) (R.thF i t (R.jV i t x))

end Defs

end Formalism.IndefR.Eqv.Act

end
