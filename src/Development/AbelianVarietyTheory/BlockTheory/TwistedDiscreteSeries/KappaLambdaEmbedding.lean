import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable (D) in

abbrev Eig : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badF : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def rowsAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ R.HE.H := (R.EEat P).comap R.HE.e

def liftPart (i : Fin D.R.m) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R) c ⊓
    R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

def datXP (t : T) (P : LevelP R.Pg D.R.r ℂ) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B

def scal (t : T) : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def formsAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H where
  carrier := {x | ∀ v, HasType D.sp.X' R.βX (datXP R t P) (scal R t x v)}
  add_mem' := by
    intro x y hx hy v κ hκ h
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
  zero_mem' := by
    intro v κ _ h
    simp
  smul_mem' := by
    intro a x hx v κ hκ h
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul]
    ring

def eX (t : T) : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  gaL D.sp.X' R.βX (R.datXt t) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def goodAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H :=
  formsAt R t P ⊓ ⨅ v : SmT R.MX,
    LinearMap.ker ((eX R t - LinearMap.id) ∘ₗ LinearMap.applyₗ v ∘ₗ scal R t)

def kerAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H := goodAt R t P ⊓ LinearMap.ker (R.Th t)

def quotAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H := goodAt R t P ⊓ (kerAt R t P)ᗮ

example (t : T) : datXP R t R.triv = R.datXt t := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding

end
