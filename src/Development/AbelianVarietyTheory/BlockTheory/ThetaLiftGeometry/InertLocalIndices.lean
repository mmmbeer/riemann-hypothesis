import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Polynomial
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def InertOver (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = P.asIdeal

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v' : HeightOneSpectrum (𝓞 D.host.F), v' ≠ v →
    (Units.val (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

theorem locAt_one (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : LocAt V v 1 := by
  intro v' _
  simp only [OneMemClass.coe_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HasResC (A : FamIn D.what₂.LL G Pl0 T D.R.m) (p : Pl0 → D.what₂.LL[X]) (x : A.ok A.μ0 × ℕ → ℂ) : Prop :=
  ∀ P : A.ok A.μ0, Col.heckePoly (A.fam.R A.μ0).n (A.fam.R A.μ0).q x P =
    (p P.1 * (A.fam.R A.μ0).blockProd P).map D.what₂.embLL


variable (R : RealDat D A Ks)

abbrev levX (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

structure InertIx (t : T) where

  v : HeightOneSpectrum (𝓞 D.host.F)

  P : Formalism.L2.DIV.Pl D.host.E
  inert : InertOver v P
  offG : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
  offS : P ∉ R.Sb
  offQ : P ∉ R.Q t

  x : Bridge.Gf D.sp.X'
  loc : LocAt D.sp.X' v x

def InertIx.unit (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Formalism.L2.DIV.Pl D.host.E) (h1 : InertOver v P)
    (h2 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (h3 : P ∉ R.Sb) (h4 : P ∉ R.Q t) : InertIx R t :=
  ⟨v, P, h1, h2, h3, h4, 1, locAt_one _ _⟩

def InertTie (TI : ∀ t, InertIx R t → Module.End ℂ (R.HX t).H) : Prop :=
  ∀ (t : T) (i : InertIx R t), ∃ reps : Finset (Bridge.Gf D.sp.X'),
    Bridge.IsDC (levX R t) i.x reps ∧ (∀ a ∈ reps, LocAt D.sp.X' i.v a) ∧
      ∀ f : (R.HX t).H, (R.HX t).e (TI t i f) = Bridge.dcOp reps ((R.HX t).e f)

end GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

end
