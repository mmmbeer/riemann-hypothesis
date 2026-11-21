import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)

namespace GlobalTheory.CompanionTheory.OntoAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def NodeGap (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (j : Fin D.R.m) (h : j.1 + 1 < D.R.m),
    (D.R.t : ℚ) + 2 * ((D.R.r + D.R.m * D.R.t + 1 : ℕ) : ℚ) ^ 3 + 1 ≤ (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).b j

def rowsAll (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (MMap (R.MY 0)) :=
  Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P))

def partAll (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badPl R A.μ0) c

def reachedAll (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (partAll R c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R A.μ0 k u x}) k

def dn (y : (R.HX A.μ0).H) : MMap (R.MY 0) := PiTensorProduct.lift.symm (R.thDn A.μ0 y)

def datXP (P : LevelP R.Pg D.R.r ℂ) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q A.μ0) P R.chi (R.xiR A.μ0) Frm.B

def HasLev (P : LevelP R.Pg D.R.r ℂ) (y : (R.HX A.μ0).H) : Prop :=
  ∀ v, ∀ k ∈ levS _ R.βX (datXP R P), ∀ g,
    R.cX.toMap R.prX ((R.HX A.μ0).e y) v (g * k) = levChi _ R.βX (datXP R P) k * R.cX.toMap R.prX ((R.HX A.μ0).e y) v g

def OntoLev (P : LevelP R.Pg D.R.r ℂ) : Prop := ∀ u ∈ rowsAll R P, ∃ y, HasLev R P y ∧ dn R y = u

def OntoAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.Hk3.Core R F → NodeGap D → OntoLev R (R.levR F true)

end GlobalTheory.CompanionTheory.OntoAll

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)
open GlobalTheory.LFun (Fam twist segFam val above IsCont Bounded IsSysParamD)

namespace GlobalTheory.CompanionTheory.OntoAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def badE : Set (HeightOneSpectrum (𝓞 D.host.E)) := above D.host.E (badPl R A.μ0 : Set (HeightOneSpectrum (𝓞 D.host.F)))

def upFun (k : ℕ) (u : MMap (R.MY k)) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec) (h : GA D (Yc D (k + 1))) : ℂ :=
  ∫ g in R.fdY A.μ0 k, star (thetaKO (R.ωY A.μ0 k) g h (R.ptY A.μ0 k φ)) * u v g ∂(R.νY A.μ0 k)

def upFunX (u : MMap (R.MY (D.R.m - 1))) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec)
    (h : GA D D.sp.X') : ℂ :=
  ∫ g in R.fdY A.μ0 (D.R.m - 1), star (thetaKO (R.ωX A.μ0) g h (R.ptX A.μ0 φ)) * u v g ∂(R.νY A.μ0 (D.R.m - 1))

def partAt (k : ℕ) (c : EigSys D) : Submodule ℂ (MMap (R.MY k)) :=
  partDual R.θ (R.MY k) (levS _ (R.βY k) (R.datYt A.μ0 k R.triv)) (levChi _ (R.βY k) (R.datYt A.μ0 k R.triv)) (badPl R A.μ0) c

def chainPar (B : Fam D.host.E) (k : ℕ) : Fam D.host.E :=
  B + ∑ i ∈ Finset.range k, segFam (val (R.toLevCh.mu A.μ0 (i + 1))) D.R.t

def parK (B : Fam D.host.E) (k : ℕ) : Fam D.host.E :=
  if Even k then chainPar R B k else twist (chainPar R B k) (val R.eta)⁻¹

def stepPar (B : Fam D.host.E) (k : ℕ) : Fam D.host.E := twist (chainPar R B k) (val (R.toLevCh.mu A.μ0 (k + 1)))⁻¹

def LGood (B : Fam D.host.E) (k : ℕ) : Prop :=
  ∃ (σ : ℝ) (Λ : ℂ → ℂ), σ < (1 + (D.R.t : ℝ)) / 2 ∧ IsCont (badE R) (stepPar R B k) σ Λ ∧ Λ ((1 + (D.R.t : ℂ)) / 2) ≠ 0

def NSInf (B : Fam D.host.E) (k : ℕ) : Prop :=
  {w : HeightOneSpectrum (𝓞 D.host.E) | w ∉ badE R ∧ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∧
    ∀ β ∈ stepPar R B k w, ∀ e ∈ ({((D.R.t : ℂ) - 1) / 2, -(((D.R.t : ℂ) - 1) / 2), ((D.R.t : ℂ) + 1) / 2, -(((D.R.t : ℂ) + 1) / 2)} : Set ℂ),
      (β : ℂ) ≠ GlobalTheory.LFun.npow w e}.Infinite

def UpNonzero : Prop :=
  ∀ (B : Fam D.host.E) (c : EigSys D),
    (∀ k, k + 1 < D.R.m → IsSysParamD D (badPl R A.μ0) (Yc D k).rank c (parK R B k) → LGood R B k → NSInf R B k →
      ∀ u ∈ partAt R k c, u ≠ 0 → ∃ φ v h, upFun R k u φ v h ≠ 0) ∧
    (IsSysParamD D (badPl R A.μ0) (Yc D (D.R.m - 1)).rank c (parK R B (D.R.m - 1)) → LGood R B (D.R.m - 1) → NSInf R B (D.R.m - 1) →
      ∀ u ∈ partAt R (D.R.m - 1) c, u ≠ 0 → ∃ φ v h, upFunX R u φ v h ≠ 0)

end GlobalTheory.CompanionTheory.OntoAll

end
end
