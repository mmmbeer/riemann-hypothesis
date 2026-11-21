import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsHilbertModuleExists

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open Formalism.L2.Host (HChar ordF atFin IsUnitAt)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.AdelicLiftCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0)
include hL

end Places

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (ρ : G →* Module.End ℂ W)

end Generic

section Forms

variable {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

include hc

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsResidual (i : Fin D.R.m) (t : T) (s : ℂ →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  (∀ PP ∈ R.Pg, m PP = (LiftFormsMainTerm.conjRes s (R.chi ((i : ℕ) + 1)) PP)⁻¹) ∧ ∀ PP ∈ R.Q t, m PP = LiftFormsMainTerm.conjRes s (R.xiR t) PP

variable {R}

section Residual

variable {i : Fin D.R.m} {t : T} {s : ℂ →+* ℂ} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hm : IsResidual R i t s m)
  (P : LevelP R.Pg D.R.r ℂ)

include hm

end Residual

section Concl

variable {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ}

variable {t : T} {s : ℂ →+* ℂ} {P : LevelP R.Pg D.R.r ℂ} (X : LiftFormsMainTerm.LiftInput R i σ)
  (HV : HMod (Bridge.Gf (Vc D i) → X.coef.W)) (φ : HV.H ≃ₗ[ℂ] X.src t s P)
  (hφ : ∀ x, (φ x : GA D (Vc D i) → X.coef.W) = X.coef.ext (HV.e x))
  (hip : ∀ x y, IntegrableOn (fun h => ⟪X.coef.ext (HV.e x) h, X.coef.ext (HV.e y) h⟫_ℂ) X.fd X.ν ∧
    ∫ h in X.fd, ⟪X.coef.ext (HV.e x) h, X.coef.ext (HV.e y) h⟫_ℂ ∂X.ν = ⟪x, y⟫_ℂ)

end Concl

variable (R)

variable {R} {F : Face D A}

end GlobalTheory.AdelicLiftCompare

end
