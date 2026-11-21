import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (D) in

def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  have h := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  simpa [labE, labLL, tauE, Host.emb] using h

theorem labE_conj (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

structure ArchLab (D : D7) where
  perm : D.what₂.Tau ≃ D.what₂.Tau
  side : Bool

def ArchLab.emb (A : ArchLab D) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  if A.side then tauE D (A.perm τ) else (starRingEnd ℂ).comp (tauE D (A.perm τ))

def ArchLab.flip (A : ArchLab D) : ArchLab D := ⟨A.perm, !A.side⟩

def ArchLab.pos (A : ArchLab D) : ArchLab D := ⟨A.perm, true⟩

def IsLabOf (σ : D.what₂.LL →+* ℂ) (A : ArchLab D) : Prop := ∀ τ, labE σ τ = A.emb τ

variable (D) in

def baseLab : ArchLab D := ⟨Equiv.refl _, true⟩




variable (D) in

def LabExists : Prop := ∀ σ : D.what₂.LL →+* ℂ, ∃ A : ArchLab D, IsLabOf σ A

variable (D) in

def LabUnique : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (A A' : ArchLab D), IsLabOf σ A → IsLabOf σ A' → A = A'

open Classical in

def labOf (σ : D.what₂.LL →+* ℂ) : ArchLab D :=
  if h : ∃ A : ArchLab D, IsLabOf σ A then h.choose else baseLab D



def rl (A : ArchLab D) {X : Type*} (S : D.what₂.Tau → X) : D.what₂.Tau → X := fun ρ => S (A.perm.symm ρ)



def cv (σ : D.what₂.LL →+* ℂ) {X : Type*} (f : X → D.what₂.LL) : X → ℂ := fun x => σ (f x)



def levSig (σ : D.what₂.LL →+* ℂ) {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E D.what₂.LL n) :
    Formalism.L2.DIV.LevDat D.host.E ℂ n where
  r := L.r
  hr := L.hr
  t := L.t
  s := L.s
  Pg := L.Pg
  Q := L.Q
  P := ⟨L.P.H, (Units.map σ.toMonoidHom).comp L.P.chi⟩
  cg := fun i PP => (Units.map σ.toMonoidHom).comp (L.cg i PP)
  xq := fun PP => (Units.map σ.toMonoidHom).comp (L.xq PP)

def IsConjChar (σ : D.what₂.LL →+* ℂ) (χL : (AE D)ˣ →* D.what₂.LLˣ) (χ χσ : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D χσ ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 →
    ((χσ x : Circle) : ℂ) * D.what₂.embLL (χL x : D.what₂.LL) = ((χ x : Circle) : ℂ) * σ (χL x : D.what₂.LL)


def IsThPKernelSig (ψ : AddChar (AF D.host.F) ℂ) (σ : D.what₂.LL →+* ℂ)
    (μL : ℕ → (AE D)ˣ →* D.what₂.LLˣ) (ηL : (AE D)ˣ →* D.what₂.LLˣ) (μ : ℕ → (AE D)ˣ →* Circle)
    (η : (AE D)ˣ →* Circle) (j : ℕ) (Vj Wj : HSp D)
    (th : GA D Wj → GA D Vj → (Datum.WO Vj Wj → ℂ) → ℂ) : Prop :=
  ∃ (μσ : ℕ → (AE D)ˣ →* Circle) (ησ : (AE D)ˣ →* Circle),
    (∀ k, IsConjChar σ (μL k) (μ k) (μσ k)) ∧ IsConjChar σ ηL η ησ ∧
      Lift.IsThPKernel ψ μσ ησ j Vj Wj th

def deltaSig (A : ArchLab D) {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) :
    MvPolynomial (Datum.FVar D m n) ℂ :=
  Datum.delta p q (rl A ap) (rl A am)


variable (D) in

def ConjCharUnique : Prop :=
  ∀ χ₁ χ₂ : (AE D)ˣ →* Circle, IsHeckeChar D χ₁ → IsHeckeChar D χ₂ →
    (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → χ₁ x = χ₂ x) → χ₁ = χ₂

end Formalism.IndefR.Conj

end
