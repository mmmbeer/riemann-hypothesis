import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ParabSt

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))

def embP (S T : HSp D) {ρ : ℕ} (CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M' : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M' ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram).map (incA D))

def embQ (S T S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (x : WO S0 T) : WO S T :=
  HMul.hMul x ((S0.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) BS * S.gram).map (incA D))

def ellS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (F : WO S T → ℂ) : ℂ :=
  ∫ M in 𝓕, F (embS S T CS M) ∂μ

def RedS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (F : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ellS S T CS μ 𝓕 (heisO ψ S T w F)

def descS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (f : WO S T → ℂ) : WO S0 T → ℂ :=
  fun x => RedS ψ S T CS μ 𝓕 f (embQ S T S0 BS x)

def IsDescSOf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ)) : Prop :=
  ∀ g0 g h, IsLeviEmb S CS CS' S0 BS g0 g → ∀ f, IsThetaFunO ψ S T f →
    descS ψ S T CS μ 𝓕 S0 BS (om (g, h) f) = om0 (g0, h) (descS ψ S T CS μ 𝓕 S0 BS f)

example (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) : IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 1 1 := by
  intro g0 g h _ f _
  simp

end Formalism.IndefR.Mi

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCutoff (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) (β : GA D S → ℝ) : Prop :=
  (∀ h, 0 ≤ β h) ∧ Measurable β ∧ ∀ h,
    Integrable (fun p : NI S CS × GA D S0 => β ((p.1 : GA D S) * lev p.2 * h)) (μN.prod μ0) ∧
      ∫ p, β ((p.1 : GA D S) * lev p.2 * h) ∂(μN.prod μ0) = 1

def cutInt (S : HSp D) (ν : Measure (GA D S)) (β : GA D S → ℝ) (Φ : GA D S → ℂ) : ℂ :=
  ∫ h, (β h : ℂ) * Φ h ∂ν

def IsPsiUVal (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) (v : ℂ) : Prop :=
  ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    v = ψ (Algebra.trace (AF D.host.F) (AE D) (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then u i j else 0))

open Classical in

def psiU (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) : ℂ :=
  if h : ∃ v, IsPsiUVal ψ S CS g v then h.choose else 1

example (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) [IsProbabilityMeasure (μN.prod μ0)] :
    IsCutoff S S0 CS lev μN μ0 (fun _ => 1) :=
  ⟨fun _ => zero_le_one, measurable_const, fun _ => ⟨integrable_const _, by simp⟩⟩

end Formalism.IndefR.Mi

end
end
