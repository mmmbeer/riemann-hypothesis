import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsParI

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsQuotFrame (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : Prop :=
  IsIsoFrame T C ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C' = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B0 * T.gram * B0 = T0.gram ∧
    T.rank = 2 * r + T0.rank

def desc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (f : WO S T → ℂ) : WO S T0 → ℂ :=
  fun x0 => Red ψ S T C μ 𝓕 f (embI S T B0 x0)

def IsLeviEmb (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (h0 : GA D T0) (h : GA D T) : Prop :=
  HMul.hMul (mt T h) (C.map (incA D)) = C.map (incA D) ∧
    HMul.hMul (mt T h) (C'.map (incA D)) = C'.map (incA D) ∧
    HMul.hMul (mt T h) (B0.map (incA D)) = HMul.hMul (B0.map (incA D)) (mt T0 h0)

def IsDescOf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ)) : Prop :=
  ∀ g h0 h, IsLeviEmb T C C' T0 B0 h0 h → ∀ f, IsThetaFunO ψ S T f →
    desc ψ S T C μ 𝓕 T0 B0 (om (g, h) f) = om0 (g, h0) (desc ψ S T C μ 𝓕 T0 B0 f)

def hv (T : HSp D) (x y : Fin T.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (x i) * incA D (T.gram i j) * y j

example (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : IsLeviEmb T C C' T0 B0 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Formalism.L2.Theta.mt, map_one]

example (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) : IsDescOf ψ S T C C' T0 B0 μ 𝓕 1 1 := by
  intro g h0 h _ f _
  simp

end Formalism.IndefR.Mi

end
