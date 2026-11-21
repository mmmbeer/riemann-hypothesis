import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev RPt (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Fin m → Fin n → ℂ

def IsRealPtO (θ : InfFam D) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) : Prop :=
  w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of (z τ)

def gramAt (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  V.gram.map (tauE D τ)

def efAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  -2 * (tauE D τ D.host.xi0 * ((gramAt S τ)⁻¹ * yᴴ * gramAt T τ * x).trace).re

def hAt (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  (efAt S T τ (cplxO (sS τ) (sT τ) x) y : ℂ) + Complex.I * (efAt S T τ x y : ℂ)

def hR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (z z' : RPt D T.rank S.rank) : ℂ :=
  ∑ τ, hAt S T sS sT τ (Matrix.of (z τ)) (Matrix.of (z' τ))

def RealPtEx (D : D7) : Prop :=
  ∀ (θ : InfFam D) (m n : ℕ), IsInfFam θ → ∀ z : RPt D m n, ∃! w, IsRealPtO θ z w

end Formalism.IndefR.Mi
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Fock.DRho Matrix

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isRealPtO_iff {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) :
    IsRealPtO θ z w ↔ w = Lb D m n z := by
  have e := Formalism.IndefR.Eqv.eq_thetaC D hθ
  subst e
  constructor
  · rintro ⟨h1, h2⟩
    have hf : ∀ i j, finPart D (w i j) = 0 := fun i j => by
      have := congrFun (congrFun h1 i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    rw [← Lb_sigH w hf]
    congr 1
    funext ρ i j
    have := congrFun (congrFun (h2 ρ) i) j
    simp only [compAt, Matrix.map_apply, Matrix.of_apply] at this
    rw [sigH_apply]
    exact this
  · rintro rfl
    refine ⟨?_, fun τ => compAt_Lb z τ⟩
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    exact finPart_Lb z i j

theorem realPtEx_holds : RealPtEx D := by
  intro θ m n hθ z
  exact ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl, fun w hw => (isRealPtO_iff hθ z w).1 hw⟩

end Formalism.IndefR.Mi
end
end
