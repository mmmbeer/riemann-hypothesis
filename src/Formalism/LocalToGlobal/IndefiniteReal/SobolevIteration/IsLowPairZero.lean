import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ParabSt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def perpSub (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) :
    AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | Formalism.IndefR.Eqv.IsPerpI S T C x}
  zero_mem' := by simp [Formalism.IndefR.Eqv.IsPerpI]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Formalism.IndefR.Eqv.IsPerpI] at ha hb ⊢
    rw [Matrix.mul_add, ha, hb, add_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Formalism.IndefR.Eqv.IsPerpI] at ha ⊢
    rw [Matrix.mul_neg, ha, neg_zero]

def uX (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Matrix (Fin S.rank) (Fin r) D.host.E :=
  S.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x * T.gram * C

def jX (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)) (νN : Measure (NI T C)) (𝓕N : Set (NI T C))
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (h : GA D S) (g : GA D T) : ℂ :=
  ∫ n in 𝓕N, Formalism.IndefR.Eqv.ellI S T C μ 𝓕L (heisO ψ S T (ratW T S x) (om (h, (n : GA D T) * g) f)) ∂νN

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftO {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)) (f : WO S T → ℂ) (F : GA D S → ℂ) : GA D T → ℂ :=
  Formalism.IndefR.Lift.liftInt ν 𝓕 (fun (g' : GA D T) (h : GA D S) (s : WO S T → ℂ) => thetaKO om h g' s) f F

end Formalism.IndefR.Tow

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def IsLowPair (θ : InfFam D) {S T' : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (pt' : MvPolynomial (FVar D T'.rank S.rank) ℂ → (WO S T' → ℂ))
    (B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ)) : Prop :=
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ), ∀ φ φ', pt' φ' = om' (atTau θ S τ g, 1) (pt' φ) →
    ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → B φ' (Function.update v τ w) = B φ v) ∧
  (∀ τ, ∀ X ∈ lieAt S τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (oneP θ S τ X t, 1) (pt' φ) z) (pt' φ' z) 0) →
    ∀ (v : M.Vec) (w : M.sm τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v τ)) (w : M.H τ) 0 →
      B φ' v + B φ (Function.update v τ w) = 0) ∧
  (∀ τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D T' τ), ∀ φ φ', pt' φ' = om' (1, atTau θ T' τ k) (pt' φ) →
    ∀ v g', B φ' v g' = B φ v (g' * atTau θ T' τ k)) ∧
  (∀ τ, ∀ Y ∈ lieAt T' τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => om' (1, oneP θ T' τ Y t) (pt' φ) z) (pt' φ' z) 0) →
    ∀ v g', HasDerivAt (fun t : ℝ => B φ v (g' * oneP θ T' τ Y t)) (B φ' v g') 0)

end Formalism.IndefR.Tow

end
end
