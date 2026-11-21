import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv.Act

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Comm

variable {D : D7} {V : HSp D}

theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (matA D V h).map (infPart D) = 1 := by
  rw [GfC, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem comm_inf_fin {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' := (mem_GinfC (D := D) (V := V) (h := a)).1 ha
  have hb' := (mem_GfC' b).1 hb
  have hinf : (matA D V a * matA D V b).map (infPart D) = (matA D V b * matA D V a).map (infPart D) := by
    rw [Matrix.map_mul, Matrix.map_mul, hb', mul_one, one_mul]
  have hfin : (matA D V a * matA D V b).map (finPart D) = (matA D V b * matA D V a).map (finPart D) := by
    rw [Matrix.map_mul, Matrix.map_mul, ha', mul_one, one_mul]
  have key : matA D V (a * b) = matA D V (b * a) := by
    rw [matA_mul, matA_mul]
    ext i j
    exact ae_ext (D := D) (congrFun (congrFun hinf i) j) (congrFun (congrFun hfin i) j)
  first
  | exact Subtype.ext (Units.ext key)
  | (apply Subtype.ext; apply Units.ext; exact key)
  | (apply Subtype.ext; apply Subtype.ext; apply Units.ext; exact key)

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V := by
  unfold oneP
  exact atTau_mem θ τ _

end Comm

section RTr

variable {D : D7} {V : HSp D} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {κ : GA D V}

theorem rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ f) = rTr V κ (Rder θ V τ X f) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, comm_inf_fin (oneP_mem θ τ X t) hκ, ← mul_assoc]

theorem rderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ f) = rTr V κ (RderC θ V τ Z f) := by
  simp only [RderC, rder_rTr θ hκ]
  funext g
  simp only [rTr, Pi.add_apply, Pi.smul_apply]

theorem foldr_comm_rTr (l : List ((GA D V → ℂ) → (GA D V → ℂ)))
    (h : ∀ f ∈ l, ∀ φ, f (rTr V κ φ) = rTr V κ (f φ)) (φ : GA D V → ℂ) :
    l.foldr (fun f acc => f acc) (rTr V κ φ) = rTr V κ (l.foldr (fun f acc => f acc) φ) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun f hf => h f (by simp [hf]))]
    exact h g (by simp) _

end RTr

end Formalism.IndefR.Eqv.Act

end
