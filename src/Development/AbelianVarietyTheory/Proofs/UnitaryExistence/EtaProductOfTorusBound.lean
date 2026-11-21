import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.EtArchPf
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.EtaleProductPrimes
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SymmetricMeasureL2NormEqResolutionL2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.PhiNeOne

section
noncomputable section

namespace GlobalTheory.TorusFrameRigid

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E]

def hfR (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ Hf
    (fun u v w => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c u v => by simp [Hf, Finset.mul_sum, mul_assoc])
    (fun u v w => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c u v => by simp [Hf, Finset.mul_sum, mul_left_comm])

def actR (dim : (E →+* ℂ) → ℕ) (α : 𝓞 E) : Vsp dim →ₗ[ℝ] Vsp dim where
  toFun := act α
  map_add' := GlobalTheory.TupleSumPos.act_add_vec α
  map_smul' c v := by ext i; simp [act, mul_left_comm]

structure Match (Y Y' : PT E) (ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim) : Prop where
  lat : ∀ y, y ∈ Y.L ↔ ψ y ∈ Y'.L
  act : ∀ α y, ψ (act α y) = act α (ψ y)
  herm : (∀ u v, Hf (ψ u) (ψ v) = Hf u v) ∨ ∀ u v, Hf (ψ u) (ψ v) = conj (Hf u v)

variable {Y Y' : PT E} {ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim}

variable [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

open GlobalTheory.SemicharIndep

def EpsBy (Y : PT E) (w : 𝓞 E) : Prop := ∀ y ∈ Y.L, (Y.eps y : ℝ) = Real.cos (Real.pi * (Hf y (act w y)).im)

omit [IsCMField E] in
theorem Match.eps (h : Match Y Y' ψ) {w : 𝓞 E} (he : EpsBy Y w) (he' : EpsBy Y' w) :
    ∀ y ∈ Y.L, Y'.eps (ψ y) = Y.eps y := fun y hy => by
  have : (Y'.eps (ψ y) : ℝ) = Y.eps y := by
    rw [he y hy, he' _ ((h.lat y).1 hy), ← h.act]
    rcases h.herm with h1 | h1 <;> simp [h1]
  exact_mod_cast this

end GlobalTheory.TorusFrameRigid
end
end

section
noncomputable section

namespace GlobalTheory.EtaProdCompare

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductPrimes GlobalTheory.TorusFrameRigid

section Num

variable (E : Type) [Field E] [NumberField E]

def gap (r m r1 : ℕ) : ℝ := A E r m r1 * (1 + Real.log (2 * Real.pi - 1))

end Num

section Torus

variable {E : Type} [Field E] [NumberField E]

def FixBound (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (r1 Nc nt i : ℕ) (y : ℝ) : Prop :=
  ∃ (c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ) (a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin X.r → Vsp X.dim),
    (∀ g t, |c g t| ≤ Nc) ∧ (∀ g t, TrOK X r1 (a g t)) ∧ y ≤ ∏ g, ∑ t, |(c g t : ℝ)| * thRat X s (a g t)

variable {X : PT E} {s : (Fin 1 → Vsp X.dim) → ℂ} {r1 i : ℕ} {y : ℝ}

theorem FixBound.prodBound {Nc nt : ℕ} {N : ℝ} (hN : (Nc : ℝ) ≤ N) (hn : nt ≤ r1 ^ (2 * PT.f E * X.r ^ 2))
    (h : FixBound X s r1 Nc nt i y) : ProdBound X s r1 N i y := by
  obtain ⟨c, a, hc, ha, hy⟩ := h
  exact ⟨fun _ => nt, c, a, fun _ => hn, fun g t => le_trans (by exact_mod_cast hc g t) hN, ha, hy⟩

variable {Y : PT E} {ψ : Vsp X.dim ≃ₗ[ℝ] Vsp Y.dim}

variable [IsCMField E] {r : ℕ} {Z : FD.Data E r} {x : FD.Frame Z.Ψ r}


end Torus

section Record

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) {j i : ℕ} (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def nTerms (D : D7) : ℕ := 5 ^ (2 * PT.f D.host.E * D.R.r ^ 2)

end Record

end GlobalTheory.EtaProdCompare
end
end
