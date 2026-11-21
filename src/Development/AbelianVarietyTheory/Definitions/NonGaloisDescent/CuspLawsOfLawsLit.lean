import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive

section
noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker

namespace GlobalTheory.LocLanglands.GammaModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem arg_three_one (g : GL (Fin 1) k) (x : Fin 1 → Fin 1 → k) :
    (emb₂ k (stdSum (rfl : 1 + (1 + 1) = 3)) (g, 1) * lowUnip rfl (padRow x) *
        emb₂ k (stdSum (rfl : 1 + (1 + 1) = 3)) (1, longElt (1 + 1) k)).val =
      !![g.val 0 0, 0, 0; x 0 0, 0, 1; 0, 1, 0] := by
  have e0 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 0 = Sum.inl 0 := by decide
  have e1 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 1 = Sum.inr 0 := by decide
  have e2 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 2 = Sum.inr 1 := by decide
  have p0 : padRow x 0 0 = x 0 0 := rfl
  have p1 : padRow x 1 0 = 0 := rfl
  rw [Units.val_mul, Units.val_mul, val_emb₂, val_emb₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, lowUnip, longElt, e0, e1, e2, p0, p1, Fin.ext_iff]

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem lowUnip_zero {m r n : ℕ} (hn : m + r = n) : lowUnip hn (0 : Matrix (Fin r) (Fin m) k) = 1 := by
  ext1
  simp [lowUnip]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem longElt_one : longElt (0 + 1) k = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [longElt]



end GlobalTheory.LocLanglands.GammaModel

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.CuspModel

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_ofChar (χ ψ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) (e : ψ = χ⁻¹) :
    DualCl (IrrGL.ofChar χ hχ) (IrrGL.ofChar ψ hψ) := by
  subst e
  exact ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ⁻¹ hψ, rfl, rfl,
    ProjLine.nonempty_equiv_contra_ofChar (χ := detChar (Fin 1) χ) hχ.detChar⟩

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r rc : IrrGL (w.adicCompletion E) → WD h}






end GlobalTheory.LocLanglands.CuspModel

end
end
