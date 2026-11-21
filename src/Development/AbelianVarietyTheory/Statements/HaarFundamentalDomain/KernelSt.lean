import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

def KernelSt : Prop :=
  ∀ (D : D7) (S T : HSp D) (C : Ctx S T), 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (m : ℕ) (Q : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ), C.IsFam Q → ∀ (ν : Measure (GA D S)) (𝓖 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓖 ν → ∀ g₁ g₂ : GA D T, ν 𝓖 ≠ ⊤ ∧ IntegrableOn (fun h => ∑ j, om (h, g₁) (C.fvec B (C.uVec Lv hn f') (Q j)) 0 * conj (om (h, g₂) (C.fvec B (C.uVec Lv hn f') (Q j)) 0)) 𝓖 ν ∧ HasSum (fun γ : GQ T => ((ν 𝓖).toReal : ℂ) * ∑ j, ipO μ 𝓕 (om (1, g₁) (C.fvec B (C.uVec Lv hn f') (Q j))) (om (1, γ.1 * g₂) (C.fvec B (C.uVec Lv hn f') (Q j)))) (∫ h in 𝓖, ∑ j, om (h, g₁) (C.fvec B (C.uVec Lv hn f') (Q j)) 0 * conj (om (h, g₂) (C.fvec B (C.uVec Lv hn f') (Q j)) 0) ∂ν)

end GlobalTheory.Ker
