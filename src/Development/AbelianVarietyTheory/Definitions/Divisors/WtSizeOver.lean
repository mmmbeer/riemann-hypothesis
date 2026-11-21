import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenTyL
import Development.AbelianVarietyTheory.Definitions.Divisors.OverPair

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

open Classical in

def wtSizeOver (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (u : HeightOneSpectrum (𝓞 E)) : ℕ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => OverPair ι u τ), ∑ k : Fin a, ((lam τ).w k).natAbs

end GlobalTheory.CongW

end
