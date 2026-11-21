import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def PhiAt (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hBw : Pst.Induces Bw),
    ∀ (σ : Weil hA) (n : ℕ), GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (r.comp (Dec (F := E) A).subtype)) σ n =
      GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n

def HasLevelOff (w₀ v' : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥

open Classical in

def PowSatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (n : ℤ) : ℂ :=
  if h : ∃ B, SatU U w B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (fun z => z ^ n)).sum else 0

end GlobalTheory.CongL

end
