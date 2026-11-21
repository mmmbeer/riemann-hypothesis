import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem wn (k : Lev.WO ι r y) : WDN ι r y := .of_isWDOf k
theorem woOf (k : IsWDOf ι r y) : Lev.WO ι r y := k



theorem satFrobW (P : Hypotheses₂) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hc : Continuous r) (w : HeightOneSpectrum (𝓞 F))
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ)
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (H : ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
      Lev.WO ι r (rc (algNorm σ))) : FrobEig ι r w (algSat n (normV w) B) :=
  satFrob P F Ω l ι n r hc w hw σ B hB fun A h rc hrc => (wn (H A h rc hrc)).of_hasSat hrc hB

end UpperTheory.GalN.V
