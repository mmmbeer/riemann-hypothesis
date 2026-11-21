import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
import Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def GenAt (D : MvPolynomial (Fin a) ℤ) (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ →
    ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B →
      MvPolynomial.aeval (fun i => (α i : ℂ)) D ≠ 0

example (p : ℕ) [Fact p.Prime] : PolyApprox (fun _ : Unit => (0 : ℚ_[p]))
    {ϑ | MvPolynomial.aeval ϑ (MvPolynomial.X () : MvPolynomial Unit ℤ) ≠ 0} :=
  (polyApprox_zero_padic p).1.mono fun ϑ ⟨n, hn⟩ => by
    simpa [hn] using (Fact.out : p.Prime).ne_zero

end GlobalTheory.CongW
