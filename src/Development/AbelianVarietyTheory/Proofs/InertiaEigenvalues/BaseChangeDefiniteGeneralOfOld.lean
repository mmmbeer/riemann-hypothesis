import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasSatakeOfUnrT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspReadGIffCuspReadT

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCSupport

variable {E : Type} [Field E] [NumberField E]

abbrev clsOf {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

theorem good_of_good_locProd {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (hi : (locProd h w σ).IsIrreducible)
    (hG : Good (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi)) : ∀ i, Good (clsOf (σ i)) := by
  have hs : IsSubquotient (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi).rep
      (prodIrr (fun i => clsOf (σ i)) h) := by
    let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
    let f := e.symm.trans (IrrGL.equivOf (locProd h w σ) (isSmooth_parInd _ _) hi)
    exact IsSubquotient.of_surjective f.toIntertwiningMap f.toLinearEquiv.surjective
  exact (GlobalTheory.RecT.good_toral_of_isSubquotient_prodIrr _ c (fun i => clsOf (σ i)) (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi) h hs).1 hG

theorem isSpherical_of_equiv {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (e : ρ.Equiv τ) {K : Subgroup G}
    (h : GlobalTheory.LGrp.IsSpherical ρ K) : GlobalTheory.LGrp.IsSpherical τ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, ?_⟩
  · rw [← Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap k x, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h1
    exact h0 (e.toLinearEquiv.injective (by simpa using h1))

theorem isSphericalFor_of_eq {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K K' : Subgroup G} (e : K = K') (h : GlobalTheory.SmGL.IsSphericalFor ρ K) : GlobalTheory.SmGL.IsSphericalFor ρ K' := e ▸ h

variable [IsCMField E]

end GlobalTheory.BCSupport
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC GlobalTheory.RecT

namespace GlobalTheory.DefiniteBCGood

section Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL

variable {E : Type} [Field E] [NumberField E]

theorem good_of_isSpehQuot {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hd : 1 ≤ d) (hq : IsSpehQuot h σ σ') (hG : Good (GlobalTheory.BCSupport.clsOf σ')) :
    Good (GlobalTheory.BCSupport.clsOf σ) := by
  obtain ⟨q, hq⟩ := hq
  let x := IrrGL.of σ.ρ σ.smooth σ.irred
  let T : ∀ i : Fin d, (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor x d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  have hA : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep σ'.ρ :=
    IsSubquotient.of_surjective (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toIntertwiningMap
      (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toLinearEquiv.surjective
  have hB : IsSubquotient σ'.ρ (spehInd h σ) := IsSubquotient.of_surjective q hq
  have hC : IsSubquotient (spehInd h σ) (prodIrr (spehFactor x d) h) :=
    IsSubquotient.of_surjective M.symm.toIntertwiningMap M.symm.toLinearEquiv.surjective
  have hs : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep (prodIrr (spehFactor x d) h) := hA.trans (hB.trans hC)
  have h0 := (good_toral_of_isSubquotient_prodIrr _ d (spehFactor x d) (GlobalTheory.BCSupport.clsOf σ') h hs).1 hG ⟨0, hd⟩
  exact (good_nu_iff x _).1 h0

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

attribute [local instance] host_isCMField

section Statements

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {A : NAut N}

def GoodSplitU {n : ℕ} (U : Submodule ℂ (UA H.E n → ℂ)) : Prop :=
  ∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w n,
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → Good (GlobalTheory.BCSupport.clsOf σ)

end Statements

section Proof

variable {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Proof

section Frozen

open Formalism.MainNotions

end Frozen

section LawsCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (w.adicCompletion E) → WD h}

end LawsCore

section LawsSpeh

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.NuShift

end LawsSpeh

section SatCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (w.adicCompletion E) → WD h}

end SatCore

section RecordLaws

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
  {rec : ∀ w : PlE H, IrrGL (w.adicCompletion H.E) → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)}

open GlobalTheory.RecLaws GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end RecordLaws

section Top

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end Top

section RecordLawsFam

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SmGL GlobalTheory.LocLanglands GlobalTheory.RecLaws

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A) {rc : GlobalTheory.RecT.RecFam}

end RecordLawsFam

end GlobalTheory.DefiniteBCGood

end
end
