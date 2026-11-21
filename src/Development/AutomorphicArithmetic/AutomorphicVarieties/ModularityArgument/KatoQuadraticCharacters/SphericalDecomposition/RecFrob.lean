import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.CuspRep Polynomial
open UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.CuspRep.ParLaws in
private theorem algNorm_diag {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (w.adicCompletion E) → WD h} (L : LawsT a ha rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) n
    ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ (GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB)
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have hx : GlobalTheory.SmGL.HasSatake (IrrGL.of σ.ρ σ.smooth σ.irred).rep α :=
    ⟨(IrrGL.of σ.ρ σ.smooth σ.irred).2.rep.irr, fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hα.2.1,
      (IsSubquotient.of_surjective (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toIntertwiningMap (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toLinearEquiv.surjective).trans hα.2.2⟩
  have e := GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff a ha rc).2 L) (IrrGL.of σ.ρ σ.smooth σ.irred) α hx
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
  change (_ : ℂ) * ((_ : ℂ) * v i) = _ * (_ * v i)
  ring

end UpperTheory.V.Z.Kato.WeilSphericalRecords
