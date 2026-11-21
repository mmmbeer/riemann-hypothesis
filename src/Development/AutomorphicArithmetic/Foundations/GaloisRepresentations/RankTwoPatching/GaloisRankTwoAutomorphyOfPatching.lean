import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealPatch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.UnrAtOfIsoTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.WinPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
open private UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr

namespace UpperTheory.Gal.SV

theorem props_iso {Rc : UpperTheory.GalStar.RecNotion} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {m : ℕ}
    [NumberField E] [IsAlgClosure E Ω] [IsCMField E] {π : CuspSub E m}
    {ι : Qbar l ≃+* ℂ} {r r' : G E Ω →* GL (Fin m) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalStar.PropsB Rc π ι r wt HT) (hs : IsSSRep r') (h : RepIso r r') :
    UpperTheory.GalStar.PropsB Rc π ι r' wt HT := by
  have hc := continuous_of_iso H.cont h
  obtain ⟨g, hg⟩ := h
  have hg' : ∀ s, g * r s = r' s * g := fun s => by rw [hg, inv_mul_cancel_right]
  have ew : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      wdOf h hw ι r' = wdOf h hw ι r := fun w hw A h =>
    ((isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)).of_conj hw g fun s => hg' _).wdOf_eq hw
  refine ⟨hc, hs, fun w hw A h rc hrc σ hσ => ew w hw A h ▸ H.away w hw A h rc hrc σ hσ, H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj => ?_⟩
  have Ha := H.above P AI T w A h O Bw hj
  have e : ∀ s : ↥(Dec (F := E) A), r'.comp (Dec (F := E) A).subtype s = g * r.comp (Dec (F := E) A).subtype s * g⁻¹ :=
    fun s => hg s
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e
  refine ⟨fun σ hσ hf => ?_, fun σ hσ rc hrc h1 h2 => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := Ha.crys σ hσ hf
    exact ⟨c2 a1, c1 a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := Ha.nice σ hσ rc hrc h1 h2
    exact ⟨c1 a1, isPstAt_conj P Bw g e a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ), wdAt_conj P ι Bw h hj g e ▸ a4⟩


theorem hodgeTate : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a), π.IsRegAlg → ∃ HTF : (F →+* Qbar l) → Multiset ℤ, (∀ τ, (HTF τ).card = a) ∧ (∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m → (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z) ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → (∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) ∧ ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt - ·) := by
  intro F Ω _ _ _ _ _ _ l _ ι a π hπ
  choose HTF hHTF using fun τ : F →+* Qbar l => exists_hodgeTate π hπ (InfinitePlace.mk (ι.toRingHom.comp τ))
  have key : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
      (HTF τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
    intro τ m hm
    obtain ⟨m0, hm0, e⟩ := hHTF τ
    rw [e, TR.CuspSub.HasInfChar.unique hm0 hm]
  refine ⟨HTF, fun τ => ?_, key, ?_⟩
  · obtain ⟨m0, hm0, e⟩ := hHTF τ
    have := congrArg Multiset.card e
    simpa [hm0.1] using this
  · intro K _ _ _ _ _ _ _ h2 P hBC r wt HT hG
    have hK : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K)) := by
      intro τ
      obtain ⟨m0, hm0, e⟩ := hHTF (τ.comp (algebraMap F K))
      have h1 : P.HasInfChar (ι.toRingHom.comp τ) m0 := hBC.inf _ _ hm0
      have h3 : (CG.mk P).infChar (ι.toRingHom.comp τ) = m0 := CG.HasInfChar.infChar_eq h1
      apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
      rw [hG.weights τ, h3, e]
    refine ⟨hK, fun τ => ?_⟩
    letI : Algebra F (Qbar l) := τ.toAlgebra
    haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
    haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
    let τ' : K →ₐ[F] Qbar l := IsAlgClosed.lift
    have hτ' : (τ' : K →+* Qbar l).comp (algebraMap F K) = τ := RingHom.ext fun x => τ'.commutes x
    have hc : ((τ' : K →+* Qbar l).comp (IsCMField.complexConj K).toRingEquiv.toRingHom).comp (algebraMap F K) = τ := by
      rw [← hτ']
      ext x
      simp only [RingHom.comp_apply]
      exact congrArg τ' (complexConj_algebraMap (K := K) x)
    have := hG.weights_conj (τ' : K →+* Qbar l)
    rw [hK, hK, hc, hτ'] at this
    exact this

section Descent

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure At (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin a) (Qbar l)) (HT : (F →+* Qbar l) → Multiset ℤ)
    {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A v) : Prop where
  plain : ∀ B, π.HasSat v B → PlainAtR π v
  cmp : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ rc : IrrGL (v.adicCompletion F) → WD h, IsRecT h rc → CmpT ι r (rc (algNorm σ))
  ht : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      IsdRAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
      ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ (HT τ)
  ratio : ∀ hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal, PlainAtR π v → UpperTheory.GalN.V.RatioW (wdOf h hl ι r)
  crys : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
    ∀ σ, π.IsLocComp v σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)

end Descent

end UpperTheory.Gal.SV
