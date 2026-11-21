import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.MonodromyFreeOfNoRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwV (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwV.refl (x : WD h) : AwV x x := ⟨fun _ => rfl, fun _ => rfl⟩

theorem charPol_sum (x y : WD h) (g : ↥(Weil h)) : (x.lpSum y).charPol g = x.charPol g * y.charPol g := by
  rw [← WD.inePol_of_mem _ g.2, WD.inePol_sum, WD.inePol_of_mem _ g.2, WD.inePol_of_mem _ g.2]

theorem AwV.sum {x y x' y' : WD h} (k : AwV x y) (k' : AwV x' y') : AwV (x.lpSum x') (y.lpSum y') :=
  ⟨fun g => by rw [charPol_sum, charPol_sum, k.pol, k'.pol],
    fun m => by rw [k.n0 ((WD.monomial_sum_iff _ _).1 m).1, k'.n0 ((WD.monomial_sum_iff _ _).1 m).2]⟩

theorem AwV.tw {x y : WD h} (k : AwV x y) (s : ℝ) : AwV (x.lpTw s) (y.lpTw s) :=
  ⟨fun g => GlobalTheory.GalCut.AwayMono.charPol_lpTw_congr k.pol s g, fun m => by rw [k.n0 ((WD.monomial_twist_iff _ _).1 m)]⟩


variable {l : ℕ} [Fact l.Prime] {n : ℕ}

def WDN (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := ∃ x : WD h, IsWDOf ι r x ∧ AwV x y

variable {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem WDN.of_isWDOf (k : IsWDOf ι r y) : WDN ι r y := ⟨y, k, .refl y⟩
theorem WDN.isWDOf (k : WDN ι r y) (m : y.mono0) : IsWDOf ι r y := by
  obtain ⟨x, hx, k⟩ := k
  exact k.n0 m ▸ hx
theorem WDN.of_unr (k : WDN ι r y) (m : y.unr) : IsWDOf ι r y := k.isWDOf (WD.unr_mono0 _ m)
theorem WDN.of_hasSat {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {a : ℕ}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (k : WDN ι r (rc (algNorm σ))) {S : Multiset ℂˣ}
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := k.of_unr (unr_algNorm hrc σ S hS)
theorem WDN.of_conj (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : WDN ι r' y := by
  obtain ⟨x, hx, k⟩ := k
  exact ⟨x, hx.of_conj hl P hP, k⟩
theorem WDN.awV (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : AwV (wdOf h hl ι r) y := by
  obtain ⟨x, hx, k⟩ := k
  rwa [hx.wdOf_eq hl]
end Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def CsdSsN : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            Lev.SsCmp (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

def CsdMonoOddN : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → Odd a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)).mono0 → (rc (algNorm σ)).mono0

def CarV : Prop := CarU ∧ CsdSsN ∧ CsdMonoOddN

end UpperTheory.GalN.V
