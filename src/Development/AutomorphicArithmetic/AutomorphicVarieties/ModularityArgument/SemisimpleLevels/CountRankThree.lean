import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc UpperTheory.V.Br

namespace UpperTheory.V.Lev

def Safe (l M : ℕ) {n : ℕ} (m : Fin n → ℤ) : Prop := l ∣ M ∨ ∀ i j, m i ≠ m j + 1

def IsAbPol {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (n : ℕ) (x : WD h) : Prop :=
  ∃ μ : Fin n → ↥(Weil h) →* ℂˣ, ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))

structure LevelF {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ κ, FlagAt M m r A κ

theorem LevelF.of_level {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)} (H : Level l M m r) : LevelF l M m r :=
  ⟨H.cont, H.away, fun w hw => by
    obtain ⟨A, hA, χ, κ, h1, h2, h3, -⟩ := H.above w hw
    exact ⟨A, hA, κ, χ, h1, h2, h3⟩⟩

structure AdmPS {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G K Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π
  level : LevelF l M m r
  safe : Safe l M m

def CompatPS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (l : ℕ) [Fact l.Prime]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n),
    Continuous r → (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        IsAbPol n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := K) A).subtype)) →
        ∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := K) A).subtype)).charPol s = (rc (algNorm σ)).charPol s

def FlagPol : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∃ μ : Fin n → ↥(Weil h) →* ℂˣ,
        (∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s = ∏ i, (X - C (μ i s : ℂ))) ∧
        (∀ i (s : ↥(Ine (F := F) A)), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → μ i (ineIncl h s) = 1) ∧
        ∀ i j, (∀ s, (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s) →
          κ i = κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype ∨ κ j = κ i * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def FixedDvd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n M : ℕ), 1 ≤ M →
    ∀ (w : HeightOneSpectrum (𝓞 F)), (M : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
        (rc (algNorm σ)).charPol (ineIncl h s) = (X - 1) ^ n) → HasFixed σ.ρ (KLoc F w n M)

def FixedUnr : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (μ : Fin n → ↥(Weil h) →* ℂˣ), (∀ s, (rc (algNorm σ)).charPol s = ∏ i, (X - C (μ i s : ℂ))) →
    (∀ i (s : ↥(Ine (F := F) A)), μ i (ineIncl h s) = 1) →
    GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ ∧
      ((∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) → GlobalTheory.SmGL.IsSpherical σ.ρ)

def UnlGap : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, FlagAt M m r A κ → (∀ i j, m i ≠ m j + 1) →
      ∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def FixedSs : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      (IsAbPol n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) →
        ∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s = (rc (algNorm σ)).charPol s) →
      (l ∣ M ∨ (∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨
        (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ → GlobalTheory.SmGL.IsSpherical σ.ρ)) →
      HasFixed σ.ρ (KLoc F w n M)

def LevelFRes : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), LevelF l M m r → LevelF l M m (r.comp (res F Ω K))

def LevelPS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), LevelF l M m r → Safe l M m → (CG.mk π).IsRegAlg →
      (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
      π ∈ SigP K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

def CountRankThree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∃ c A : ℕ,
    ∀ e : ℕ, 1 ≤ e → ∀ H : ℕ, (∀ i, |![(e : ℤ) - 1, -1, -(e : ℤ) - 1] i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData 3 (normV w) ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (1 - (3 : ℕ)), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmK ι M ![(e : ℤ) - 1, -1, -(e : ℤ) - 1])

end UpperTheory.V.Lev

end
