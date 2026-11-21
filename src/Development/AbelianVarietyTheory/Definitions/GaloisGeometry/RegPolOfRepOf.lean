import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

structure Base : Prop where
  llc : GlobalTheory.Published.LocalLanglandsGL
  ex : GlobalTheory.Published.LocalLanglandsExists
  conv : GlobalTheory.Published.LocalConverseGL
  adm : GlobalTheory.Published.IrreducibleAdmissibleGL
  len : GlobalTheory.Published.StandardFunctorsFiniteLength
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  js : GlobalTheory.Published.JacquetShalikaRigidity
  gk : GlobalTheory.Published.GelfandKazhdanDual

theorem Base.uniq (H : Base) : GlobalTheory.TheRec.RecUnique :=
  GlobalTheory.TheRec.recUnique_of_localConverse H.ex H.conv H.exh H.adm H.len

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SatMatch (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, sat w B ∧
    ∀ (_hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      IsWDOf ι r ((WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2))

theorem SatMatch.wdOf_eq {sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} (H : SatMatch sat ι r) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, sat w B ∧
      ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        wdOf h hl ι r = (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2) :=
  H.mono fun _ ⟨B, hB, hw⟩ => ⟨B, hB, fun hl A h => (hw hl A h).wdOf_eq hl⟩

def IsSumOf {Γ k : Type} [Group Γ] [Field k] {a m : ℕ} {b : Fin m → ℕ} (r : Γ →* GL (Fin a) k)
    (ρ : ∀ i, Γ →* GL (Fin (b i)) k) : Prop :=
  ∀ g, (r g).val.trace = ∑ i, (ρ i g).val.trace

example {Γ k : Type} [Group Γ] [Field k] {a : ℕ} {b : Fin 2 → ℕ} (r : Γ →* GL (Fin a) k)
    (ρ : ∀ i, Γ →* GL (Fin (b i)) k) (H : IsSumOf r ρ) (g : Γ) :
    (r g).val.trace = (ρ 0 g).val.trace + (ρ 1 g).val.trace := by
  have := H g; rwa [Fin.sum_univ_two] at this

example (H : Base) : GlobalTheory.TheRec.RecUnique := H.uniq

end GlobalTheory.AboveL

end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

section Local

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (Polynomial.X - 1) ^ x.lpDim

structure Near (x y : WD h) : Prop where
  mono : x.mono0 ↔ y.mono0
  size : ∀ σ : Weil h, (x.eig σ).map (fun z => ‖z‖) = (y.eig σ).map (fun z => ‖z‖)
  eq : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IneTriv (y.lpTwist χ hχ) → x = y
  tame : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IsTameWD (y.lpTwist χ hχ) →
    ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = y.charPol (ineIncl h τ)

theorem Near.refl (x : WD h) : Near x x := ⟨Iff.rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Near.of_eq {x y : WD h} (e : x = y) : Near x y := e ▸ Near.refl x

theorem Near.lpDim_eq {x y : WD h} (n : Near x y) : x.lpDim = y.lpDim := by
  have := congrArg Multiset.card (n.size 1)
  simpa only [Multiset.card_map, WD.card_eig] using this

example : ¬ Near (WD.lpZero h) (WD.lpSp h 1) := fun n => by
  have := n.lpDim_eq
  rw [WD.lpDim_lpSp, WD.lpZero, WD.lpDim_mk] at this
  simp at this

end Local

def SolvDisj {K Ω : Type} (M : Type) [Field K] [Field M] [Field Ω] [Algebra K Ω] [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω]
    (N : Subgroup (G K Ω)) : Prop :=
  IsGalois K M ∧ IsSolvable (M ≃ₐ[K] M) ∧
    ∀ g : G K Ω, ∃ (x : G M Ω) (n : G K Ω), n ∈ N ∧ g = AlgEquiv.restrictScalarsHom K x * n

def BCof (Ω : Type) {K M : Type} [Field Ω] [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] {a : ℕ}
    (π : CuspSub K a) (π' : CuspSub M a) : Prop :=
  RegPol π ∧ RegPol π' ∧
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin a) (Qbar l)), RepOf π ι r → RepOf π' ι (resTo M r)

section API

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

variable {K M : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] {a : ℕ}

theorem BCof.repOf {π : CuspSub K a} {π' : CuspSub M a} (hb : BCof Ω π π') {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r : G K Ω →* GL (Fin a) (Qbar l)} (hr : RepOf π ι r) : RepOf π' ι (resTo M r) := hb.2.2 l ι r hr

end API

end GlobalTheory.AboveL

end
end
