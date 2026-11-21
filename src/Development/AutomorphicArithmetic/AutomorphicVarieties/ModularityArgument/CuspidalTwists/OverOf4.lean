import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.DefsBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.TnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu

def AutOff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω)
    (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) : Prop :=
  ∀ (L : IntermediateField ℚ Ω) [NumberField L] [IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L →
    IsIrr (R.comp (resQ L)) → IsAutC ι (R.comp (resQ L))

def AutomorphyRankFour : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ → IrrOpen ρ →
    ∀ (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), g0 ∉ K'.fixingSubgroup →
    (∃ τ s, TauDat ι K' g0 (m * 1) c₁ τ s (κ ^ 1)) →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 9 ∧ ∀ (ρ₁ τ : G ℚ Ω →* M2 c₁.O) s, RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits →
      TauDat ι K' g0 (m * j) c₁ τ s (κ ^ j) → AutOff ι K' (tenB ρ₁ τ)

end UpperTheory.V.Cu

end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu

def BadOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' L M : IntermediateField ℚ Ω)
    [NumberField L] [NumberField M] [IsCMField M] [Algebra L M] [IsScalarTower L M Ω] [IsAlgClosure M Ω] [IsGalois L M], M = K' ⊔ L →
    ∀ (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (r : G M Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub M 2), GoodAt K' L ρ → Continuous r → Af.Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := M) A, ρ (resQ M s) = 1 → r s = 1) → Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L π

def AutOffS {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) : Prop :=
  ∀ (L : IntermediateField ℚ Ω) [NumberField L] [IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
    IsIrr (R.comp (resQ L)) → IsAutC ι (R.comp (resQ L))

def AutomorphyRankFourPolarized : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ → IrrOpen ρ →
    ∀ (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), g0 ∉ K'.fixingSubgroup →
    (∃ τ s, TauDat ι K' g0 (m * 1) c₁ τ s (κ ^ 1)) →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 9 ∧ ∀ (ρ₁ τ : G ℚ Ω →* M2 c₁.O) s, RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits →
      TauDat ι K' g0 (m * j) c₁ τ s (κ ^ j) → AutOffS ι K' ρ (tenB ρ₁ τ)

theorem AutomorphyRankFour.s (h : AutomorphyRankFour) : AutomorphyRankFourPolarized := fun Ω _ _ _ l _ ι K' _ h2 hc ρ a b c g0 m c₁ κ d e =>
  let ⟨j, j1, j9, hj⟩ := h Ω l ι K' h2 hc ρ a b c g0 m c₁ κ d e
  ⟨j, j1, j9, fun ρ₁ τ s x y L _ _ u v _ => hj ρ₁ τ s x y L u v⟩

end UpperTheory.V.Cu

end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

structure Dat (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] where
  ι : Qbar l ≃+* ℂ
  c : Coef l
  D : Raw Ω c
  T₀ : Tower D
  ctx : Ctx3 D
  ok : T₀.Ok
  K' : IntermediateField ℚ Ω
  [nK : NumberField K']
  quad : QuadOn T₀ K'
  k : ℕ
  m : ℕ
  big : 2 * m + 3 ≤ k
  cong : k - 1 ≡ D.e [MOD l - 1]
  δ : G ℚ Ω →* c.Oˣ
  tw : Tw4 T₀ k δ
  θ : G ℚ Ω →* (Qbar l)ˣ
  ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)
  eis : EisRep ι (toB (phi D T₀.pr)) θ k ρ
  irr : IrrOpen ρ
  c₁ : Coef l
  h : c.O ≤ c₁.O
  ρ₁ : G ℚ Ω →* M2 c₁.O
  x : ValuationSubring Ω → c₁.O
  mod : Mod4 D T₀.pr θ k (resQ T₀.F T₀.g0) ρ h ρ₁ x
  τ : G ℚ Ω →* M2 c₁.O
  s : ValuationSubring Ω → c₁.O
  κ : G K' Ω →* (Qbar l)ˣ
  tau : TauDat ι K' (resQ T₀.F T₀.g0) m c₁ τ s κ
  aut : AutOffS ι K' ρ (tenB ρ₁ τ)
  w : ℕ
  wp : w.Prime
  wsp : T₀.Splits w
  wunr : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker

attribute [instance] Dat.nK

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

def Dat.Q (d : Dat Ω l) (T : Tower d.D) : PD T.ι (G T.F Ω) d.c₁.O :=
  ⟨(rep4 (toC d.h d.δ) d.ρ₁ d.τ).comp (resQ T.F), fun v => flg (d.x (T.pl v)) (d.s (T.pl v))⟩

def TwEx4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D), Ctx3 D →
    ∀ k : ℕ, 1 ≤ k → k - 1 ≡ D.e [MOD l - 1] → ∃ δ, Tw4 T₀ k δ

def PairOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → ∀ (W : Finset ℕ) (R : Type) [CommRing R] (f : d.c₁.O →+* R),
    (∀ g ∈ T.F.fixingSubgroup, f (d.ρ₁ g).det = f (inc d.h (Phi d.D d.T₀.pr d.k g))) →
    (∀ A, Raw.Away (insert l W) A → ∀ g ∈ Ine (F := T.F) A, d.θ (resQ T.F g) = 1) →
    (T.fr W).IsPair (f.comp (inc d.h)) ((d.Q T).map f)

def ResOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → ∀ (W : Finset ℕ) (R : Type) [Field R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
    (T.fr W).Res (f.comp (inc d.h)) ((d.Q T).map f) ∧ Supp nM ((d.Q T).map f).r ∧ InA ((d.Q T).map f) ∧
      ∀ g, f (d.ρ₁ g).det = f (inc d.h (Phi d.D d.T₀.pr d.k g))

def ContOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), (d.Q T).Cont (maximalIdeal d.c₁.O) ∧
    ∀ (R : Type) [CommRing R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) → ((d.Q T).map f).Cont ⊥

def EntOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → ∀ (R : Type) [Field R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
    Ent ((d.Q T).map f).r (-wBe) ∧ Ent ((d.Q T).map f).r (-wTh)

def OverOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D) (hT : d.T₀.Le T) (R : Type) [Field R] (f : d.c₁.O →+* R), (∀ y ∈ maximalIdeal d.c₁.O, f y = 0) →
    d.T₀.OverT hT ((d.Q d.T₀).map f) ((d.Q T).map f)

def WtsOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D) (U : Subgroup (G ℚ Ω)) (j : ℤ), IsOpen (U : Set (G ℚ Ω)) → (∀ g ∈ U, d.δ g ^ 2 = chiO ℚ Ω l d.c.O g ^ j) →
    T.Wts (fun i => j + 2 * ![(d.k : ℤ) - 1 + d.m, (d.k : ℤ) - 1 - d.m, d.m, -(d.m : ℤ)] i)
      ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l)))

def AlNe : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → ∃ g ∈ T.G', resQ T.F g ∉ d.K'.fixingSubgroup

def IrrOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → Irr (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp T.G'.subtype)

def AutOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok →
    Irr (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp T.G'.subtype) →
    ∃ π : CuspSub T.L 4, (CG.mk π).IsRegAlg ∧ AttC d.ι (Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp
      (resLe T.F_le)).toHomUnits ((toB d.δ).comp (resQ T.L))⁻¹) π

end UpperTheory.V.Cu

end
end
