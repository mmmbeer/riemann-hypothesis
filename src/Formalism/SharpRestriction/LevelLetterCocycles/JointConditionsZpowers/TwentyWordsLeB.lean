import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift

section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Glue

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

def coreB (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
    (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)

end Glue

section Row

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)

abbrev LatW : Type 1 := LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥Cx.LL.1 ↥(OL Cx.LL)

def IsTwistedDualOfGaloisRep (T₂ : LatW i w hw Cx) : Prop :=
  IsMatLat (ρ := T₂.ρ) T₂.L.T ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))

def IsSubOfTwistedDualSums (T₁ : LatW i w hw Cx) : Prop :=
  IsSubOfSums T₁.ρ (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)))

def RowL (x : ℝ) : Prop :=
  ∀ (T₁ T₂ : LatW i w hw Cx) (F : LatHom T₁.L T₂.L), IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ → IsSubOfTwistedDualSums i r w hw Cx T₁ →
    F.Onto → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR (Br.PD D.loc D.nbr i w hw) F x

abbrev nLet : ℕ := finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)

theorem nLet_neZero : NeZero (nLet i w hw) := by
  have := (D.nbr i w hw).Kw.2
  have h0 : K0 (D.nbr i w hw).Kw ≤ (D.nbr i w hw).Kw.1 := inf_le_left
  have : FiniteDimensional ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) :=
    Module.Finite.of_injective (IntermediateField.inclusion h0).toLinearMap
      (IntermediateField.inclusion h0).injective
  exact ⟨(finrank_pos).ne'⟩

end Row

structure WordDat (n : ℕ) where
  b : ℕ
  w : ℕ
  S : ℕ
  η : ℕ
  m : ℕ
  up : ZMod n → Bool
  sz : ZMod n → ℕ
  Mi : ZMod n → ℕ
  hi : ZMod n → ℕ

def WordDat.win {n : ℕ} (Wd : WordDat n) (a : ZMod n) : Set ℤ :=
  if Wd.up a then Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
  else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η

section Word

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

abbrev WW := (HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG

structure WordBase (Wd : WordDat (nLet i w hw)) : Prop where
  unram : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)
  deg : Br.DegW D.nbr i w hw
  split : ∀ _ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    Splits (K := ↥(D.nbr i w hw).Kw.1) (Qp := ℚ_[D.nd.l i]) ↥Cx.LL.1
  dvr : ∃ hO : IsDomain ↥(OL Cx.LL), @IsDiscreteValuationRing ↥(OL Cx.LL) _ hO ∧
    IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1
  t1 : ∀ T₁ : LatW i w hw Cx, IsSubOfTwistedDualSums i r w hw Cx T₁ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₁.ρ ∧
    (∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₁ a (Wd.win a)) ∧
    Formalism.MainNotions.LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₁ Wd.Mi Wd.hi
  t2 : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ ∧
    ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) (a : ZMod (nLet i w hw)),
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount (WW HW i w hw Cx hG) T₂ a Wd.η ≤ Wd.m
  thick_or : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∨ Wd.sz a ≤ Wd.w
  h_le : (Wd.b : ℝ) + Wd.η + Wd.S ≤ Formalism.MainNotions.TwistedPlaces.hB L
  w_le : (Wd.w : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.wP L
  S_le : (Wd.S : ℝ) ≤ L.Sc
  η_le : (Wd.η : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eta₃ L
  m_eq : Wd.m = D.R.m

variable {L HW i r ρ π w hw Cx hG}

structure WordsB (L : SizeData₂ D) (C₂ : ℝ) (l : ℕ) {n : ℕ} (Wd : WordDat n) : Prop where
  j_lt : Formalism.MainNotions.TwistedPlaces.jA L l + 1 ≤ n
  par : C₂ * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) * (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) ≤ Wd.b
  clusters : Formalism.MainNotions.TruncatedSeriesCountingBounds.Clusters (Formalism.MainNotions.TwistedPlaces.jA L l) (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz)

end Word

def ratIn (x y : ℝ) : ℚ := if h : x < y then (exists_rat_btwn h).choose else 0

section RowB

variable (L : SizeData₂ D)

def lenRowB (C₂ : ℝ) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  ratIn (3 * C₂ * coreB L l lam) ((3 * C₂ + 1) * coreB L l lam)

def LocalRepresentationBoundCondition (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBase L HW i r ρ π w hw Cx hG Wd ∧ WordsB L C₂ (D.nd.l i) Wd

end RowB

end Formalism.MainNotions.N

end
end

section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

variable {D : D7}

section Cores

variable (L : SizeData₂ D)

def coreE (l : ℕ) : ℝ := 1 + Formalism.MainNotions.TwistedPlaces.hB L / l + Real.logb l (Formalism.MainNotions.TwistedPlaces.hB L)

def coreH (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (Formalism.MainNotions.TwistedPlaces.hB L / (l : ℝ) ^ 2)

open Classical in
def flat (bd : Prop) (l : ℕ) : ℝ :=
  (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / l + L.Sc + Formalism.MainNotions.TwistedPlaces.large₂ L +
    Formalism.MainNotions.TwistedPlaces.eta₃ L * (if bd then 1 else 0)

def coreF (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  ((Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * flat L bd l

def coreM (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℝ :=
  (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) * D.R.m * coreE L l

def bdCD (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) (K₁ K₂ K₃ : ℝ) : ℝ :=
  K₁ * coreH L l lam + K₂ * coreF L bd l lam + K₃ * coreM L l lam

end Cores

structure WordBox (L : SizeData₂ D) {n : ℕ} (Wd : WordDat n) : Prop where
  box_le : ∀ a, ((Wd.Mi a + Wd.hi a : ℕ) : ℝ) ≤ 2 * Formalism.MainNotions.TwistedPlaces.hB L
  nt : ∀ a, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a →
    ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ Formalism.MainNotions.TwistedPlaces.wB L ∧ |(Wd.sz a : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2
  b_lo : L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ Wd.b
  b_hi : (Wd.b : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1

structure WordsNT {n : ℕ} (Wd : WordDat n) : Prop where
  eta_lt : ∀ a, Wd.η < Wd.sz a
  w20 : 20 * Wd.w ≤ Wd.b
  η20 : 20 * Wd.η ≤ Wd.b
  twenty_words_le_b : 20 * Wd.S ≤ Wd.b
  some_nt : ∃ a, ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a
  alt : ∀ a, Wd.up (a + 1) ≠ Wd.up a ∧
    ¬ (Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∧ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz (a + 1) ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz (a + 2))

structure WordsAT (l : ℕ) {n : ℕ} [NeZero n] (Wd : WordDat n) (d : ℕ) : Prop where
  even : Even n
  typ : ∀ a : ZMod n, Wd.up a = true ↔ (a.val + d) % 2 ≠ 0
  thick : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a
  big1 : ∀ a, 2 * Formalism.MainNotions.RamifiedCoefficientChains.aR l (Formalism.MainNotions.RamifiedCoefficientChains.hpar n Wd.sz Wd.S + Wd.η) + (Wd.η : ℝ) + 1 ≤ (Wd.sz a : ℝ)
  big2 : ∀ a, ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n Wd.sz Wd.S : ℕ) : ℝ) / 2 ≤ (Wd.sz a : ℝ)

section Word2

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

def WordDat.band {n : ℕ} (Wd : WordDat n) (l : ℕ) (CB : ℝ) : Prop :=
  Formalism.MainNotions.TruncatedSeriesCountingBounds.Band l Wd.b Wd.S Wd.η Wd.sz
    (Real.logb l (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℕ) : ℝ))) CB

end Word2

attribute [local instance] nLet_neZero

section Word3

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

variable (ρ π hG) in

structure WordBaseC (Wd : WordDat (nLet i w hw)) : Prop where
  zeta : ∃ ζ : ↥Cx.LL.1, IsPrimitiveRoot ζ (D.nd.l i)
  mult : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    ∀ (a : ZMod (nLet i w hw)) (τ : ↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
      Formalism.MainNotions.LiftingTheory.Over (WW HW i w hw Cx hG) τ a →
      ∑ x ∈ Finset.Icc (-(Wd.η : ℤ)) (Wd.η : ℤ),
        multV ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ τ x ≤ (Wd.m : ℤ)

end Word3

section RowCD

variable (L : SizeData₂ D)

def LocalRepresentationCongruenceCondition (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBase L HW i r ρ π w hw Cx hG Wd ∧ WordBox L Wd ∧
        (WordsNT Wd ∨ (WordBaseC (HW := HW) ρ π hG Wd ∧ ∃ d, WordsAT (D.nd.l i) Wd d))

def bandOf (HW : HWOf D.loc) (CB : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (lam : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  11 ≤ D.nd.l i ∧ ∃ π ∈ D.nd.Zgood i, ∃ (hw : lam ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i lam hw) (hG : Good (D.nbr i lam hw).Kw 1 Cx.LL)
    (Wd : WordDat (nLet i lam hw)), WordBase L HW i r ρ π lam hw Cx hG Wd ∧ WordBox L Wd ∧ WordsNT Wd ∧
      Wd.band (D.nd.l i) CB

def lenRowCD (bd : HeightOneSpectrum (𝓞 D.host.E) → Prop) (K₁ K₂ K₃ : ℝ) (l : ℕ)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  ratIn (bdCD L (bd lam) l lam K₁ K₂ K₃) (bdCD L (bd lam) l lam K₁ (K₂ + 1) K₃)

variable (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowCD

end Formalism.MainNotions.N

end
end
