import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

noncomputable section

namespace GlobalTheory.Core.Rk.SW

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

def sch (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (f : WO (dblSp A) B → ℂ) : Mx D B.rank A.rank → ℂ := fun x => (dblDec A).mixS B ψ ν 𝓨 f x 0

def gramOf (B : HSp D) {n : ℕ} (x : Mx D B.rank n) : Mx D n n := adj x ⬝ (gA B ⬝ x)

def chr (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ} (T : Mx D n n) (c : skewA D n) : ℂ :=
  ψ (-(trHalf D (Matrix.trace (T ⬝ c.1 : Mx D n n))))

def skewQ (D : D7) (n : ℕ) : AddSubgroup (skewA D n) := (GlobalTheory.MixModel.ratMx D n n).addSubgroupOf (skewA D n)

def IsSkewOne {n : ℕ} (κ : Measure (skewA D n)) (𝓒 : Set (skewA D n)) : Prop :=
  κ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (skewQ D n) 𝓒 κ ∧ κ 𝓒 = 1

section Group

variable (A : HSp D)

def lowC (g : GA D (dblSp A)) : Mx D A.rank A.rank := (dblDec A).pY ⬝ (mt (dblSp A) g ⬝ (dblDec A).jX)

def IsWeyl (w : GA D (dblSp A)) : Prop :=
  w ∈ GQ (dblSp A) ∧ ((dblDec A).pY ⬝ (mt (dblSp A) w ⬝ (dblDec A).jY) : Mx D A.rank A.rank) = 0

variable (ψ : AddChar (AF D.host.F) ℂ) (κ : Measure (skewA D A.rank))

def coef (𝓒 : Set (skewA D A.rank)) (T : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (Φ : GA D (dblSp A) → ℂ)
    (g : GA D (dblSp A)) : ℂ :=
  ∫ c in 𝓒, Φ ((dblDec A).nC c * g) * conj (chr ψ (rat T) c) ∂κ

def whit (w : GA D (dblSp A)) (T : Mx D A.rank A.rank) (Φ : GA D (dblSp A) → ℂ) (g : GA D (dblSp A)) : ℂ :=
  ∫ c, Φ (w * (dblDec A).nC c * g) * conj (chr ψ T c) ∂κ

variable {A} in

def fam {N : ℕ} (c : Fin N → ℂ) (x : Fin N → GA D (dblSp A)) (Φ : GA D (dblSp A) → ℂ) : GA D (dblSp A) → ℂ :=
  fun g => ∑ i, c i * Φ (g * x i)

end Group

structure Dbl (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B)
    (a : GL (Fin A.rank) (AE D)) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)) (mH : Measure (GA D B))
    (κ : Measure (skewA D A.rank)) (𝓒 : Set (skewA D A.rank)) (f : WO (dblSp A) B → ℂ) : Prop where

  pos : 1 ≤ A.rank

  gap : A.rank + 2 ≤ B.rank

  witt : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank

  weil : IsWeilDatumO ψ (dblSp A) B 1 χB omh

  maj : IsMaj A a

  covol : IsCovolOne (ratL B A) ν 𝓨

  haar : mH.IsHaarMeasure

  skew : IsSkewOne κ 𝓒

  theta : IsThetaFunO ψ (dblSp A) B f

  kfin : IsKFinVec omh (Khat A a) f

def sec (A B : HSp D) (omh : WRep (dblSp A) B) (a : GL (Fin A.rank) (AE D)) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (f : WO (dblSp A) B → ℂ) : ℂ → GA D (dblSp A) → ℂ := flat A a (swSec A B omh ν 𝓨 f) (sZero A B)

def ModelLaws (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B),
    IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
  ∀ f, IsThetaFunO ψ (dblSp A) B f →
    (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧
    (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x =
      ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧
    (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧
    HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (rat ξ)) (f 0) ∧
    swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 ∧
    Integrable (sch ψ A B ν 𝓨 f) ν ∧ ∀ w, IsWeyl A w → swSec A B omh ν 𝓨 f w = ∫ x, sch ψ A B ν 𝓨 f x ∂ν

def SchSchwartz (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D)
    (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    (∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ B.rank A.rank) ∧
    (∀ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ B.rank A.rank, ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ sch ψ A B ν 𝓨 f = φ) ∧
    ∀ f f', IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B f' → sch ψ A B ν 𝓨 f = sch ψ A B ν 𝓨 f' → f = f'

def NSAt (par : LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle) (t : ℕ) (q : FinPl D) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = q → ∀ β ∈ par w,
    ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ),
      (β : ℂ) * ((LFun.val (F := D.host.F) χ w : ℂˣ) : ℂ)⁻¹ ≠ LFun.npow w ((k : ℂ) / 2)

structure VacAt (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B)
    (LB : Lat B) (q : FinPl D) (f : WO (dblSp A) B → ℂ) : Prop where

  split : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q

  unr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = q → LFun.UnrAt χB w

  sd : IsSelfDualC B LB

  vac : IsLatVac (heisO ψ (dblSp A) B)
    (latO (dblSp A) B (sumLat finSumFinEquiv (frameLat A) (frameLat A) : Lat (dblSp A)) LB fun u => u = q) f

  fix : ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram (frameLat A) q, omh (emb D.sp.cm.sig (dblSp A).gram q k, 1) f = f

def IsEigAvg (A : HSp D) (L : Lat A) (q : FinPl D) {N : ℕ} (c : Fin N → ℂ) (y : Fin N → Gv A q) (u : GA D A → ℂ)
    (e : ℂ) : Prop :=
  ∀ μ : Measure (Gv A q), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L q) = 1 → ∀ g,
    ∑ i, c i * ∫ k in stabLoc D.sp.cm.sig A.gram L q, u (g * emb D.sp.cm.sig A.gram q (k * (y i)⁻¹)) ∂μ = e * u g

def HeckeFormNS (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → 2 ≤ t → (wittIndex B = 0 ∨ wittIndex B < t) →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ q ∉ Sf, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧ NSAt par χB t q) →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

theorem heckeFormNS_of_heckeForm (h : HeckeForm D) : HeckeFormNS D :=
  fun ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP _ hW LA LB Sf Φ₁ Φ₂ h₁ h₂ hU m mH hm hH u₁ hu₁ u₂ hu₂ par hp hs _ hc =>
    h ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hW LA LB Sf Φ₁ Φ₂ h₁ h₂ hU m mH hm hH u₁ hu₁ u₂ hu₂ par hp hs hc

end GlobalTheory.Core.Rk.SW

end
