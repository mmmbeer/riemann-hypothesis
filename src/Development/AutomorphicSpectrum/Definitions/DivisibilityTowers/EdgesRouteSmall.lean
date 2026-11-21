import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HaarOrderData
import Development.WeilBound.CoreStatements.TorusUniformisation.RepresentationHypotheses.HostNumDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.RT

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

variable (G) in

abbrev PolAll : Type := ∀ b : GlobalTheory.SplitFlip.Edge,
  PolF D (G.V (.grid b.src.1 b.src.2)).rank (G.V (.grid b.tgt.1 b.tgt.2)).rank

def IsFockVec (W : G.Weil) (a : Arrow T) (f : Sch G a) : Prop :=
  ∃ f₀ P, IsThetaFunO W.ψ (G.pS a.pair) (G.pT a.pair) f₀ ∧
    (∀ τ, IsFockVacAt (heisO W.ψ (G.pS a.pair) (G.pT a.pair)) W.θ τ
      (cplxO (G.cartS W.cart a.pair τ) (G.onT W.cart a.pair τ)) f₀) ∧ f = W.fock a.pair f₀ P

section Square

variable (W : G.Weil) (B : Frames G) (ρ : RealMatch W)

end Square

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri) in

def FactorZ {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧ ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
    (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
    Nontrivial Pi ∧ Function.Surjective p ∧ Function.Surjective p' ∧ (∀ t, Function.Injective (J t)) ∧
    (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧ (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
    (∀ t P' z h, IntegrableOn (translates z (X.ker' ψ θ t P' h)) X.fd' X.m' →
      ∫ g in X.fd', translates z (X.ker' ψ θ t P' h) g ∂X.m' = zdeg z * J t (p' P') h) ∧
    ∀ t P' h, ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (X.ker' ψ θ t P' h)) X.fd' X.m'

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri) in

def IsStage (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ (D.R.m - (j + 1)) / 2 ∧ q ≤ (D.R.m - j) / 2 ∧
    A.rank + 2 * ((D.R.m - (j + 1)) / 2) = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * ((D.R.m - j) / 2) = rankV D i j + 2 * q ∧
    GlobalTheory.ConstRatio.NegIdx A p ∧ GlobalTheory.ConstRatio.NegIdx A' q ∧ GlobalTheory.ConstRatio.NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (fun t => SqNum.nuH G t i j) (locPl G)

structure Std (W : G.Weil) (μ₀ : T) : Prop where

  lev : L.Is μ₀

  size : GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions.SizeOK D

  host : PositivityTheory.HostN.HostNum D

  cc : D.host.ccK = ⊤

  rk : 2 * D.R.m + 1 < D.R.r

  split : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK

  pdeE : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
    (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

namespace Std

variable {W : G.Weil} {μ₀ : T}

end Std

variable (G) in

def SqField {K : Type} [Field K] (σ : K →+* ℂ) : Prop :=
  CharsIn G σ ∧ RootsIn σ 8 ∧ ∀ t, ∀ w ∈ locPl G t, RootsIn σ (Ideal.absNorm w.asIdeal ^ depthAt G w) ∧
    ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ Set.range σ

section Tower

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

end Tower

end GlobalTheory.CompanionTheory.Ar.RT

end
