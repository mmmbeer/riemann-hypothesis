import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

open scoped ComplexOrder

namespace GlobalTheory.HSCore

section Lattice

variable {K : Type} [Field K] [NumberField K]

def diagHerm {κ : Type} [Fintype κ] [DecidableEq κ] (c : (K →+* ℂ) → κ → ℝ) (hc : ∀ σ p, 0 < c σ p) : HermFam K (κ → K) :=
  ofGram (Pi.basisFun K κ) (fun σ => Matrix.diagonal fun p => (((c σ p)⁻¹ ^ 2 : ℝ) : ℂ))
    fun σ => Matrix.PosDef.diagonal fun p => Complex.zero_lt_real.2 (pow_pos (inv_pos.2 (hc σ p)) 2)

def vecHt {n : ℕ} (a : Fin n → K) (c : (K →+* ℂ) → ℝ) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (a k))) + ∑ τ : K →+* ℂ, Real.log (c τ)) / (Module.finrank ℚ K : ℝ)

end Lattice

section Geometry

variable {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K)

def filV (a : ℕ) : Submodule K (X.V X.T) := (Fil (X.ideal s) a (spaceV X s)).comap (X.V X.T).subtype

variable {X s}

def symV {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) :
    filV X s a →ₗ[K] (MonoDeg (Fin X.D) a × Fin δ → K) :=
  if h : a ≤ X.T then
    (LinearMap.pi fun q : MonoDeg (Fin X.D) a × Fin δ =>
      (LinearMap.proj q.2 : (Fin δ → K) →ₗ[K] K) ∘ₗ (Co.ev (X.T - a)).toLinearMap ∘ₗ LinearMap.proj q.1) ∘ₗ
      hs.sym (Nat.sub_add_cancel h) (spaceV X s) ∘ₗ (X.V X.T).subtype.restrict fun _ hx => hx
  else 0

def Coord.gen {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (k : Fin G.n) (p : Fin δ) : K :=
  ∑ j, G.w j k * Co.y p j

def Coord.c₁ {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (σ : K →+* ℂ) (p : Fin δ) : ℝ :=
  archSize (G.A σ) fun k => σ (Co.y p k)

variable (X) in

structure Stable : Prop where
  nef : IsNef K X.LA
  big : IsBig K X.LA
  mulStable : X.MulStable
  mulBound : ∀ σ, X.MulBoundAt σ X.beta
  integralBound : X.IntegralBound (fun _ => X.beta) fun _ => 1
  shortD : X.ShortFamily X.D X.LamD
  shortT : X.ShortFamily X.T X.LamT

end Geometry

def RegSeq {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : List L.Sec) : Prop :=
  List.rec (motive := fun _ => Y.Modules → Prop) (fun _ => True)
    (fun a _ ih G => Mono (GlobalTheory.cutHom G hL a) ∧ ih (GlobalTheory.cut G hL a)) t F

theorem regSeq_cons {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (a : L.Sec) (r : List L.Sec) :
    RegSeq hL F (a :: r) ↔ Mono (GlobalTheory.cutHom F hL a) ∧ RegSeq hL (GlobalTheory.cut F hL a) r := Iff.rfl

def VanishFrom {Y : Scheme.{0}} (L : LB Y) (F : Y.Modules) (j₀ : ℤ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ q : ℕ, 0 < q → Subsingleton (coh (GlobalTheory.twistZ F L j) q)

example {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) : RegSeq hL F [] := trivial

end GlobalTheory.HSCore
