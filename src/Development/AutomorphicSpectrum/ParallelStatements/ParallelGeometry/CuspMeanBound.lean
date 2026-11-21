import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

def corrWeight (U : ((Σ k, J k) → ℂ) → ℝ) (z : (Σ k, J k) → ℂ) : ℝ := phMu Hd z + U z / 2

def meanOf (U : ((Σ k, J k) → ℂ) → ℝ) : ℝ :=
  ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U / degMu Hd

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

def HtLower (Ch rd Lval : ℝ) (pt : Ideal (MRing J) → Prop) : Prop :=
  ∀ B p q : ℕ, 4 * Dc.f * Dc.N ^ 2 ≤ B → 0 < p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ),
    ∀ Q : Ideal (MRing J), IsArithVar Q 1 → mCoordIdeal Dc.y ≤ Q → pt Q →
      -(Ch * Dc.f * Dc.j' * abelian₂ B rd Lval) - (p : ℝ) / q * Dc.KA ≤ htMUc Hd S B p q t' Q

def HtInterior (Ch rd Lval : ℝ) : Prop := HtLower Hd S Ch rd Lval fun Q => ∀ z ∈ mcPts Q, z ∉ Dc.Bd

def HtBoundary (Ch rd Lval : ℝ) : Prop := HtLower Hd S Ch rd Lval fun Q => ∃ z ∈ mcPts Q, z ∈ Dc.Bd

end Clauses

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound
