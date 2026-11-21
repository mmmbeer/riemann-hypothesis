import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.LiftDataTimeEqWeightTime

section
noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

open Classical in

def MultIn (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (Z : Comp Xo c)
    (a₁ a' : WZ D.host.E) (B : ℕ) (cc : ℝ) : Prop :=
  ∃ (aτ : WZ D.host.E) (w : CMType H → ℤ) (F : FlatSec U (xiR D) (e Z) (flatZ H w)) (μ m : ℕ) (τ : Rul Xo c)
    (S : Finset ℕ) (ep bτ b cp : ℕ → ℝ) (c₀ ρ A P R₀ cinf : ℝ) (rh : ∀ σ k, Frame ((U σ).X k).Ψ D.R.r → ℝ),
    0 < μ ∧ WEq Dw ((8 * μ) • a₁) ((8 * μ) • a' + (3 * μ) • aτ + m • flatZ H w) ∧ τ ∈ secZ Xo c aτ ∧ evC h Z τ ≠ 0 ∧
    c₀ ≤ 3 * ρ ∧
    (∀ (p : ℕ), p.Prime → ∀ la : HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ la.asIdeal →
      (Ref.pjSys Xo c).RefBound (cuspZ Xo c U a₁) la (ramOverZ la * ep p) c₀ (Ref.phU Xo c la) ∧
      -F.cFin la ≤ ramOverZ la * b p ∧ ∀ y : (Ref.pjSys Xo c).Pt la, 0 ≤ Ref.phU Xo c la y ∧
        ((8 * ρ * Ref.phU Xo c la y - ramOverZ la * bτ p : ℝ) : EReal) ≤ (Ref.pjSys Xo c).val y τ) ∧
    (∀ p ∈ S, p.Prime) ∧ (∀ p, 0 ≤ cp p) ∧ (∀ p, p ∉ S → cp p = 0) ∧
    (∀ p : ℕ, p.Prime → (((8 * μ : ℕ) : ℝ) * (ep p + (if p ≤ B ∨ (p : ℤ) ∣ 2 * discr D.host.E * l.M' then
      1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr D.host.E) : ℝ) / Module.finrank ℚ D.host.E else 0) *
        Top.l1 (towerWt Dw a')) + ((3 * μ : ℕ) : ℝ) * bτ p + m * b p) * Real.log p ≤ ((8 * μ : ℕ) : ℝ) * cp p) ∧
    (∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k →
      ∃ (x0 : Frame ((U σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))),
        IsOrth ((U σ).X k) x0 ∧ IsFundSet ((U σ).X k) x0 FF ∧ ∀ y ∈ ((U σ).X k).dom,
          ThA.BergLB ((U σ).X k) x0 FF (laZ (U σ) a₁ k) y (Real.exp (-(A + 3 * rh σ k y))) ∧
          lieFacZ Dw (xiR D) aτ * ((U σ).X k).pnorm (laZ (U σ) aτ k) (rdU (U σ) τ k) y ≤
            Real.exp (4 * (2 * P - rh σ k y) + R₀)) ∧
    ((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ +
      m * ((∑ σ : c.F →+* ℂ, Real.log (F.cInf σ)) / Module.finrank ℚ c.F) ≤ ((8 * μ : ℕ) : ℝ) * cinf ∧
    ∑ p ∈ S, cp p + cinf ≤ cc

def ShortIn {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] (L : Submodule (𝓞 K) V)
    (ip : (K →+* ℂ) → V → V → ℂ) (Λ : ℝ) : Prop :=
  ∃ (n : ℕ) (ω : Fin n → V), Submodule.span ℤ (Set.range ω) = L.restrictScalars ℤ ∧ ∀ σ j, (ip σ (ω j) (ω j)).re ≤ Λ ^ 2

example {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] (ip : (K →+* ℂ) → V → V → ℂ) (Λ : ℝ) :
    ShortIn (⊥ : Submodule (𝓞 K) V) ip Λ := ⟨0, Fin.elim0, by simp, fun _ j => j.elim0⟩

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section
noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Q : Par D}

variable (P : SlopeBoundParameters) (S : SlopeGeometry.SharpGeo Q (SlopeGeometry.Msh D P)) (i : Fin D.R.m)

variable (D) in

def gapG : ℝ := P.η / P.m / (4 * (SlopeGeometry.Tn D P : ℝ))

variable (D) in

def boundG : ℝ := (SlopeGeometry.pack0 D P i 0 (fun _ : Unit => 0)).B0

structure GeoRows : Prop where
  h0 : D.R.m ^ 4 ≤ D.R.f
  indef : (i : ℕ) + 1 < D.R.m
  primes : (2 * discr D.host.E * S.l.M').natAbs.primeFactors.card ≤ 4 * D.R.f * D.R.r ^ 2
  rd : P.rd = D.host.rdE
  lval : P.Lc = dlogL D 1
  gaps : Top.WeightHyp (SlopeGeometry.pp D i) (SlopeGeometry.upR D P i) (gapG D P)
  reg : ∀ τ, StrictAnti (SlopeGeometry.u1R D P i τ)

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Q : Par D} (P : SlopeBoundParameters) (S : SlopeGeometry.SharpGeo Q (SlopeGeometry.Msh D P)) (i : Fin D.R.m)
  (El : SlopeGeometry.ELocIn P S i) (B : SlopeGeometry.MbarIn P S i) (r4 lmu : ℝ)

variable (D) in

def keyLoss (p : ℕ) : ℝ :=
  4 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 *
    ((padicValInt p (discr D.host.E) : ℝ) / Module.finrank ℚ D.host.E + if p = 2 then 1 else 0)

def GeoTheta (Z : SlopeGeometry.Cmp P S i) : Prop :=
  ∃ (τ : Rul (S.Xo i) S.c) (rh : ∀ σ k, Frame ((S.U i σ).X k).Ψ D.R.r → ℝ),
    τ ∈ secZ (S.Xo i) S.c (fun _ => 4 * (D.R.r : ℤ)) ∧ evC (S.gen i) Z τ ≠ 0 ∧
    (∀ p : ℕ, p.Prime → ∀ la : HeightOneSpectrum (𝓞 S.c.F), (p : 𝓞 S.c.F) ∈ la.asIdeal →
      ∀ y : (Ref.pjSys (S.Xo i) S.c).Pt la,
        ((8 * (1 / 625) * Ref.phU (S.Xo i) S.c la y - ramOverZ la * keyLoss D p : ℝ) : EReal) ≤
          (Ref.pjSys (S.Xo i) S.c).val y τ) ∧
    ∀ σ, GoodEmb S.c σ → ∀ k, Over (S.U i σ) (S.e i Z) k →
      ∃ (x0 : Frame ((S.U i σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((S.U i σ).X k)))),
        IsOrth ((S.U i σ).X k) x0 ∧ IsFundSet ((S.U i σ).X k) x0 FF ∧ ∀ y ∈ ((S.U i σ).X k).dom,
          ThA.BergLB ((S.U i σ).X k) x0 FF (laZ (S.U i σ) (SlopeGeometry.wtZ' D i (SlopeGeometry.u1R D P i)) k) y
            (Real.exp (-((SlopeGeometry.packGeo P S i El B r4 lmu).U1 +
              (SlopeGeometry.lvOf D P i lmu (SlopeGeometry.elocOf P S i El)).PPA (SlopeGeometry.packGeo P S i El B r4 lmu) + 3 * rh σ k y))) ∧
          lieFacZ (Q.Dw ((i : ℕ) + 1)) (xiR D) (fun _ => 4 * (D.R.r : ℤ)) *
              ((S.U i σ).X k).pnorm (laZ (S.U i σ) (fun _ => 4 * (D.R.r : ℤ)) k) (rdU (S.U i σ) τ k) y ≤
            Real.exp (4 * (2 * (SlopeGeometry.lvOf D P i lmu (SlopeGeometry.elocOf P S i El)).Ptau0 (SlopeGeometry.packGeo P S i El B r4 lmu) -
              rh σ k y) + 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.pi))

end GlobalTheory.CompanionTheory.Ar.Rec
end
end
