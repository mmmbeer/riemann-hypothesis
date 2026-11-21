import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.CuspMeanBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights.LowerBoundFree (AmpleOnGenericFibre)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Field

variable {F : Type} [Field F]

def EffOn (V : Ideal (MRingOver F ι)) (β : K → ℤ) : Prop :=
  ∀ W : Ideal (MRingOver F ι), IsMultiProjPrime W → V ≤ W →
    ∃ f g, IsRatSection W β f g ∧ ∀ W', 0 ≤ ratDiv W f g W'

end Field

variable {Ω : Type} [Field Ω]

open Classical in

abbrev numQ : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L

theorem geomDeg_eq (hD : DegreeStatement) {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1))
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) : geomDeg W A d = genDeg W d A.a := by
  classical
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hD K ι W d (fun _ => A) hW (fun _ => hA)
  have hpot : pot (fun _ : Fin d => A) = fun (_ : Fin d) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

section Values

variable {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L} {c : ∀ k, ι k}

def ChartVal (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (s : Ω) (v : L) : Prop :=
  ∃ (e : K → ℕ) (G : MRing ι), IsMultiHomog G e ∧ aeval y G = s * aeval y (GenOnFibres.cmon c e) ∧
    aeval z G = v * aeval z (GenOnFibres.cmon c e)

theorem ChartVal.add {s s' : Ω} {v v' : L} (h : ChartVal y z c s v) (h' : ChartVal y z c s' v') :
    ChartVal y z c (s + s') (v + v') := by
  obtain ⟨e, G, hG, h1, h2⟩ := h
  obtain ⟨e', G', hG', h1', h2'⟩ := h'
  refine ⟨e + e', G * GenOnFibres.cmon c e' + GenOnFibres.cmon c e * G',
    GenOnFibres.homog_add (GenOnFibres.homog_mul hG (GenOnFibres.homog_cmon c e'))
      (GenOnFibres.homog_mul (GenOnFibres.homog_cmon c e) hG'), ?_, ?_⟩
  · simp only [GenOnFibres.cmon_add, map_add, map_mul, h1, h1']; ring
  · simp only [GenOnFibres.cmon_add, map_add, map_mul, h2, h2']; ring

theorem ChartVal.mul {s s' : Ω} {v v' : L} (h : ChartVal y z c s v) (h' : ChartVal y z c s' v') :
    ChartVal y z c (s * s') (v * v') := by
  obtain ⟨e, G, hG, h1, h2⟩ := h
  obtain ⟨e', G', hG', h1', h2'⟩ := h'
  refine ⟨e + e', G * G', GenOnFibres.homog_mul hG hG', ?_, ?_⟩
  · simp only [GenOnFibres.cmon_add, map_mul, h1, h1']; ring
  · simp only [GenOnFibres.cmon_add, map_mul, h2, h2']; ring

end Values

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.CuspMeanBound

section Systems

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end Systems

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

end Clauses

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq
end
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem nefCount : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  intro hRR hG II _ K _ ι _ Ω _ _ y D A _ hX hB hA hnef
  obtain ⟨-, -, -, -, -, -, -, -, -, hPB, -⟩ := hG
  obtain ⟨-, ⟨-, hD, -⟩, -⟩ := hPB
  have hN : GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericDeg (mCoordIdeal y) A.a := by
    intro W hW hle
    have h := hnef W hW hle
    rw [GlobalTheory.CompanionTheory.Ar.Cusp.NineEq.geomDeg_eq hD (d := 1) hW hA] at h
    exact_mod_cast h
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.NineEq.geomDeg_eq hD hX hA
  rw [e]
  exact hRR K ι Ω y D A.a hX hB hN

end GlobalTheory.CompanionTheory.Ar.Plug
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_count_tendsto_geomDeg : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Plug.nefCount
end
