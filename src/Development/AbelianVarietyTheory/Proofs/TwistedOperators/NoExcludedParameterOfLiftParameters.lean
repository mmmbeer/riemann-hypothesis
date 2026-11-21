import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSphericalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData

section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LFun.HeckeScalar

namespace GlobalTheory.LFun.IsoBound

section General

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Representation ℂ G H}
  {K : Subgroup G} {x : H}

def gen (hx : x ∈ fixed ρ K) : Representation ℂ G (LinearMap.range (orbitMap ρ K x)) :=
  sub ρ _ (by
    rintro g _ ⟨φ, rfl⟩
    exact ⟨_, orbitMap_permRep hx g φ⟩)

end General

end GlobalTheory.LFun.IsoBound

end
end

section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) (SelfDual.isLattice_frameLat V).span_eq_top h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

def funsOf (σ : Submodule ℂ (DividedPowerChartLift V ν)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | ∃ h : MemL2Quotient (GQ V) ν F, h.toL2 ∈ σ}
  zero_mem' := ⟨⟨fun _ _ _ => rfl, MemLp.zero⟩, by
    convert σ.zero_mem using 1
    exact MemLp.toLp_zero _⟩
  add_mem' := fun ⟨h, e⟩ ⟨h', e'⟩ => ⟨⟨fun γ hγ g => congrArg₂ (· + ·) (h.1 γ hγ g) (h'.1 γ hγ g), h.2.add h'.2⟩,
    σ.add_mem e e'⟩
  smul_mem' := fun c _ ⟨h, e⟩ => ⟨⟨fun γ hγ g => congrArg (c • ·) (h.1 γ hγ g), h.2.const_smul c⟩, σ.smul_mem c e⟩

end Zero

end GlobalTheory.NoExcl

end
end
