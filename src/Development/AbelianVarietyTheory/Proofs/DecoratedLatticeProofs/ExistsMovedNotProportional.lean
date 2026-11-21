import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GlobalLocalFactorization
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

def sph (α : kˣ) (n'' n' n : Type) [Fintype n''] [Fintype n'] [Fintype n] : Matrix n' n'' k × Matrix n n' k → ℂ :=
  tens (ind (stdL k n'') (scal α (stdL k n'))) (ind (stdL k n') (scal α (stdL k n)))

def homLat (α : kˣ) (n'' n' n : Type) : AddSubgroup (Matrix n' n'' k × Matrix n n' k) where
  carrier := {x | (∀ r s, ((α⁻¹ : kˣ) : k) * x.1 r s ∈ 𝒪[k]) ∧ ∀ r s, ((α⁻¹ : kˣ) : k) * x.2 r s ∈ 𝒪[k]}
  add_mem' h h' := ⟨fun r s => by simpa [mul_add] using add_mem (h.1 r s) (h'.1 r s),
    fun r s => by simpa [mul_add] using add_mem (h.2 r s) (h'.2 r s)⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  neg_mem' h := ⟨fun r s => by simpa using h.1 r s, fun r s => by simpa using h.2 r s⟩

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

variable {c : Comm D}

end Global

end GlobalTheory.PlaceCompare.Spherical

end
