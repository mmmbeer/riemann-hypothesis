import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GammaMembershipConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker GlobalTheory.IndefiniteRowSideFullHecke Filter Topology
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.VacuumFrameCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem af_ext {α β : Af D.host.F} (h : ∀ w, evalV D.host.F w α = evalV D.host.F w β) : α = β :=
  FiniteAdeleRing.ext _ h

theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from af_ext fun w => ?_)
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

theorem place_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * α = α from af_ext fun w => ?_)
  rw [map_mul]
  by_cases hw : w = v
  · rw [hw, h1, mul_one]
  · rw [h0 w hw, zero_mul]

theorem place_inf {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  exact TensorProduct.zero_tmul _ _

theorem eq_of_orth {R : Type} [CommRing R] {e c e' c' : R} (h : e + c = e' + c') (h1 : e * e' = 0) (h2 : c * c' = 0)
    (h3 : e * e = e) (h4 : e * c = 0) (h5 : c' * c' = c') (h6 : e' * c' = 0) : e = c' := by
  linear_combination (e + c') * h - h3 - h4 + h1 - h2 + h6 + h5

theorem eq_or_eq_conj {e e' : AE D} (he : IsSplitIdem D e) (he' : IsSplitIdem D e')
    (h : e + cA D e = e' + cA D e') : e = e' ∨ e = cA D e' := by
  rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he he' with h1 | h1
  · exact Or.inl h1
  · right
    have h2 : cA D e * cA D e' = 0 := by rw [← map_mul, h1, map_zero]
    exact eq_of_orth h h1 h2 he.1 he.2.1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA he').1 he'.2.1


def cut {R : Type} [CommRing R] (η : R) (h : η * η = η) (x : Rˣ) : Rˣ where
  val := 1 + η * ((x : R) - 1)
  inv := 1 + η * (((x⁻¹ : Rˣ) : R) - 1)
  val_inv := by
    have := x.mul_inv
    linear_combination ((x : R) - 1) * (((x⁻¹ : Rˣ) : R) - 1) * h + η * this
  inv_val := by
    have := x.mul_inv
    linear_combination ((x : R) - 1) * (((x⁻¹ : Rˣ) : R) - 1) * h + η * this

def offS (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Af D.host.F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
    (fun v : HeightOneSpectrum (𝓞 D.host.F) => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
    cofinite fun v => if v ∈ S then (0 : v.adicCompletionIntegers D.host.F) else 1

theorem evalV_offS (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : HeightOneSpectrum (𝓞 D.host.F)) :
    evalV D.host.F w (offS D S) = if w ∈ S then 0 else 1 := by
  change (((if w ∈ S then (0 : w.adicCompletionIntegers D.host.F) else 1 : w.adicCompletionIntegers D.host.F)) :
    w.adicCompletion D.host.F) = _
  split_ifs <;> rfl

def offE (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (offS D S))

theorem offE_empty {y : AE D} (hy : infPart D y = 0) : offE D ∅ * y = y := by
  have h1 : offS D ∅ = 1 := af_ext fun w => by rw [evalV_offS, map_one]; simp
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, hy, mul_zero]
  · rw [RingHom.map_mul, offE, h1]
    exact one_mul _

end GlobalTheory.VacuumFrameCompare

end
