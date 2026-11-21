import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatLargeCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin.CondTest

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem barF_tmul (a : Af D.host.F) (x : D.host.E) : barF D (a ⊗ₜ x) = a ⊗ₜ star x := rfl

theorem barF_barF (x : AfE D) : barF D (barF D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [barF_tmul, barF_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]



theorem NormOne.mul' {x y : (AfE D)ˣ} (hx : NormOne x) (hy : NormOne y) : NormOne (x * y) := by
  unfold NormOne at *
  rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, one_mul]

theorem NormOne.inv_eq {x : (AfE D)ˣ} (hx : NormOne x) : ((x⁻¹ : (AfE D)ˣ) : AfE D) = barF D x :=
  Units.inv_eq_of_mul_eq_one_right hx

theorem congOne_of_dvd {M N : ℕ} (h : M ∣ N) {x : (AfE D)ˣ} (hx : CongOne N x) : CongOne M x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨w, hw, e⟩ := hx
  exact ⟨k • w, (intAE D).nsmul_mem hw k, by rw [e, mul_smul]⟩







theorem integral_of_mem_intAE {x : D.host.E} (hx : (1 : Af D.host.F) ⊗ₜ[D.host.F] x ∈ intAE D) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) = x := by
  have h : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 x).1 (h hx))




end GlobalTheory.FinalJoin.CondTest
