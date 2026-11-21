import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb Polynomial

namespace GlobalTheory.CompanionTheory.LatPolyB

variable (l : ℕ) [Fact l.Prime]

theorem dvd_pow_of_ne_zero {x : ℤ_[l]} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : ℤ_[l]) ^ n := by
  have h := PadicInt.unitCoeff_spec hx
  refine ⟨x.valuation, ((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ), ?_⟩
  calc (l : ℤ_[l]) ^ x.valuation
      = (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) *
          (((PadicInt.unitCoeff hx : ℤ_[l]ˣ) : ℤ_[l]) * (l : ℤ_[l]) ^ x.valuation) :=
        (Units.inv_mul_cancel_left _ _).symm
    _ = (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * x := congrArg _ h.symm
    _ = x * (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := mul_comm _ _

def quotX : (ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) ≃+* ℤ_[l] :=
  (Ideal.quotEquivOfEq (by simp)).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℤ_[l])).toRingEquiv

theorem cpl : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])})})
    (ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) := by
  have h : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  have e : (Ideal.span {(l : ℤ_[l])}).map ((quotX l).symm : ℤ_[l] →+* _) =
      Ideal.span {((l : ℕ) : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])})} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  rw [← e]
  exact (IsAdicComplete.congr_ringEquiv _ (quotX l).symm).2 h

end GlobalTheory.CompanionTheory.LatPolyB
