import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASWitt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASSmall
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASGlue

section
namespace GlobalTheory.ArtinSchreierTilt

open Formalism.BasicNotions.Loc

namespace Div

open scoped NNReal
open Ideal

section General

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))] [IsAdicComplete (span {(p : O)}) O]

noncomputable def lift (u : PreTilt O p) (m : ℕ) : O :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[m]) u)

theorem mk_lift (u : PreTilt O p) (m : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (lift u m) = PreTilt.coeff m u := by
  rw [lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem lift_succ_pow (u : PreTilt O p) (m : ℕ) : lift u (m + 1) ^ p = lift u m := by
  rw [lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem lift_pow (u : PreTilt O p) (m : ℕ) : lift u m ^ p ^ m = PreTilt.untilt u :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m

variable (hv : v.Integers O)
include hv

theorem val_eq_untilt (u : PreTilt O p) (hu : u ≠ 0) :
    PreTilt.val K v O hv p u = v (algebraMap O K (PreTilt.untilt u)) := by
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0 := not_forall.1 fun h => hu (Perfection.ext h)
  have hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0 := by rwa [mk_lift]
  change PreTilt.valAux K v O p u = _
  rw [PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]

theorem dvd_of_val_le (x y : PreTilt O p)
    (h : PreTilt.val K v O hv p x ≤ PreTilt.val K v O hv p y) : y ∣ x := by
  by_cases hx : x = 0
  · exact hx ▸ dvd_zero y
  by_cases hy : y = 0
  · exfalso
    apply hx
    rw [← PreTilt.map_eq_zero hv]
    rw [hy, map_zero] at h
    exact le_antisymm h zero_le
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective (algebraMap O K) := hv.hom_inj
  rw [val_eq_untilt hv x hx, val_eq_untilt hv y hy] at h
  have hY : ∀ m, lift y m ≠ 0 := by
    intro m h0
    apply hy
    rw [← PreTilt.map_eq_zero hv, val_eq_untilt hv y hy, ← lift_pow y m, h0,
      zero_pow (pow_ne_zero _ hp0), map_zero, map_zero]
  have hle : ∀ m, v (algebraMap O K (lift x m)) ≤ v (algebraMap O K (lift y m)) := by
    intro m
    have h' := h
    rw [← lift_pow x m, ← lift_pow y m, map_pow, map_pow, map_pow, map_pow] at h'
    exact (pow_le_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp0)).1 h'
  choose q hq using fun m => hv.dvd_of_le (hle m)
  have hqs : ∀ m, q (m + 1) ^ p = q m := by
    intro m
    have h1 : lift y m * q (m + 1) ^ p = lift y m * q m := by
      rw [← hq m, ← lift_succ_pow y m, ← mul_pow, ← hq (m + 1), lift_succ_pow]
    have hK : algebraMap O K (lift y m) ≠ 0 := fun h0 => hY m (hinj (h0.trans (map_zero _).symm))
    apply hinj
    have h2 := congrArg (algebraMap O K) h1
    rw [map_mul, map_mul] at h2
    exact mul_left_cancel₀ hK h2
  let e : PreTilt O p :=
    (⟨fun m => Ideal.Quotient.mk (span {(p : O)}) (q m), fun m => by
      simp only
      rw [← map_pow, hqs]⟩ : Perfection (ModP O p) p)
  refine ⟨e, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n x = PreTilt.coeff n (y * e)
  rw [map_mul, ← mk_lift, ← mk_lift, hq n, map_mul]
  rfl

end General

end Div

section Complete

open scoped NNReal
open Ideal

variable {p : ℕ} [Fact p.Prime]

theorem norm_eq_val (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := by
  first | exact GlobalTheory.RingBasics.norm_eq_val .. | exact GlobalTheory.RingBasics.norm_eq_val | exact @GlobalTheory.RingBasics.norm_eq_val _ _ | simpa using GlobalTheory.RingBasics.norm_eq_val .. | (intros; exact GlobalTheory.RingBasics.norm_eq_val ..)

theorem isAdicComplete_OC : IsAdicComplete (span {(p : OC p)}) (OC p) := by
  first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _

end Complete

theorem tiltDiv : PI.ArtSch.TiltDiv := by
  intro l _ x y h
  have := isAdicComplete_OC (p := l)
  exact Div.dvd_of_val_le (PadicComplexInt.integers l) x y h

end GlobalTheory.ArtinSchreierTilt

namespace GlobalTheory


end GlobalTheory
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BddDen

variable {l : ℕ} [hl : Fact l.Prime]

abbrev redMap {K : FinExt l} (bk : BK K) : bk.S →+* (OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) :=
  (Ideal.Quotient.mk _).comp ((Per.θ l).comp bk.ev)

theorem redMap_coe {K : FinExt l} (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    redMap bk (p : bk.S) = p.eval₂ ((redMap bk).comp PowerSeries.C) (redMap bk X) := by
  have h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) =
      Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun f => f p) h

theorem redMap_E {K : FinExt l} (bk : BK K) : redMap bk bk.E = redMap bk X ^ bk.Ep.natDegree := by
  rw [BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree,
    map_one, one_mul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  have hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]

theorem flat_not_isUnit {K : FinExt l} (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  have h0 : redMap bk bk.E = 0 := by
    have hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hk
    simp only [redMap, RingHom.comp_apply, hk, map_zero]
  rw [redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h0
  have hX : IsUnit (bk.ev X) := bk.ev_X ▸ hu.map (WittVector.teichmuller l)
  exact PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) →
    ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  intro l _ K bk a ha n
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h
    have h1 := ha.map (WittVector.constantCoeff (p := l) (R := Cb l))
    rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero] at h1
    exact not_isUnit_zero h1
  have hv1 : PI.ArtSch.valb l bk.flat < 1 := by
    by_contra h
    push_neg at h
    exact flat_not_isUnit bk (isUnit_of_dvd_one
      (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))
  have hv0 : 0 < PI.ArtSch.valb l (a.coeff 0) := by
    rw [pos_iff_ne_zero]
    exact fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hv0 hv1
  obtain ⟨c, hc⟩ := GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)
  obtain ⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  have hxy : WittVector.teichmuller l c * a =
      bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b) := by
    have ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b := by linear_combination hb
    have ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀ := by
      rw [bk.ev_X, ← map_pow, hc, map_mul, mul_comm]
    rw [ha', mul_add, ht]
    ring
  have h2 := geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n
  refine ⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i),
    -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩
  rw [pow_mul]
  linear_combination (∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2

end GlobalTheory.BSP.BddDen
end
end
