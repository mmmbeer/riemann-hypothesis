import Mathlib
import Formalism.PeriodIntegrals.JetsPhW
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTer

noncomputable section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

noncomputable def intS (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexValuationRing.intS p

theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega

theorem coeff_pow_memS {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (k : ℕ) : ∀ i ≤ m, PowerSeries.coeff i (f ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    intro i hi
    rw [pow_succ]
    exact coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))

theorem coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.algebraMap_apply, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp

theorem wq_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  simp only [IsWq] at h
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X ^ 1 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := by
    rw [pow_one]; exact h
  have key : ∀ n, (∀ i < n, PowerSeries.coeff i wq ∈ S) → PowerSeries.coeff n wq ∈ S := by
    intro n ih
    rw [h']
    simp only [map_add, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn => exact key n ihn

theorem wq_const {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  simp only [IsWq] at h
  have := congrArg PowerSeries.constantCoeff h
  simpa using this

def serS (S : Subring ℂ_[p]) : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | ∀ n, PowerSeries.coeff n f ∈ S}
  mul_mem' {f g} hf hg n := coeff_mul_memS (fun i _ => hf i) (fun i _ => hg i)
  one_mem' n := by
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' {f g} hf hg n := by
    rw [map_add]; exact S.add_mem (hf n) (hg n)
  zero_mem' n := by simp
  neg_mem' {f} hf n := by
    rw [map_neg]; exact S.neg_mem (hf n)



theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

def vInv (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  1 - (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X ^ 3 * wq) +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X * (PowerSeries.X ^ 3 * wq) +
    3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X ^ 3 * wq) ^ 2)



theorem inverse_omega_holds : InvOmega :=
  _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
