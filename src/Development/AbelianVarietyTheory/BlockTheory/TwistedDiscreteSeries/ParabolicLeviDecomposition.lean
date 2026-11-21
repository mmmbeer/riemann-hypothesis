import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.SmGL GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped NNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition

structure ParabLevi (k : Type) [Field k] (r : ℕ) where

  s : ℕ

  d : Fin s → ℕ

  e : (Σ a, Fin (d a)) ≃ Fin r

  g : GL (Fin r) k

namespace ParabLevi

variable {k : Type} [Field k] {r : ℕ} (P : ParabLevi k r)

def coord : GL (Fin r) k →* GL (Fin r) k := (MulAut.conj P.g⁻¹).toMonoidHom

theorem coord_apply (x : GL (Fin r) k) : P.coord x = P.g⁻¹ * x * P.g := by simp [coord]

def Q : Subgroup (GL (Fin r) k) := (parab k P.e).comap P.coord

def M : Subgroup (GL (Fin r) k) := (leviEmb k P.e).range.comap P.coord

def N : Subgroup (GL (Fin r) k) := (unipRad k P.e).comap P.coord

def lieN : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, blk P.e j ≤ blk P.e i →
    ((P.g⁻¹ : GL (Fin r) k).1 * X * P.g.1) i j = 0}
  zero_mem' := fun i j _ => by simp
  add_mem' := fun {X Y} hX hY i j h => by
    rw [mul_add, add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  smul_mem' := fun c X hX i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

theorem M_le_Q : P.M ≤ P.Q := by
  rintro x ⟨y, hy⟩
  change P.coord x ∈ parab k P.e
  exact hy ▸ leviEmb_mem_parab k P.e y

theorem exists_mul {q : GL (Fin r) k} (hq : q ∈ P.Q) : ∃ m ∈ P.M, ∃ n ∈ P.N, q = m * n := by
  obtain ⟨u, hu, e⟩ := exists_levi_mul_unip k P.e ⟨P.coord q, hq⟩
  have hc : ∀ y, P.coord (P.g * y * P.g⁻¹) = y := fun y => by rw [coord_apply]; group
  refine ⟨P.g * leviEmb k P.e (leviProj k P.e ⟨P.coord q, hq⟩) * P.g⁻¹, ⟨_, (hc _).symm⟩, P.g * u * P.g⁻¹,
    show P.coord _ ∈ unipRad k P.e from (hc u).symm ▸ hu, ?_⟩
  calc q = P.g * P.coord q * P.g⁻¹ := by rw [coord_apply]; group
    _ = P.g * (leviEmb k P.e (leviProj k P.e ⟨P.coord q, hq⟩) * u) * P.g⁻¹ := congrArg (P.g * · * P.g⁻¹) e
    _ = _ := by group


theorem conj_mem_lieN {q : GL (Fin r) k} (hq : q ∈ P.Q) {X : Matrix (Fin r) (Fin r) k} (hX : X ∈ P.lieN) :
    q.1 * X * (q⁻¹ : GL (Fin r) k).1 ∈ P.lieN := by
  intro i j h
  have e : (P.g⁻¹ : GL (Fin r) k).1 * (q.1 * X * (q⁻¹ : GL (Fin r) k).1) * P.g.1 =
      (P.coord q).1 * ((P.g⁻¹ : GL (Fin r) k).1 * X * P.g.1) * (P.coord q⁻¹).1 := by
    simp only [coord_apply, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
  have h1 := mem_parab.1 (show P.coord q ∈ parab k P.e from hq)
  have h2 := mem_parab.1 (show P.coord q⁻¹ ∈ parab k P.e from P.Q.inv_mem hq)
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : blk P.e j < blk P.e b
  · rw [h2 b j hb, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => ?_, zero_mul]
    by_cases ha : blk P.e a < blk P.e i
    · rw [h1 i a ha, zero_mul]
    · rw [hX a b (((not_lt.1 hb).trans h).trans (not_lt.1 ha)), mul_zero]

def adN (q : P.M) : P.lieN →ₗ[k] P.lieN :=
  (LinearMap.mulLeftRight k (q.1.1, (q.1⁻¹ : GL (Fin r) k).1)).restrict fun _ hX =>
    P.conj_mem_lieN (P.M_le_Q q.2) hX


def detOneSubAd (q : P.M) : k := LinearMap.det (1 - P.adN q)

end ParabLevi

def borelLevi (k : Type) [Field k] (r : ℕ) (g : GL (Fin r) k) : ParabLevi k r :=
  ⟨r, fun _ => 1, Equiv.sigmaUnique _ _, g⟩

example (k : Type) [Field k] : !![0, 1; 0, 0] ∈ (borelLevi k 2 1).lieN ∧ !![0, 0; 1, 0] ∉ (borelLevi k 2 1).lieN := by
  refine ⟨fun i j h => ?_, fun h => ?_⟩
  · change j ≤ i at h
    fin_cases i <;> fin_cases j <;> simp_all [borelLevi]
  · have := h 1 0 (show (0 : Fin 2) ≤ 1 by decide)
    simp [borelLevi] at this

variable (F : Type) [Field F] [NumberField F] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev GS : Type := ∀ v : S, GL (Fin r) (Fv F v.1)

variable {F r S} (P : ∀ v : S, ParabLevi (Fv F v.1) r)

def QS : Subgroup (GS F r S) := Subgroup.pi Set.univ fun v => (P v).Q

def MS : Subgroup (GS F r S) := Subgroup.pi Set.univ fun v => (P v).M

def NS : Subgroup (GS F r S) := Subgroup.pi Set.univ fun v => (P v).N

def absDet (q : MS P) : ℝ := ∏ v : S, ‖(P v).detOneSubAd ⟨q.1 v, q.2 v trivial⟩‖

example {v : HeightOneSpectrum (𝓞 F)} {ϖ : (Fv F v)ˣ} (h : IsUnif ϖ) :
    ‖(ϖ : Fv F v)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, h]
  have : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ this]
  have e : WithZero.unzero this = Multiplicative.ofAdd (-1 : ℤ) := WithZero.coe_inj.1 (WithZero.coe_unzero this)
  rw [e]
  simp

def IsLeviPart (K : Subgroup (GS F r S)) (μ : GS F r S → MS P) : Prop :=
  ∀ x, ∃ n ∈ NS P, ∃ k ∈ K, x = μ x * n * k


section Meas

variable {H : Type} [Group H] [MeasurableSpace H] {T M : Subgroup H}

end Meas

def weight (γ : MS P) (b : Quot ((cent (γ : GS F r S)).subgroupOf (MS P)) → ℂ)
    (q : Quot ((cent (γ : GS F r S)).subgroupOf (MS P))) : ℂ :=
  b q * ((absDet P (q.out⁻¹ * γ⁻¹ * q.out) : ℝ) : ℂ)⁻¹

end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicLeviDecomposition
