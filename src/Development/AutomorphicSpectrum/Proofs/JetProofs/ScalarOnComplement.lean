import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.HCSide

section Circle

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def circleSpace (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) : Submodule ℂ H where
  carrier := {x | ∀ z : ℂ, ‖z‖ = 1 → π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x}
  zero_mem' := fun z _ => by simp
  add_mem' := fun {x y} hx hy z hz => by rw [map_add, hx z hz, hy z hz, smul_add]
  smul_mem' := fun c x hx z hz => by rw [map_smul, hx z hz, smul_comm]

theorem mem_circleSpace {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {m : ℤ} {x : H} :
    x ∈ circleSpace π m ↔ ∀ z : ℂ, ‖z‖ = 1 → π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x := Iff.rfl

theorem isClosed_circleSpace (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) :
    IsClosed (circleSpace π m : Set H) := by
  have : (circleSpace π m : Set H) =
      ⋂ z : ℂ, ⋂ _ : ‖z‖ = 1, {x | π (z • (1 : Matrix (Fin n) (Fin n) ℂ)) x = z ^ m • x} := by
    ext x; simp [mem_circleSpace]
  rw [this]
  exact isClosed_iInter fun z => isClosed_iInter fun _ =>
    isClosed_eq (π _).continuous (continuous_const_smul _)

instance [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m : ℤ) :
    CompleteSpace (circleSpace π m) :=
  (isClosed_circleSpace π m).completeSpace_coe

end Circle

section Blocks

variable {n : ℕ} {ι : Type} [Fintype ι]

structure CentralBlocks (G : Set (Matrix (Fin n) (Fin n) ℂ)) (P D : ι → Matrix (Fin n) (Fin n) ℂ) : Prop where

  lin : IsLinRed G

  closed : IsClosed G

  polar : ∀ g ∈ G, ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧
    (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ G) ∧ g = NormedSpace.exp X * NormedSpace.exp Y

  proj_isHermitian : ∀ l, (P l)ᴴ = P l

  P_idem : ∀ l, P l * P l = P l

  P_ne : ∀ l, P l ≠ 0

  P_comm : ∀ l, ∀ g ∈ G, P l * g = g * P l

  det_norm : ∀ l, ∀ g ∈ G, ‖(1 - P l + P l * g).det‖ = 1

  D_idem : ∀ l, D l * D l = D l

  D_orth : ∀ l k, l ≠ k → D l * D k = 0

  D_sum : ∑ l, D l = 1

  D_comm : ∀ l, ∀ g ∈ G, D l * g = g * D l

  PD : ∀ l, P l * D l = P l

  PD_ne : ∀ l k, l ≠ k → P l * D k = 0

  scal_mem : ∀ c : ι → ℂ, (∀ l, ‖c l‖ = 1) → ∑ l, c l • D l ∈ G

  centre : ∀ z ∈ G, (∀ g ∈ G, z * g = g * z) → ∃ c : ι → ℂ, z = ∑ l, c l • D l

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end Exp

end Blocks

section Levi

variable {n a : ℕ}

variable (ε : Fin n → Bool)

end Levi

end GlobalTheory.CompanionTheory.HCSide

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCSS GlobalTheory.CompanionTheory.HCSide
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.HCSide.CentreNone

variable {n a : ℕ} {ε : Fin n → Bool}

theorem Jm_herm (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  simp only [Jm, diagonal_conjTranspose]; congr 1; funext i; by_cases h : ε i <;> simp [h]

theorem half_props {C J : Matrix (Fin n) (Fin n) ℂ} (hh : Cᴴ = C) (hi : C * C = C) (hJ : J * C = C * J)
    (hJJ : J * J = 1) (hJh : Jᴴ = J) {t : ℂ} (ht : t * t = 1) (hs : star t = t) :
    ((1 / 2 : ℂ) • (C * (1 + t • J)))ᴴ = (1 / 2 : ℂ) • (C * (1 + t • J)) ∧
      (1 / 2 : ℂ) • (C * (1 + t • J)) * ((1 / 2 : ℂ) • (C * (1 + t • J))) = (1 / 2 : ℂ) • (C * (1 + t • J)) ∧
      J * ((1 / 2 : ℂ) • (C * (1 + t • J))) = t • ((1 / 2 : ℂ) • (C * (1 + t • J))) := by
  have c : (1 + t • J) * C = C * (1 + t • J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hJ]
  have s : (1 + t • J) * (1 + t • J) = (2 : ℂ) • (1 + t • J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, hJJ,
      smul_smul, ht]
    match_scalars <;> first | linear_combination ht | ring
  have e : C * (1 + t • J) * (C * (1 + t • J)) = (2 : ℂ) • (C * (1 + t • J)) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + t • J), c, Matrix.mul_assoc, s, ← Matrix.mul_assoc, hi,
      mul_smul_comm]
  refine ⟨?_, ?_, ?_⟩
  · have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_add, conjTranspose_one, conjTranspose_smul, hh, hJh,
      hs, h2, c]
  · rw [smul_mul_assoc, mul_smul_comm, e, smul_smul, smul_smul]
    norm_num
  · have e2 : J * (1 + t • J) = t • (1 + t • J) := by
      simp only [Matrix.mul_add, Matrix.mul_one, mul_smul_comm, hJJ, smul_add, smul_smul, ht]
      module
    rw [mul_smul_comm, ← Matrix.mul_assoc, hJ, Matrix.mul_assoc, e2, mul_smul_comm, smul_comm]

theorem exists_frame_J {C : Matrix (Fin n) (Fin n) ℂ} (hh : Cᴴ = C) (hi : C * C = C)
    (hJ : Jm ε * C = C * Jm ε) :
    ∃ (m : ℕ) (ε' : Fin m → Bool) (B : Matrix (Fin n) (Fin m) ℂ),
      Bᴴ * B = 1 ∧ B * Bᴴ = C ∧ Jm ε * B = B * Jm ε' := by
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh := Jm_herm ε
  obtain ⟨p1, p2, p3⟩ := half_props hh hi hJ hJJ hJh (t := 1) (by norm_num) (by simp)
  obtain ⟨m1, m2, m3⟩ := half_props hh hi hJ hJJ hJh (t := -1) (by norm_num) (by simp)
  have hsum : (1 / 2 : ℂ) • (C * (1 + (1 : ℂ) • Jm ε)) + (1 / 2 : ℂ) • (C * (1 + (-1 : ℂ) • Jm ε)) = C := by
    simp only [Matrix.mul_add, Matrix.mul_one, mul_smul_comm]
    module
  generalize (1 / 2 : ℂ) • (C * (1 + (1 : ℂ) • Jm ε)) = Dp at p1 p2 p3 hsum
  generalize (1 / 2 : ℂ) • (C * (1 + (-1 : ℂ) • Jm ε)) = Dm at m1 m2 m3 hsum
  obtain ⟨r, Bp, a1, a2⟩ := GlobalTheory.IsoTorus.proj_frame p1 p2
  obtain ⟨s, Bm, b1, b2⟩ := GlobalTheory.IsoTorus.proj_frame m1 m2
  have hp : Jm ε * Bp = Bp := by
    have e : Bp = Dp * Bp := by rw [← a2, Matrix.mul_assoc, a1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, p3, one_smul]
  have hm : Jm ε * Bm = -Bm := by
    have e : Bm = Dm * Bm := by rw [← b2, Matrix.mul_assoc, b1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, m3, neg_one_smul, Matrix.neg_mul]
  have hpH : Bpᴴ * Jm ε = Bpᴴ := by
    have := congrArg conjTranspose hp
    rwa [conjTranspose_mul, hJh] at this
  have hX : Bpᴴ * Bm = 0 := by
    have e : Bpᴴ * Bm = -(Bpᴴ * Bm) := by
      nth_rewrite 1 [← hpH]
      rw [Matrix.mul_assoc, hm, Matrix.mul_neg]
    have e2 : (2 : ℂ) • (Bpᴴ * Bm) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e]
      simp
    exact (smul_eq_zero.1 e2).resolve_left two_ne_zero
  have hX' : Bmᴴ * Bp = 0 := by
    have := congrArg conjTranspose hX
    simpa [conjTranspose_mul] using this
  refine ⟨r + s, fun k => Sum.elim (fun _ => true) (fun _ => false) (finSumFinEquiv.symm k),
    (fromCols Bp Bm).submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · rw [conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, a1, b1, hX, hX', fromBlocks_one]
    exact submatrix_one_equiv _
  · rw [conjTranspose_submatrix, Matrix.submatrix_mul_equiv, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromCols_mul_fromRows, a2, b2, hsum]
    rfl
  · ext i k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    have e1 := fun l => congrFun (congrFun hp i) l
    have e2 := fun l => congrFun (congrFun hm i) l
    rcases k with l | l
    · have := e1 l
      simp only [Jm, diagonal_mul] at this ⊢
      simpa [mul_diagonal] using this
    · have := e2 l
      simp only [Jm, diagonal_mul] at this ⊢
      simpa [mul_diagonal] using this


end GlobalTheory.CompanionTheory.HCSide.CentreNone

end
end
