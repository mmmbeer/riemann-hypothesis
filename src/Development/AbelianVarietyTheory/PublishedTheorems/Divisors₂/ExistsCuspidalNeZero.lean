import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SiegelSet.Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem aniso_one (h : IsCMExt F E σ) (z : Fin n → E) (hz : hE σ (1 : Matrix (Fin n) (Fin n) E) z z = 0) : z = 0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have e : ∑ i, σ (z i) * z i = 0 := by
    simpa [hE, Formalism.UG.hform, Matrix.one_apply] using hz
  have e2 := congrArg (fun x => (τ x).re) e
  simp only [map_sum, map_mul, h.2.2.2, map_zero, Complex.zero_re, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at e2
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (τ (z i))).1 e2 i (Finset.mem_univ i)
  exact τ.injective (by simpa using this)





theorem torus_eq_one (h : IsCMExt F E σ) {X Y : Matrix (Fin n) (Fin 0) E} {t : Fin 0 → ℝ} {a : GAd σ J}
    (ha : IsTorusElt σ J X Y t a) : a = 1 := by
  refine GAd_ext σ J (fun w => ?_) fun v => by rw [mem_infPts_iff_forall.1 ha.1 v, map_one]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  apply (archEquiv J h τ).injective
  rw [map_one, map_one]
  refine Subtype.ext (Units.ext ?_)
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h]
  ext i j
  have := congrFun ((ha.2 w τ).2.2 (Pi.single j 1) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) i
  simpa [mulVec, dotProduct, Pi.single_apply, apply_ite, Matrix.one_apply] using this

theorem compact_quotient (hP : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin 0) E} (hW : IsWittFrame σ J X Y) :
    ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ C, g = γ * s := by
  obtain ⟨K, Ω, c, hK, hΩ, -, -, -, -, hcov, -⟩ := hP F E σ h n J hJ 0 X Y hW
  refine ⟨_, hΩ.mul hK, fun g => ?_⟩
  obtain ⟨γ, hγ, _, ⟨p, hp, t, -, a, ha, k, hk, rfl⟩, e⟩ := hcov g
  exact ⟨γ, hγ, _, ⟨p, hp, k, hk, rfl⟩, by rw [e, torus_eq_one h ha, mul_one]⟩


example (t : Fin 1 → ℝ) : modulus ℚ 3 t = t 0 ^ 4 := by
  simp [modulus]
example (t : Fin 2 → ℝ) : modulus ℚ 4 t = t 0 ^ 6 * t 1 ^ 2 := by
  simp [modulus, Fin.prod_univ_two]

end GlobalTheory.SiegelSet.Model

end
