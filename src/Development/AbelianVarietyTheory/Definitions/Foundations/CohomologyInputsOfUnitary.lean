import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2.Test

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem isConj_iff (s : G ℚ Ω) : IsConj s ↔ IsCC s := Iff.rfl



theorem om_mulVec (A : Matrix (Fin 2) (Fin 2) (Qbar l)) (x y : Fin 2 → Qbar l) :
    om (A *ᵥ x) (A *ᵥ y) = A.det * om x y := by
  simp [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem om_equiv (W : R2 Ω l) (s : G ℚ Ω) (x y : Fin 2 → Qbar l) :
    om (mat W s *ᵥ x) (mat (dual1 W) s *ᵥ y) = eps l s * om x y := by
  have h1 : mat (dual1 W) s = (eps l s * ((mat W s).det)⁻¹) • mat W s := by
    rw [mat, dual1, tw_val]; simp [dt]
  have h2 : (mat W s).det ≠ 0 := (Matrix.GeneralLinearGroup.det (W s)).ne_zero
  have h3 : ∀ (a : Qbar l) (u v : Fin 2 → Qbar l), om u (a • v) = a * om u v := fun a u v => by
    simp [om]; ring
  rw [h1, Matrix.smul_mulVec, h3, om_mulVec]; field_simp

theorem om_add_left (x y z : Fin 2 → Qbar l) : om (x + y) z = om x z + om y z := by simp [om]; ring
theorem om_add_right (x y z : Fin 2 → Qbar l) : om z (x + y) = om z x + om z y := by simp [om]; ring

theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by simp [mat]

theorem cup_coc (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l) (ha : ∀ s t, a (s * t) = a s + mat W s *ᵥ a t)
    (hb : ∀ s t, b (s * t) = b s + mat (dual1 W) s *ᵥ b t) (r s t : G ℚ Ω) :
    eps l r * cup W a b s t + cup W a b r (s * t) = cup W a b (r * s) t + cup W a b r s := by
  simp only [cup]
  rw [ha, hb, mat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, om_add_left, om_add_right, om_equiv]
  ring

theorem eps_eq (s : G ℚ Ω) : eps l s = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cont_int : Continuous (algebraMap ℤ_[l] (Qbar l)) :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val

theorem cg_refl (n : ℕ) (a : Qbar l) : Cg n a a := by simp [Cg]

theorem cycZ_ine [IsAlgClosure ℚ Ω] {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
  simp



theorem nu (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u

end GlobalTheory.Ord2.Test

end
