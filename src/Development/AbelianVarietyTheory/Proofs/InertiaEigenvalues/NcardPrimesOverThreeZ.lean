import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FieldCompatibleIffWdRel

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt.Inhab

abbrev QI : Type := CyclotomicField 4 ℚ

instance : IsGalois ℚ QI := IsCyclotomicExtension.isGalois {4} ℚ QI

theorem finrank_QI : Module.finrank ℚ QI = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 QI]; decide

def threeZ : Ideal ℤ := Ideal.span {((3 : ℕ) : ℤ)}

instance : threeZ.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).2 (Nat.prime_iff_prime_int.mp Nat.prime_three)

theorem threeZ_ne_bot : threeZ ≠ ⊥ := by
  simp [threeZ]

theorem ncard_primesOver_threeZ : (threeZ.primesOver (𝓞 QI)).ncard = 1 := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn threeZ (𝓞 QI) (QI ≃ₐ[ℚ] QI)
  have hf := IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 4) 3 QI (by norm_num)
  have ho : orderOf ((3 : ℕ) : ZMod 4) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hc : Nat.card (QI ≃ₐ[ℚ] QI) = 2 := by rw [IsGalois.card_aut_eq_finrank, finrank_QI]
  rw [show threeZ = Ideal.span {((3 : ℕ) : ℤ)} from rfl, hf, ho, hc, ← mul_assoc] at h
  exact Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_right two_pos (h.trans (one_mul 2).symm))

def primeAbove3 : threeZ.primesOver (𝓞 QI) := (Ideal.nonempty_primesOver (S := 𝓞 QI) threeZ).some

theorem primeAbove3_ne_bot : (primeAbove3 : Ideal (𝓞 QI)) ≠ ⊥ := by
  intro h0
  have hov := (primeAbove3.2.2).over
  rw [h0, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 QI))] at hov
  exact threeZ_ne_bot hov

def placeAbove3 : HeightOneSpectrum (𝓞 QI) := ⟨primeAbove3.1, primeAbove3.2.1, primeAbove3_ne_bot⟩

def place3 : HeightOneSpectrum (𝓞 ℚ) := placeAbove3.under (𝓞 ℚ)

theorem placeAbove3_under_int : placeAbove3.asIdeal.under ℤ = threeZ :=
  (primeAbove3.2.2).over.symm


section Loc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end Loc

end GlobalTheory.FunExt.Inhab

end
