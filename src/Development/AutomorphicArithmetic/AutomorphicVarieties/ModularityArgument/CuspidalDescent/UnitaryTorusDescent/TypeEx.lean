import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UniqRec
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.ToTL
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TypeExNZ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem te_root {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Finite (ResidueField O)] {a b : Oˣ}
    (ha : a ^ (Nat.card (ResidueField O) - 1) = 1) (hb : b ^ (Nat.card (ResidueField O) - 1) = 1)
    (h : residue O a = residue O b) : a = b := by
  letI := Fintype.ofFinite (ResidueField O)
  have hu : ((a * b⁻¹ : Oˣ) : O) ^ (Nat.card (ResidueField O) - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ha, hb]; simp
  have hr : residue O (a * b⁻¹ : Oˣ) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, Units.mul_inv, map_one]
  have h1 := geom_sum_mul ((a * b⁻¹ : Oˣ) : O) (Nat.card (ResidueField O) - 1)
  rw [hu, sub_self] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · have h3 := congrArg (residue O) h2
    simp only [map_sum, map_pow, hr, one_pow, Finset.sum_const, Finset.card_range, map_zero, nsmul_eq_mul, mul_one] at h3
    rw [Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero] at h3
    simp at h3
  · exact mul_inv_eq_one.1 (Units.ext (sub_eq_zero.1 h2))
