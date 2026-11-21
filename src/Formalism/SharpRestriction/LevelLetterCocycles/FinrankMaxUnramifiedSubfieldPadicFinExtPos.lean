import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
import Formalism.PadicSubsetSums.StableGradedCounts.FrobeniusDifferenceDividedPower
import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

section
noncomputable section

namespace Formalism.MainNotions.EmbeddingTypeJumps

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

variable (D : D7)

section Sqrt

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

theorem sqrt_neg_mem (M : IntermediateField ℚ_[l] (Om l)) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3)
    (ζ : Om l) (hζ : IsPrimitiveRoot ζ p) (hM : ζ ∈ M) (y : Om l) (hy : y ^ 2 = -(p : Om l)) :
    y ∈ M := by
  obtain ⟨z, hz⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.sqrt_neg_in_cyclotomic_field p hp hp4 ↥M ⟨ζ, hM⟩
    (IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ)
  have hz' : -(p : Om l) = (z : Om l) * z := by
    have := congrArg (Subtype.val : ↥M → Om l) hz
    simpa using this
  have h0 : (y - z) * (y + z) = 0 := by linear_combination hy + hz'
  rcases mul_eq_zero.mp h0 with h | h
  · rw [sub_eq_zero.mp h]; exact z.2
  · rw [eq_neg_of_add_eq_zero_left h]; exact M.neg_mem z.2

end Sqrt

section Local

open Formalism.BasicNotions.Loc Polynomial UpperTheory.InertGen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

end Local

section Proviso

open Ideal

end Proviso

section Kill

open Formalism.MainNotions.N

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.EmbeddingTypeJumps

end
end

section
noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks (K : FinExt l) {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

end Formalism.MainNotions.N.PreambleDegrees
end
end
