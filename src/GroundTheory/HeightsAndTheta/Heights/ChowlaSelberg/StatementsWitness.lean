import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian Module IntermediateField
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

theorem exists_isPeriodLattice (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ Λ, IsPeriodLattice W Λ := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve W
  exact ⟨_, L, C⁻¹, inv_smul_eq_of_smul_eq C hC, rfl⟩

section Model

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] [IsTotallyComplex K]

def unitCMCurve (hK : finrank ℚ K = 2) : CMCurve K :=
  CMCurve.ofLattice (algebraMap K ℂ) (idealPeriodPair (algebraMap K ℂ) hK 1)
    (latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 1)

theorem exists_isogeny_invConst (hK : finrank ℚ K = 2) (E : CMCurve K) {W : WeierstrassCurve ℂ}
    [W.IsElliptic] (C : WeierstrassCurve.VariableChange ℂ) (hC : C • W = E.curve) (a : 𝓞 K)
    (ha : a ≠ 0) : ∃ ψ : Isogeny W W, invConst ψ = algebraMap K ℂ (a : K) := by
  obtain ⟨ι, hι, -⟩ := existsUnique_normalized (algebraMap K ℂ) hK E
  set f : isogEnd W := vcEndEquiv C⁻¹ (inv_smul_eq_of_smul_eq C hC) (ι a) with hfdef
  have hf : endConst W f = algebraMap K ℂ (a : K) := by
    rw [hfdef, endConst_vcEndEquiv, hι]
  have hf0 : f ≠ 0 := by
    rw [hfdef]
    exact (map_ne_zero_iff _ (RingEquiv.injective _)).2
      ((map_ne_zero_iff _ ι.injective).2 ha)
  have hiso : IsIsogeny W W f.1 :=
    (mem_isogHom_iff.mp f.2).resolve_left fun h ↦ hf0 (Subtype.ext h)
  refine ⟨⟨f.1, hiso⟩, ?_⟩
  have h1 := homConst_toHom (⟨f.1, hiso⟩ : Isogeny W W)
  have h2 : Isogeny.toHom (⟨f.1, hiso⟩ : Isogeny W W) = f := Subtype.ext rfl
  rw [h2] at h1
  exact h1.symm.trans hf

theorem exists_model (hK : finrank ℚ K = 2) :
    ∃ (L : IntermediateField K ℂ) (W : WeierstrassCurve L) (_ : W.IsElliptic),
      FiniteDimensional K L ∧
        ∀ a : 𝓞 K, a ≠ 0 → ∃ φ : Isogeny W W, invConst φ = algebraMap K L (a : K) := by
  set E := unitCMCurve hK
  obtain ⟨W, hW, C, hC, hdesc⟩ := E.exists_model_endomorphisms_defined hK
  refine ⟨K⟮E.curve.j⟯, W, hW, ?_, fun a ha ↦ ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional
      (ELL.isAlgebraic_j_over hK E.toEll).isIntegral
  · obtain ⟨ψ, hψ⟩ := exists_isogeny_invConst hK E C hC a ha
    obtain ⟨φ, hφ⟩ := hdesc ψ
    refine ⟨φ, (algebraMap K⟮E.curve.j⟯ ℂ).injective ?_⟩
    rw [← invConst_map, hφ]
    exact hψ.trans (IsScalarTower.algebraMap_apply K K⟮E.curve.j⟯ ℂ _)

omit [IsTotallyComplex K] in

theorem numberField_of_finiteDimensional (L : IntermediateField K ℂ) [FiniteDimensional K L] :
    NumberField L where
  to_finiteDimensional := Module.Finite.trans K L

end Model

abbrev cyclo3 : Type := CyclotomicField 3 ℚ

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {3} ℚ cyclo3 := CyclotomicField.isCyclotomicExtension 3 ℚ

instance : NumberField cyclo3 := IsCyclotomicExtension.numberField {3} ℚ _

theorem finrank_cyclo3 : finrank ℚ cyclo3 = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 3) cyclo3
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

instance : Algebra.IsQuadraticExtension ℚ cyclo3 := ⟨finrank_cyclo3⟩

instance : IsTotallyComplex cyclo3 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) cyclo3 (by norm_num)

def primeDiscriminantCyclo3 : PrimeDiscriminant cyclo3 where
  d := 3
  prime := Nat.prime_three
  mod_four := rfl
  discr_eq := by
    rw [IsCyclotomicExtension.Rat.discr_prime 3 cyclo3]
    norm_num

instance : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ cyclo3 := by
  simpa using (inferInstance : IsCyclotomicExtension {3} ℚ cyclo3)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
