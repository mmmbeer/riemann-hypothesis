import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

def formsDeg (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (d : K → ℕ) :
    Submodule F (MRingOver F ι) :=
  Submodule.span F {f | ∃ m : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, m ⟨k, i⟩ = d k) ∧ f = monomial m 1}

instance finiteDimensional_formsDeg (d : K → ℕ) : FiniteDimensional F (formsDeg F ι d) := by
  classical
  unfold formsDeg
  apply FiniteDimensional.span_of_finite
  have hfin : {m : (Σ k, ι k) →₀ ℕ | ∀ k, ∑ i, m ⟨k, i⟩ = d k}.Finite := by
    apply (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun p : Σ k, ι k => d p.1)).subset
    intro m hm
    rw [Set.mem_Iic, Finsupp.le_def]
    intro p
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p.2)
  exact (hfin.image fun m => monomial m (1 : F)).subset (by
    rintro f ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section SupSpan

variable [DecidableEq K]

end SupSpan

end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

open Classical in

def secNum (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ) : MRingOver F ι :=
  if h : IsRelevant V then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver F ι) ^ (a k).toNat else 1

open Classical in

def secDen (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ) : MRingOver F ι :=
  if h : IsRelevant V then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver F ι) ^ (-a k).toNat else 1

open Classical in

def ptDeg0 (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (V : Ideal (MRingOver F ι)) : ℕ :=
  if h : IsRelevant V then ptDeg V (fun k => (h k).choose) else 0

theorem isRatSection_sec {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) (a : K → ℤ) :
    IsRatSection V a (secNum F ι V a) (secDen F ι V a) := by
  classical
  have hr := hV.2.2
  refine ⟨fun k => (a k).toNat, fun k => (-a k).toNat, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [secNum, dif_pos hr]
    exact isMultiHomog_coordProd _ _
  · simp only [secDen, dif_pos hr]
    exact isMultiHomog_coordProd _ _
  · simp only [secNum, dif_pos hr]
    exact coordProd_not_mem hV.1 _ (fun k => (hr k).choose_spec) _
  · simp only [secDen, dif_pos hr]
    exact coordProd_not_mem hV.1 _ (fun k => (hr k).choose_spec) _
  · intro k
    simp

theorem mem_of_ratDiv_ne_zero {V W : Ideal (MRingOver F ι)} {f g : MRingOver F ι}
    (h : ratDiv V f g W ≠ 0) : W ∈ divSupp V f ∨ W ∈ divSupp V g := by
  by_contra hc
  rw [not_or] at hc
  apply h
  have hf : divCycle V f W = 0 := by
    by_contra h'
    exact hc.1 (mem_divSupp_of_divCycle_ne_zero h')
  have hg : divCycle V g W = 0 := by
    by_contra h'
    exact hc.2 (mem_divSupp_of_divCycle_ne_zero h')
  simp [ratDiv, hf, hg]

end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end
