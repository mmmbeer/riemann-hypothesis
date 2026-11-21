import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

section Devissage

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem sup_span_inf_eq' {I : Ideal (MRingOver F ι)}
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι)))) {g : MRingOver F ι}
    {δ : K → ℕ} (hg : g ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) δ) {d : K → ℕ} (hd : δ ≤ d) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) d ⊓ (I ⊔ Ideal.span {g}).restrictScalars F =
      (weightedHomogeneousSubmodule F (mw (ι := ι)) d ⊓ I.restrictScalars F) ⊔
        (weightedHomogeneousSubmodule F (mw (ι := ι)) (d - δ)).map (LinearMap.mulLeft F g) := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨hxd, hx⟩ := Submodule.mem_inf.mp hx
    rw [Submodule.restrictScalars_mem, Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have hdd : d - δ + δ = d := tsub_add_cancel_of_le hd
    have key := DirectSum.coe_decompose_mul_add_of_right_mem
      (𝒜 := weightedHomogeneousSubmodule F (mw (ι := ι))) (a := c) (i := d - δ) hg
    rw [hdd] at key
    have hx' := DirectSum.decompose_of_mem_same (ℳ := weightedHomogeneousSubmodule F (mw (ι := ι))) hxd
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, key] at hx'
    rw [← hx']
    refine Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨SetLike.coe_mem _, ?_⟩)
      (Submodule.mem_map.mpr ⟨_, SetLike.coe_mem
        ((DirectSum.decompose (weightedHomogeneousSubmodule F (mw (ι := ι))) c) (d - δ)), ?_⟩)
    · rw [Submodule.restrictScalars_mem]
      exact hI d ha
    · rw [LinearMap.mulLeft_apply, mul_comm]
  · refine sup_le (inf_le_inf_left _ ?_) ?_
    · intro x hx
      rw [Submodule.restrictScalars_mem] at hx ⊢
      exact Ideal.mem_sup_left hx
    · rintro y ⟨z, hz, rfl⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [LinearMap.mulLeft_apply]
        have := SetLike.GradedMul.mul_mem hg hz
        rwa [add_tsub_cancel_of_le hd] at this
      · rw [Submodule.restrictScalars_mem, LinearMap.mulLeft_apply]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))



end Devissage

section Lex

def lexDeg : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun a := toLex fun i => a ((Fintype.equivFin K).symm i)
  map_zero' := rfl
  map_add' _ _ := rfl

instance lexDecEq : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq

theorem lexDeg_injective : Function.Injective (lexDeg (K := K)) := by
  intro a b h
  have h' : (fun i => a ((Fintype.equivFin K).symm i)) = fun i => b ((Fintype.equivFin K).symm i) :=
    toLex.injective h
  funext k
  simpa using congrFun h' (Fintype.equivFin K k)

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem weight_lex (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun p => lexDeg (mw (ι := ι) p)) m = lexDeg (Finsupp.weight (mw (ι := ι)) m) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]

theorem mem_lex_of_mem {x : MRingOver F ι} {d : K → ℕ}
    (hx : x ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) d) :
    x ∈ weightedHomogeneousSubmodule F (fun p => lexDeg (mw (ι := ι) p)) (lexDeg d) := by
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro m hm
  rw [weight_lex, hx hm]

theorem homog_of_lex {x : MRingOver F ι} {l : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : x ∈ weightedHomogeneousSubmodule F (fun p => lexDeg (mw (ι := ι) p)) l) :
    ∃ d, x ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) d := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  by_cases h : ∃ m, coeff m x ≠ 0
  · obtain ⟨m₀, hm₀⟩ := h
    refine ⟨Finsupp.weight (mw (ι := ι)) m₀, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    intro m hm
    exact lexDeg_injective (by rw [← weight_lex, ← weight_lex, hx hm, hx hm₀])
  · push_neg at h
    refine ⟨0, ?_⟩
    rw [mem_weightedHomogeneousSubmodule]
    intro m hm
    exact absurd (h m) hm

theorem weighted_le_of_irrel {P : Ideal (MRingOver F ι)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MRingOver F ι) ∈ P) {e : K → ℕ} (he : 1 ≤ e k) :
    weightedHomogeneousSubmodule F (mw (ι := ι)) e ≤ P.restrictScalars F := by
  intro x hx
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [Submodule.restrictScalars_mem, x.as_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hw := hx (mem_support_iff.mp hm)
  obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : Finsupp.weight (mw (ι := ι)) m k = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun p _ => ?_
      rcases p with ⟨k', j⟩
      simp only [mw, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k' = k
      · subst hk
        simp [hcon j]
      · simp [Pi.single_apply, Ne.symm hk]
    rw [hw] at h0
    omega
  have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ m := by
    rw [Finsupp.single_le_iff]
    omega
  have hmono : monomial m (coeff m x) =
      monomial (m - Finsupp.single ⟨k, i⟩ 1) (coeff m x) * X ⟨k, i⟩ := by
    rw [X, monomial_mul, mul_one, tsub_add_cancel_of_le hle]
  rw [hmono]
  exact Ideal.mul_mem_left _ _ (hk i)

end Lex

section Len

variable {R : Type*} [CommRing R]

def colonMul (I : Ideal R) (g : R) : (R ⧸ I.colon {g}) →ₗ[R] (R ⧸ I) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R g) fun x hx => by
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    show g * x ∈ I
    rw [mul_comm]
    exact hx





end Len

end ReciprocityTheory.ChartRestriction.G.AI.I1
