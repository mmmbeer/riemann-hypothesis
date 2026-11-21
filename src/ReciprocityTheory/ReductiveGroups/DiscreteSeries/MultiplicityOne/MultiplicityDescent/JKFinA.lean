import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.BesselIsometryScalar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntegrable
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
  ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

variable {k r : ℕ}

def cj (t : Mat k r) (x : Mt k r) : Mt k r := fun i j => (t⁻¹ * Matrix.of x * t) i j

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
  ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

variable {k r : ℕ}

section twist

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {t : Mat k r}

theorem tw_cancel (ht : t ∈ GV k r) (g : Mat k r) : t * (t⁻¹ * g * t) * t⁻¹ = g := by
  simp only [Matrix.mul_assoc]
  rw [gv_mul_inv ht, Matrix.mul_one, ← Matrix.mul_assoc, gv_mul_inv ht, Matrix.one_mul]

theorem tw_irr (hσ : Formalism.MainNotions.S.IsIrredOn (GV k r) σ) (ht : t ∈ GV k r) :
    Formalism.MainNotions.S.IsIrredOn (GV k r) (fun g => σ (t * g * t⁻¹)) := by
  intro S hS hst
  refine hσ S hS fun g hg v hv => ?_
  have := hst (t⁻¹ * g * t) (gv_mul (gv_mul (gv_inv ht) hg) ht) v hv
  simpa only [tw_cancel ht] using this

end twist

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

section abstract

variable {K : Type} [Group K] [TopologicalSpace K]

def Fin2 (α : C(K, ℂ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → K → ℂ) (β : ι → C(K, ℂ)), ∀ k₀ κ, α (k₀ * κ) = ∑ i, a i k₀ * β i κ

def finAlg (K : Type) [Group K] [TopologicalSpace K] : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {α | Fin2 α}
  mul_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι × ι', inferInstance, fun i k => a i.1 k * a' i.2 k, fun i => β i.1 * β' i.2, fun k₀ κ => ?_⟩
    rw [ContinuousMap.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousMap.mul_apply]; ring
  add_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim β β', fun k₀ κ => ?_⟩
    rw [ContinuousMap.add_apply, h, h', Fintype.sum_sum_type]
    rfl
  algebraMap_mem' c := ⟨Unit, inferInstance, fun _ _ => c, fun _ => 1, fun k₀ κ => by simp⟩
  star_mem' := by
    rintro α ⟨ι, _, a, β, h⟩
    refine ⟨ι, inferInstance, fun i k => star (a i k), fun i => star (β i), fun k₀ κ => ?_⟩
    rw [ContinuousMap.star_apply, h, star_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul', ContinuousMap.star_apply]

theorem exists_pairing [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hsep : (finAlg K).SeparatesPoints) (g : C(K, ℂ)) (hg : g 1 ≠ 0) :
    ∃ α : C(K, ℂ), Fin2 α ∧ ∫ κ, α κ * g κ ∂μ ≠ 0 := by
  by_contra hn
  push Not at hn
  have hint : ∀ α : C(K, ℂ), Integrable (fun κ => α κ * g κ) μ := fun α =>
    (BoundedContinuousFunction.mkOfCompact (α * g)).integrable μ
  let Λ : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun α => ∫ κ, α κ * g κ ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hint a) (hint b)]
        simp only [ContinuousMap.add_apply, add_mul]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc] }
  have hΛ : ∀ α, ‖Λ α‖ ≤ (‖g‖ * μ.real Set.univ) * ‖α‖ := fun α => by
    refine (norm_integral_le_of_norm_le_const (C := ‖α‖ * ‖g‖) (Filter.Eventually.of_forall fun κ => ?_)).trans
      (le_of_eq (by ring))
    rw [norm_mul]
    exact mul_le_mul (α.norm_coe_le_norm κ) (g.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have hcl : IsClosed {α : C(K, ℂ) | Λ.mkContinuous _ hΛ α = 0} := isClosed_eq (Λ.mkContinuous _ hΛ).continuous continuous_const
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (finAlg K) hsep
  have hmem : star g ∈ closure ((finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have : star g ∈ (finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  have h0 : ∫ κ, (star g) κ * g κ ∂μ = 0 := hcl.closure_subset_iff.2 (fun α hα => hn α hα) hmem
  have e : ∀ κ, (star g) κ * g κ = ((‖g κ‖ ^ 2 : ℝ) : ℂ) := fun κ => by
    rw [ContinuousMap.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e] at h0
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ κ, ‖g κ‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
  have hc : Continuous fun κ => ‖g κ‖ ^ 2 := g.continuous.norm.pow 2
  have hi : Integrable (fun κ => ‖g κ‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact (⟨_, hc⟩ : C(K, ℝ))).integrable μ
  have h2 := (integral_eq_zero_iff_of_nonneg (fun κ => sq_nonneg _) hi).1 h1
  have h3 := congrFun ((hc.ae_eq_iff_eq μ continuous_const).1 h2) 1
  exact hg (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))

end abstract

variable {k r : ℕ}

def KK (k r : ℕ) : Set (Mat k r) := GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)




end ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF
end
end
