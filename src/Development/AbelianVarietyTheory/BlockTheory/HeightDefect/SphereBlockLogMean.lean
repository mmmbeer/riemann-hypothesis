import Mathlib

open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

abbrev UnitSphere (N : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1

def sphereSurface (N : ℕ) : Measure (UnitSphere N) :=
  (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere

def sphereMeasure (N : ℕ) : Measure (UnitSphere N) :=
  (sphereSurface N Set.univ)⁻¹ • sphereSurface N

instance sphereSurface_finite (N : ℕ) : IsFiniteMeasure (sphereSurface N) := by
  unfold sphereSurface; infer_instance

instance sphereSurface_neZero (N : ℕ) : NeZero (sphereSurface N) := by
  refine ⟨fun h => ?_⟩
  have := (Measure.toSphere_eq_zero_iff _).1 h
  exact not_subsingleton _ this

instance sphereMeasure_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (sphereMeasure N) := by
  unfold sphereMeasure; infer_instance

def sphereMap {N : ℕ}
    (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)))
    (z : UnitSphere N) : UnitSphere N :=
  ⟨e z.1, by simpa using z.2⟩


def blockSphereMeasure (B N : ℕ) : Measure (Fin B → UnitSphere N) :=
  Measure.pi fun _ => sphereMeasure N

instance blockSphereMeasure_isProbabilityMeasure (B N : ℕ) :
    IsProbabilityMeasure (blockSphereMeasure B N) := by
  unfold blockSphereMeasure; infer_instance

def blockLogAbs {B N : ℕ} (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ)
    (T : Fin B → UnitSphere N) : ℝ :=
  Real.log ‖eval (fun i => (T i.1).1 i.2) P‖

def blockLogMean {B N : ℕ} (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ) : ℝ :=
  ∫ T, blockLogAbs P T ∂blockSphereMeasure B N

def IsBlockHomogeneous {R : Type} [CommSemiring R] {B n : ℕ}
    (ω : MvPolynomial (Fin B × Fin n) R) (a : Fin B → ℕ) : Prop :=
  ∀ d : Fin B × Fin n →₀ ℕ, coeff d ω ≠ 0 → ∀ b : Fin B, ∑ j : Fin n, d (b, j) = a b

section NumberField

variable {K : Type} [Field K] [NumberField K]

def gaussAbsValue {ι : Type} (w : FinitePlace K) (ω : MvPolynomial ι K) : ℝ :=
  ((ω.support.sup fun d => Real.toNNReal (w (coeff d ω)) : ℝ≥0) : ℝ)



theorem exists_gaussAbsValue_eq {ι : Type} (w : FinitePlace K) {ω : MvPolynomial ι K}
    (h : ω ≠ 0) : ∃ d ∈ ω.support, gaussAbsValue w ω = w (coeff d ω) := by
  obtain ⟨d, hd, e⟩ := Finset.exists_mem_eq_sup ω.support (support_nonempty.2 h)
    fun d => Real.toNNReal (w (coeff d ω))
  exact ⟨d, hd, by rw [gaussAbsValue, e, Real.coe_toNNReal _ (apply_nonneg w _)]⟩



def heightZero {B N : ℕ} (ω : MvPolynomial (Fin B × Fin (N + 1)) K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (gaussAbsValue w ω)) +
    ∑ σ : K →+* ℂ, blockLogMean (MvPolynomial.map σ ω)) / (Module.finrank ℚ K : ℝ)

end NumberField

def hermitianLinearForm {N : ℕ} (u : EuclideanSpace ℂ (Fin (N + 1))) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ j, X j * C (starRingEnd ℂ (u j))

def HeightZeroAdditive : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a a' : Fin B → ℕ)
    (ω ω' : MvPolynomial (Fin B × Fin (N + 1)) K), ω ≠ 0 → ω' ≠ 0 →
    IsBlockHomogeneous ω a → IsBlockHomogeneous ω' a' →
    heightZero (ω * ω') = heightZero ω + heightZero ω'

def HeightZeroOnFractions : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a b a' b' : Fin B → ℕ)
    (p q p' q' : MvPolynomial (Fin B × Fin (N + 1)) K), p ≠ 0 → q ≠ 0 → p' ≠ 0 → q' ≠ 0 →
    IsBlockHomogeneous p a → IsBlockHomogeneous q b →
    IsBlockHomogeneous p' a' → IsBlockHomogeneous q' b' → p * q' = p' * q →
    heightZero p - heightZero q = heightZero p' - heightZero q'

example (B n : ℕ) (b₀ : Fin B) (j₀ : Fin n) :
    IsBlockHomogeneous (X (b₀, j₀) : MvPolynomial (Fin B × Fin n) ℚ) (Pi.single b₀ 1) := by
  intro d hd b
  rw [coeff_X'] at hd
  have : Finsupp.single (b₀, j₀) 1 = d := by
    by_contra h; exact hd (if_neg h)
  subst this
  by_cases hb : b = b₀
  · subst hb; simp [Finsupp.single_apply, eq_comm]
  · simp [Finsupp.single_apply, hb, Ne.symm hb]

example (K : Type) [Field K] [NumberField K] (B N : ℕ) :
    heightZero (1 : MvPolynomial (Fin B × Fin (N + 1)) K) = 0 := by
  have h : ∀ w : FinitePlace K,
      gaussAbsValue w (1 : MvPolynomial (Fin B × Fin (N + 1)) K) = 1 := by
    intro w
    obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w
      (one_ne_zero : (1 : MvPolynomial (Fin B × Fin (N + 1)) K) ≠ 0)
    rw [mem_support_iff, coeff_one] at hd
    rw [e, coeff_one, if_pos (by by_contra h; exact hd (if_neg h)), map_one]
  simp [heightZero, h, blockLogMean, blockLogAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
