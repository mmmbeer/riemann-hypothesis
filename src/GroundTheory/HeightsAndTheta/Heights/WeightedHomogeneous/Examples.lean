import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem prod_zpow_single {M : Type*} [CommGroupWithZero M] (f : ι → M) (k₀ : ι) :
    ∏ k, f k ^ ((Pi.single k₀ 1 : ι → ℤ) k) = f k₀ := by
  rw [Finset.prod_eq_single k₀ (fun k _ hk ↦ by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h ↦ absurd (Finset.mem_univ k₀) h), Pi.single_eq_same, zpow_one]

omit [Fintype ι] in
theorem single_cast (k₀ k : ι) : (((Pi.single k₀ 1 : ι → ℕ) k : ℕ) : ℤ) = (Pi.single k₀ 1 : ι → ℤ) k := by
  by_cases h : k = k₀
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

namespace ArithVariety

variable (n : ι → ℕ)

omit [Fintype ι] in
theorem whole_isLive (c : (k : ι) → Fin (n k + 1)) : (whole n).IsLive c := fun _ h ↦
  X_ne_zero _ ((Submodule.mem_bot _).mp h)

omit [Fintype ι] in
theorem whole_mkF_X_ne_zero (v : Coord n) : (whole n).mkF (X v) ≠ 0 := fun h ↦
  X_ne_zero v ((Submodule.mem_bot _).mp (((whole n).mkF_eq_zero_iff _).mp h))

omit [Fintype ι] in
theorem whole_mkF_injective : Function.Injective (whole n).mkF := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  exact (Submodule.mem_bot _).mp (((whole n).mkF_eq_zero_iff f).mp hf)

omit [Fintype ι] in

theorem whole_isHomogGenerators :
    (whole n).IsHomogGenerators (fun i : Fin 0 ↦ i.elim0) (fun i : Fin 0 ↦ i.elim0) where
  homog i := i.elim0
  span_eq := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    rfl

end ArithVariety

variable (n : ι → ℕ) (k₀ : ι)

def blockAddData : AddBlockData (ArithVariety.whole n) where
  deg := Pi.single k₀ 1
  size := n k₀
  elt j := (ArithVariety.whole n).mkF (X ⟨k₀, j⟩)
  elt_deg j := ⟨X ⟨k₀, j⟩, 1, (Pi.single k₀ 1 : ι → ℕ), 0, isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩,
    isWeightedHomogeneous_one ℤ (coordDeg n), fun k ↦ by simp [single_cast],
    (Ideal.ne_top_iff_one _).mp (ArithVariety.whole n).isPrime.ne_top, by rw [map_one, div_one]⟩
  chart_mem c _ j := by
    rw [ArithVariety.chartPow, prod_zpow_single]
    exact Subring.subset_closure ⟨⟨k₀, j⟩, rfl⟩
  generating c _ := by
    refine ⟨Pi.single (c k₀) 1, fun j ↦ ?_, ?_⟩
    · by_cases h : j = c k₀
      · subst h; rw [Pi.single_eq_same]; exact Subring.one_mem _
      · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _
    · rw [Finset.sum_eq_single (c k₀) (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h ↦ absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
        ArithVariety.chartPow, prod_zpow_single]
      exact div_self (ArithVariety.whole_mkF_X_ne_zero n _)

def blockForms : ((k : ι) → Fin (n k + 1)) → Fin ((blockAddData n k₀).size + 1) →
    MvPolynomial (Coord n) ℤ :=
  fun c j ↦ chartMonomial c 1 * X ⟨k₀, j⟩


def blockLine : HermLine n where
  deg := Pi.single k₀ 1
  metric z := l2Norm (z k₀)
  metric_pos z hz := vectorL2Norm_pos (hz k₀)
  metric_smul c z _ _ := by
    rw [vectorL2Norm_const_mul, prod_zpow_single (fun k ↦ ‖c k‖) k₀]
  metric_smooth := contDiffOn_l2Norm_block k₀

def blockVal : Coord (blockAddData n k₀).extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => X ⟨k₀, j⟩
  | ⟨some k, i⟩ => X ⟨k, i⟩

def blockSubst :
    MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ →+* MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (blockVal n k₀ v) * X v.1





omit [Fintype ι] [DecidableEq ι] in

theorem blockNonzero_one : BlockNonzero (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) :=
  fun _ h ↦ one_ne_zero (congrFun h 0)


omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_mul {F : Type*} [CommRing F] (z : Cone n F) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := eval₂_mul _ _


omit [DecidableEq ι] in
theorem standard_quot_deg :
    (0 : ι → ℤ) = (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv).deg := by
  funext k
  simp [HermLine.pow, HermLine.mul, HermLine.inv, HermLine.standard]



theorem whole_ringKrullDim (N : ℕ) :
    ringKrullDim (ArithVariety.whole (fun _ : Unit ↦ N)).CoordRing =
      ((N + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq
      (show (ArithVariety.whole (fun _ : Unit ↦ N)).ideal = ⊥ from rfl)).trans (RingEquiv.quotientBot _)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have hc : Nat.card (Coord (fun _ : Unit ↦ N)) = N + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hc, Fintype.card_unit]
  norm_cast
  omega

def ratIntegerBasis : Module.Basis (Fin (0 + 1)) ℤ (𝓞 ℚ) :=
  (Module.Basis.singleton (Fin 1) ℤ).map Rat.ringOfIntegersEquiv.symm.toAddEquiv.toIntLinearEquiv

theorem ratIntegerBasis_apply (a : Fin (0 + 1)) : ((ratIntegerBasis a : 𝓞 ℚ) : ℚ) = 1 := by
  simp [ratIntegerBasis, Module.Basis.singleton_apply]

open Matrix in

theorem ratStandard_metricAgrees (r : ℕ) :
    OneBlockMetricAgrees ratIntegerBasis (HermLattice.standard ℚ (r + 1))
      (HermLine.standard (oneBlockSizes 0 r)) := by
  intro σ w _
  change ∏ _u : Unit, l2Norm (oneBlockPoint ratIntegerBasis σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  rw [Fintype.prod_unique, l2Norm, one_mulVec]
  congr 1
  have h1 : ∀ p, ‖oneBlockPoint ratIntegerBasis σ w () p‖ ^ 2 = ‖w (oneBlockIndex 0 r p).2‖ ^ 2 := by
    intro p
    simp [oneBlockPoint, ratIntegerBasis_apply]
  simp only [h1]
  rw [Fintype.sum_equiv (oneBlockIndex 0 r) _ (fun q ↦ ‖w q.2‖ ^ 2) (fun _ ↦ rfl),
    Fintype.sum_prod_type, Fin.sum_univ_one, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast



end

end GroundTheory.Heights₂.Heights
