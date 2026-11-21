import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder

variable {κ : Type} [Fintype κ] {D : ℕ}

def evalConstSnd (w : ((k : Unit) → GlobalTheory κ k) → ℂ) : Ix κ → ℂ := fun p => w fun _ => p.2

theorem adbLift_segre (z : Ix κ → ℂ) : evalConstSnd (segre (ι := GlobalTheory κ) z) = z := by
  funext p
  simp [evalConstSnd, segre]

theorem adb_segre_smul (c : ℂ) (z : Ix κ → ℂ) :
    segre (ι := GlobalTheory κ) (c • z) = c • segre (ι := GlobalTheory κ) z := by
  funext p
  simp [segre]

theorem adb_segre_injective : Function.Injective (segre (ι := GlobalTheory κ)) := fun z z' h => by
  rw [← adbLift_segre z, h, adbLift_segre]

theorem adb_mem_mcPts_iff {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} :
    z ∈ mcPts (ι := GlobalTheory κ) P ↔ z ∈ pts P := by
  simp only [mcPts, pts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, h⟩
    obtain ⟨i, hi⟩ := hk ()
    refine ⟨fun h0 => hi (by simp [h0]), h⟩
  · rintro ⟨hz, h⟩
    refine ⟨fun k => ?_, h⟩
    by_contra hc
    push_neg at hc
    exact hz (funext fun p => hc p.2)

variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}

theorem adb_measurable_cxHessian (f : (Fin D → ℂ) → ℝ) (i j : Fin D) :
    Measurable fun y => cxHessian f y i j := by
  have hH := measurable_fderiv ℝ (fderiv ℝ f)
  have hap : ∀ a b : Fin D → ℂ, Measurable fun y => fderiv ℝ (fderiv ℝ f) y a b := fun a b =>
    ((ContinuousLinearMap.apply ℝ ℝ b).continuous.comp
      (ContinuousLinearMap.apply ℝ _ a).continuous).measurable.comp hH
  simp only [cxHessian]
  exact (((Complex.measurable_ofReal.comp ((hap _ _).add (hap _ _))).add
    (measurable_const.mul (Complex.measurable_ofReal.comp ((hap _ _).sub (hap _ _))))).div_const 4)


theorem adb_measurable_maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) : Measurable (maDensity φ) := by
  have hcx : ∀ k i j, Measurable fun z => cxHessian (φ k) z i j := fun k i j =>
    adb_measurable_cxHessian (φ k) i j
  unfold maDensity mixedDisc
  simp only [Matrix.det_apply, Matrix.sum_apply]
  refine measurable_const.mul (Complex.measurable_re.comp (measurable_const.mul
    (Finset.measurable_sum _ fun S _ => measurable_const.mul
      (Finset.measurable_sum _ fun σ _ => (Finset.measurable_prod _ fun i _ =>
        Finset.measurable_sum _ fun k _ => hcx k _ _).const_smul _))))

def IsConeSetB (s : Set (Ix κ → ℂ)) : Prop :=
  ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → (c • z ∈ s ↔ z ∈ s)


theorem IsConeSetB.inter {s t : Set (Ix κ → ℂ)} (hs : IsConeSetB s) (ht : IsConeSetB t) :
    IsConeSetB (s ∩ t) := fun c z hc => by
  simp only [Set.mem_inter_iff, hs c z hc, ht c z hc]

theorem IsConeSetB.compl {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) : IsConeSetB sᶜ := fun c z hc => by
  simp only [Set.mem_compl_iff, hs c z hc]

theorem IsConeSetB.iInter {ι : Sort*} {s : ι → Set (Ix κ → ℂ)} (hs : ∀ i, IsConeSetB (s i)) :
    IsConeSetB (⋂ i, s i) := fun c z hc => by
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => hs i c z hc

theorem IsConeSetB.disjointed {s : ℕ → Set (Ix κ → ℂ)} (hs : ∀ i, IsConeSetB (s i)) (n : ℕ) :
    IsConeSetB (disjointed s n) := by
  rw [disjointed_eq_inter_compl]
  exact (hs n).inter (IsConeSetB.iInter fun i => IsConeSetB.iInter fun _ => (hs i).compl)

theorem IsConeSetB.indicator {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) {f : (Ix κ → ℂ) → ℝ}
    (hf : IsDegZero f) : IsDegZero (s.indicator f) := fun c z hc => by
  show s.indicator f (c • z) = s.indicator f z
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem ((hs c z hc).2 h), Set.indicator_of_mem h, hf c z hc]
  · rw [Set.indicator_of_notMem (fun h' => h ((hs c z hc).1 h')), Set.indicator_of_notMem h]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
