import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint CompatibleChartOperations

noncomputable section

def appendCLE (e e' : ℕ) : ((Fin e → ℂ) × (Fin e' → ℂ)) ≃L[ℂ] (Fin (e + e') → ℂ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin e) (Fin e') ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)).toContinuousLinearEquiv

def prodChart {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    OpenPartialHomeomorph (X × Y) (Fin (e + e') → ℂ) :=
  ((A.chart j).prod (B.chart k)).trans (appendCLE e e').toHomeomorph.toOpenPartialHomeomorph

section ProdChart

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)

theorem prodChart_symm_apply (z : Fin (e + e') → ℂ) :
    (prodChart A B j k).symm z = ((A.chart j).symm ((appendCLE e e').symm z).1,
      (B.chart k).symm ((appendCLE e e').symm z).2) := rfl

theorem prodChart_source :
    (prodChart A B j k).source = (A.chart j).source ×ˢ (B.chart k).source := by
  simp [prodChart]

theorem mem_prodChart_target (z : Fin (e + e') → ℂ) :
    z ∈ (prodChart A B j k).target ↔
      ((appendCLE e e').symm z).1 ∈ (A.chart j).target ∧
        ((appendCLE e e').symm z).2 ∈ (B.chart k).target := by
  simp [prodChart]

end ProdChart

section ProdChart2

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

theorem prodChart_holo (j j' : Fin A.n) (k k' : Fin B.n) :
    AnalyticOnNhd ℂ (prodChart A B j' k' ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (prodChart A B j' k').source) := by
  intro z ⟨ht, hs⟩
  rw [mem_prodChart_target] at ht
  rw [Set.mem_preimage, prodChart_source, prodChart_symm_apply] at hs
  have h1 := A.holo j j' _ ⟨ht.1, hs.1⟩
  have h2 := B.holo k k' _ ⟨ht.2, hs.2⟩
  have hF : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).1) z :=
    ((ContinuousLinearMap.fst ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have hS : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).2) z :=
    ((ContinuousLinearMap.snd ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have hp : AnalyticAt ℂ (fun z => ((A.chart j' ∘ (A.chart j).symm) ((appendCLE e e').symm z).1,
      (B.chart k' ∘ (B.chart k).symm) ((appendCLE e e').symm z).2)) z :=
    (h1.comp_of_eq hF rfl).prod (h2.comp_of_eq hS rfl)
  exact (appendCLE e e').analyticAt _ |>.comp hp

theorem prodChart_holo_fst (j : Fin A.n) (k : Fin B.n) (l : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart l ∘ Prod.fst ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (Prod.fst ⁻¹' (A.chart l).source)) := by
  intro z ⟨ht, hs⟩
  rw [mem_prodChart_target] at ht
  rw [Set.mem_preimage, Set.mem_preimage, prodChart_symm_apply] at hs
  have h1 := A.holo j l _ ⟨ht.1, hs⟩
  have hF : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).1) z :=
    ((ContinuousLinearMap.fst ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have := h1.comp_of_eq hF rfl
  exact this

theorem prodChart_holo_snd (j : Fin A.n) (k : Fin B.n) (l : Fin B.n) :
    AnalyticOnNhd ℂ (B.chart l ∘ Prod.snd ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (Prod.snd ⁻¹' (B.chart l).source)) := by
  intro z ⟨ht, hs⟩
  rw [mem_prodChart_target] at ht
  rw [Set.mem_preimage, Set.mem_preimage, prodChart_symm_apply] at hs
  have h1 := B.holo k l _ ⟨ht.2, hs⟩
  have hS : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).2) z :=
    ((ContinuousLinearMap.snd ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have := h1.comp_of_eq hS rfl
  exact this

end ProdChart2

def prodAtlas {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) : FinHolAtlas (e + e') (X × Y) where
  n := A.n * B.n
  chart i := prodChart A B (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  cover := by
    intro x
    obtain ⟨j, hj⟩ := A.cover x.1
    obtain ⟨k, hk⟩ := B.cover x.2
    refine ⟨finProdFinEquiv (j, k), ?_⟩
    simp only [Equiv.symm_apply_apply, prodChart_source]
    exact ⟨hj, hk⟩
  holo := fun i i' => prodChart_holo A B _ _ _ _

theorem prodAtlas_holoMap_fst {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) : HoloMap (prodAtlas A B) A Prod.fst :=
  ⟨continuous_fst, fun _ l => prodChart_holo_fst A B _ _ l⟩

theorem prodAtlas_holoMap_snd {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) : HoloMap (prodAtlas A B) B Prod.snd :=
  ⟨continuous_snd, fun _ l => prodChart_holo_snd A B _ _ l⟩

section Pull

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

end Pull

def LocPot.pr1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (P : LocPot X) :
    LocPot (X × Y) :=
  P.pullback Prod.fst continuous_fst

def LocPot.pr2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (P : LocPot Y) :
    LocPot (X × Y) :=
  P.pullback Prod.snd continuous_snd

open scoped Classical in

def openAtlas {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    FinHolAtlas b U where
  n := 1
  chart _ :=
    { toFun := Subtype.val
      invFun := fun y => if h : y ∈ U then ⟨y, h⟩ else ⟨hne.some, hne.some_mem⟩
      source := Set.univ
      target := U
      map_source' := fun x _ => x.2
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun x _ => by simp [x.2]
      right_inv' := fun y hy => by simp [hy]
      open_source := isOpen_univ
      open_target := hU
      continuousOn_toFun := continuous_subtype_val.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : (U.domRestrict fun y => if h : y ∈ U then (⟨y, h⟩ : U) else ⟨hne.some, hne.some_mem⟩) =
            id := by
          funext y
          simp only [Set.domRestrict_apply, dif_pos y.2, id]
        rw [this]
        exact continuous_id }
  cover := fun _ => ⟨0, Set.mem_univ _⟩
  holo := by
    intro j k z ⟨hz, _⟩
    refine analyticAt_id.congr ?_
    filter_upwards [hU.mem_nhds hz] with y hy
    simp [hy]

def p1p1 : FinHolAtlas 2 (OnePoint ℂ × OnePoint ℂ) := prodAtlas p1 p1

open scoped Classical in

def diagSec (x y : OnePoint ℂ × OnePoint ℂ) : ℂ :=
  if x.1 = ∞ then
    (if x.2 = ∞ then crd1 y.1 - crd1 y.2 else crd1 y.1 * crd0 y.2 - 1)
  else
    (if x.2 = ∞ then 1 - crd0 y.1 * crd1 y.2 else crd0 y.2 - crd0 y.1)

end

end ReciprocityTheory.AnForm.M
end

section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

@[simp] theorem appendCLE_apply_castAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e) :
    appendCLE e e' (u, v) (Fin.castAdd e' i) = u i := by
  simp [appendCLE]

@[simp] theorem appendCLE_apply_natAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e') :
    appendCLE e e' (u, v) (Fin.natAdd e i) = v i := by
  simp [appendCLE]

theorem appendCLE_symm_apply (y : Fin (e + e') → ℂ) :
    (appendCLE e e').symm y = (fun i => y (Fin.castAdd e' i), fun i => y (Fin.natAdd e i)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

def pr1L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)

def pr2L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e' → ℂ) :=
  (ContinuousLinearMap.snd ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)

theorem firstProjection_apply (y : Fin (e + e') → ℂ) : (pr1L y : Fin e → ℂ) = ((appendCLE e e').symm y).1 := rfl
theorem secondProjection_apply (y : Fin (e + e') → ℂ) : (pr2L y : Fin e' → ℂ) = ((appendCLE e e').symm y).2 := rfl

@[simp] theorem firstProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e) :
    (pr1L y : Fin e → ℂ) i = y (Fin.castAdd e' i) := by
  rw [firstProjection_apply, appendCLE_symm_apply]

@[simp] theorem secondProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e') :
    (pr2L y : Fin e' → ℂ) i = y (Fin.natAdd e i) := by
  rw [secondProjection_apply, appendCLE_symm_apply]

def J1 (e e' : ℕ) : Matrix (Fin e) (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.castAdd e' a then 1 else 0

def J2 (e e' : ℕ) : Matrix (Fin e') (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.natAdd e a then 1 else 0

theorem natAdd_ne_castAdd' (a : Fin e) (b : Fin e') : (Fin.natAdd e b : Fin (e + e')) ≠ Fin.castAdd e' a := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem castAdd_ne_natAdd' (a : Fin e) (b : Fin e') : (Fin.castAdd e' a : Fin (e + e')) ≠ Fin.natAdd e b :=
  fun h => natAdd_ne_castAdd' a b h.symm

theorem block_eq (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    (J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e' =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M1 0 0 M2) := by
  ext k l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
    refine Fin.addCases (fun c => ?_) (fun d => ?_) l <;>
    simp [Matrix.mul_apply, J1, J2, Matrix.fromBlocks, ite_mul, mul_ite, Finset.sum_ite_eq, natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem det_block (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    ((J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e').det = M1.det * M2.det := by
  rw [block_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def finsetAppendEquiv (e e' : ℕ) : Finset (Fin e) × Finset (Fin e') ≃ Finset (Fin (e + e')) where
  toFun p := p.1.map (Fin.castAddEmb e') ∪ p.2.map (Fin.natAddEmb e)
  invFun S := (Finset.univ.filter (fun a => Fin.castAdd e' a ∈ S),
    Finset.univ.filter (fun b => Fin.natAdd e b ∈ S))
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> ext a <;> simp [natAdd_ne_castAdd', castAdd_ne_natAdd']
  right_inv S := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
      simp [natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem pot_contDiffAt {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x ∈ 𝓝 z :=
    ((A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hz, hzU⟩
  exact ((hP.1 x k).contDiffAt hmem).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

end

end ReciprocityTheory.AnForm.M
end

section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory Filter Topology FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem pp_source (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    (prodChart A B j k).source = (A.chart j).source ×ˢ (B.chart k).source := by
  simp [prodChart]

theorem pp_target (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    (prodChart A B j k).target =
      (appendCLE e e').symm ⁻¹' ((A.chart j).target ×ˢ (B.chart k).target) := by
  simp [prodChart]

theorem pp_mem_target (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)
    (y : Fin (e + e') → ℂ) :
    y ∈ (prodChart A B j k).target ↔ pr1L y ∈ (A.chart j).target ∧ pr2L y ∈ (B.chart k).target := by
  rw [pp_target]; rfl

theorem contDiffOn_comp_pr1L {f : (Fin e → ℂ) → ℝ} {s : Set (Fin e → ℂ)} {t : Set (Fin (e + e') → ℂ)}
    (hf : ContDiffOn ℝ ∞ f s) (ht : ∀ y ∈ t, pr1L y ∈ s) : ContDiffOn ℝ ∞ (fun y => f (pr1L y)) t :=
  hf.comp ((pr1L (e := e) (e' := e')).contDiff.restrict_scalars ℝ).contDiffOn ht

theorem contDiffOn_comp_pr2L {f : (Fin e' → ℂ) → ℝ} {s : Set (Fin e' → ℂ)} {t : Set (Fin (e + e') → ℂ)}
    (hf : ContDiffOn ℝ ∞ f s) (ht : ∀ y ∈ t, pr2L y ∈ s) : ContDiffOn ℝ ∞ (fun y => f (pr2L y)) t :=
  hf.comp ((pr2L (e := e) (e' := e')).contDiff.restrict_scalars ℝ).contDiffOn ht

theorem tsupport_prod_mul_subset (a : X → ℝ) (b : Y → ℝ) :
    tsupport (fun p : X × Y => a p.1 * b p.2) ⊆ tsupport a ×ˢ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).prod (isClosed_tsupport b))
  intro p hp
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
  exact ⟨subset_tsupport _ hp.1, subset_tsupport _ hp.2⟩

def prodPartition (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : ChartPartition A)
    (Q : ChartPartition B) : ChartPartition (prodAtlas A B) where
  χ i p := P.χ (finProdFinEquiv.symm i).1 p.1 * Q.χ (finProdFinEquiv.symm i).2 p.2
  smooth i i' := by
    show ContDiffOn ℝ ∞ (fun y => P.χ (finProdFinEquiv.symm i).1
        ((A.chart (finProdFinEquiv.symm i').1).symm (pr1L y)) *
      Q.χ (finProdFinEquiv.symm i).2 ((B.chart (finProdFinEquiv.symm i').2).symm (pr2L y))) _
    refine (contDiffOn_comp_pr1L (P.smooth _ _) ?_).mul (contDiffOn_comp_pr2L (Q.smooth _ _) ?_)
    · exact fun y hy => ⟨((pp_mem_target A B (finProdFinEquiv.symm i').1
        (finProdFinEquiv.symm i').2 y).1 hy.1).1, trivial⟩
    · exact fun y hy => ⟨((pp_mem_target A B (finProdFinEquiv.symm i').1
        (finProdFinEquiv.symm i').2 y).1 hy.1).2, trivial⟩
  nonneg i p := mul_nonneg (P.nonneg _ _) (Q.nonneg _ _)
  tsupport_subset i := by
    refine (tsupport_prod_mul_subset _ _).trans ?_
    show _ ⊆ (prodChart A B _ _).source
    rw [pp_source]
    exact Set.prod_mono (P.tsupport_subset _) (Q.tsupport_subset _)
  sum_eq_one p := by
    show ∑ j : Fin (A.n * B.n), P.χ (finProdFinEquiv.symm j).1 p.1 * Q.χ (finProdFinEquiv.symm j).2 p.2 = 1
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum, P.sum_eq_one, Q.sum_eq_one, one_mul]

theorem isPotential_first_projection (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : LocPot X)
    (hP : IsPotential A P) : IsPotential (prodAtlas A B) (P.pr1 (Y := Y)) :=
  isPotentialPullback A (prodAtlas A B) Prod.fst (prodAtlas_holoMap_fst A B) P hP

theorem isPotential_second_projection (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (Q : LocPot Y)
    (hQ : IsPotential B Q) : IsPotential (prodAtlas A B) (Q.pr2 (X := X)) :=
  isPotentialPullback B (prodAtlas A B) Prod.snd (prodAtlas_holoMap_snd A B) Q hQ

def onePartition {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ChartPartition (openAtlas U hU hne) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun x _ => Set.mem_univ x
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

instance openAtlas_subsingleton {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    Subsingleton (Fin (openAtlas U hU hne).n) :=
  inferInstanceAs (Subsingleton (Fin 1))

end

end ReciprocityTheory.AnForm.M
end
