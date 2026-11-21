import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def HermLine.ConjInvariant (A : HermLine n) : Prop :=
  ∀ z : Cone n ℂ, BlockNonzero z → A.metric (fun k i ↦ starRingEnd ℂ (z k i)) = A.metric z


def HermLine.ofGeo (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N) : HermLine n where
  deg := N.a
  metric z := N.h (flatCone z)
  metric_pos z hz := N.pos _ ((blockNonzero_unflatCone_iff _).mp hz)
  metric_smul c z hc _ := N.smul c (flatCone z) hc
  metric_smooth := by
    have hu : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ flatCone z) :=
      contDiff_pi.2 fun p ↦ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n p.1 + 1) ↦ ℂ) p.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) p.1)).contDiff
    exact hN.comp hu.contDiffOn fun z hz ↦ (blockNonzero_unflatCone_iff _).mp hz

theorem HermLine.toGeo_ofGeo_h (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N)
    {w : Coord n → ℂ} (hw : BlockNonzero (unflatCone w)) : (HermLine.ofGeo N hN).toGeo.h w = N.h w :=
  HermLine.toGeo_h_of_blockNonzero _ hw

namespace ArithVariety

variable (P : ArithVariety n)

def IsSmallFor (A : HermLine n) (t : P.FunField) : Prop :=
  ∀ (p q : MvPolynomial (Coord n) ℤ) (δp δq : ι → ℕ), IsWeightedHomogeneous (coordDeg n) p δp →
    IsWeightedHomogeneous (coordDeg n) q δq → (∀ k, (δp k : ℤ) = δq k + A.deg k) →
    P.mkF p = t * P.mkF q → ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ ‖evalCone z q‖ * A.metric z

structure IsNormalSection (a : ι → ℤ) (t : P.FunField) : Prop where
  degree : P.IsOfDegree a t
  integral : ∀ c, P.IsLive c → t / P.chartPow c a ∈ integralClosure (P.chartRing c) P.FunField

def Reads {Ω : Type} [Field Ω] (y : Coord n → Ω) (a : ι → ℤ) (s : Ω) (t : P.FunField) : Prop :=
  ∀ (g h : MvPolynomial (Coord n) ℤ) (δg δh : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g δg →
    IsWeightedHomogeneous (coordDeg n) h δh → (∀ k, (δg k : ℤ) = δh k + a k) →
    (aeval y g = s * aeval y h ↔ P.mkF g = t * P.mkF h)

end ArithVariety

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

def plusCoord {Ω : Type} (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) : Coord D.extSizes → Ω
  | ⟨none, j⟩ => x' j
  | ⟨some k, i⟩ => y ⟨k, i⟩

def oldFlat {F : Type*} (w : Coord D.extSizes → F) : Coord n → F := fun p ↦ w ⟨some p.1, p.2⟩

structure BlockReading {Ω : Type} [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) : Prop where
  ideal_eq : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y
  ext_eq : D.extIdeal = Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')
  reads : ∀ j, P.Reads y D.deg (x' j) (D.elt j)

def InducesMetric {Ω : Type} [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω)
    (N : Geo.HermLine (blockIdx n)) (Ap : Geo.HermLine (blockIdx D.extSizes)) : Prop :=
  ∀ (j : Fin (D.size + 1)) (g m : MvPolynomial (Coord n) ℤ) (dg dm : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) g dg → Geo.IsMultiHomog (ι := blockIdx n) m dm →
    (∀ k, (dg k : ℤ) = dm k + N.a k) → aeval y g = aeval y m * x' j →
    ∀ z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')),
      ‖z ⟨none, j⟩‖ * ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) m)‖ * N.h (D.oldFlat z) =
        ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) g)‖ * Ap.h z

end AddBlockData

def IsSupSmallBlock {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    (y : Coord n' → Ω) (k₀ : κ) (A : Geo.HermLine (blockIdx n')) (τ : ℕ) (s : Ω) : Prop :=
  ∀ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f (Pi.single k₀ τ) →
    aeval y f = s → ∀ z ∈ Geo.mcPts (ι := blockIdx n') (Geo.mCoordIdeal (ι := blockIdx n') y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤ A.h z ^ τ

def monomialValues {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) : Set Ω :=
  {s | ∃ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧ s = ∏ p, y p ^ μ p}

theorem AddBlockData.oldFlat_mem_mcPts {P : ArithVariety n} (D : AddBlockData P) {Ω : Type} [Field Ω]
    (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (z : Coord D.extSizes → ℂ)
    (hz : z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x'))) :
    D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) := by
  refine ⟨fun k ↦ hz.1 (some k), fun f hf ↦ ?_⟩
  have hmem : D.liftOld f ∈ Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x') := by
    have hf0 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    have key : Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x') (D.liftOld f) =
        rename some (Geo.mConeMap (ι := blockIdx n) y f) := by
      have h : ((Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x')).toRingHom.comp
            (D.liftOld).toRingHom) =
          (rename (R := Ω) (some : ι → Option ι)).toRingHom.comp
            (Geo.mConeMap (ι := blockIdx n) y).toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)
        simp [Geo.mConeMap, AddBlockData.liftOld, AddBlockData.oldCoord, AddBlockData.plusCoord]
      exact congrArg (fun φ : _ →+* _ ↦ φ f) h
    rw [key, hf0, map_zero]
  have h3 := hz.2 _ hmem
  rw [eval_map] at h3 ⊢
  rw [AddBlockData.liftOld, eval₂_rename] at h3
  exact h3

section Examples

variable (n)

omit [Fintype ι] [DecidableEq ι] in

theorem mCoordIdeal_eq_ker {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    Geo.mCoordIdeal (ι := blockIdx n) y =
      RingHom.ker (eval₂Hom (Int.castRingHom (MvPolynomial ι Ω)) fun v : Coord n ↦ C (y v) * X v.1) := by
  ext f
  rw [Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, Geo.mConeMap, aeval_def]
  rfl

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_of_hom {Ω : Type} [Field Ω] (φ : MvPolynomial (Coord n) ℤ →+* Ω)
    (f : MvPolynomial (Coord n) ℤ) : aeval (fun v ↦ φ (X v)) f = φ f := by
  have h : (aeval (fun v ↦ φ (X v)) : _ →ₐ[ℤ] Ω).toRingHom = φ :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp)
  exact congrArg (fun ψ : _ →+* _ ↦ ψ f) h

omit [Fintype ι] [DecidableEq ι] in

theorem mCoordIdeal_of_aeval_injective {Ω : Type} [Field Ω] (y : Coord n → Ω)
    (hy : Function.Injective (aeval y : MvPolynomial (Coord n) ℤ →ₐ[ℤ] Ω)) :
    Geo.mCoordIdeal (ι := blockIdx n) y = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun f hf ↦ hy ?_
  have h1 : (aeval (fun _ : ι ↦ (1 : Ω))).toRingHom.comp
      (Geo.mConeMap (ι := blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp [Geo.mConeMap])
  have h2 := congrArg (fun φ : _ →+* _ ↦ φ f) h1
  have h3 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2, map_zero]

def wholePoint : Coord n → (ArithVariety.whole n).FunField := fun v ↦ (ArithVariety.whole n).mkF (X v)

omit [Fintype ι] in
theorem mCoordIdeal_wholePoint :
    Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n) = ⊥ :=
  mCoordIdeal_of_aeval_injective n _ fun f g h ↦ by
    have hf := aeval_of_hom n (ArithVariety.whole n).mkF f
    have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
    exact ArithVariety.whole_mkF_injective n (hf.symm.trans (h.trans hg))


omit [Fintype ι] in

theorem reads_wholePoint (a : ι → ℤ) (t : (ArithVariety.whole n).FunField) :
    (ArithVariety.whole n).Reads (wholePoint n) a t t := by
  intro g h _ _ _ _ _
  have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
  have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
  exact ⟨fun e ↦ hg.symm.trans (e.trans (congrArg _ hh)),
    fun e ↦ hg.trans (e.trans (congrArg _ hh.symm))⟩

theorem whole_isArithVar (N : ℕ) :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N) (ArithVariety.whole fun _ : Unit ↦ N).ideal (N + 1) :=
  ⟨inferInstance, ArithVariety.isMultiProjPrime _, ArithVariety.isHorizontal _, whole_ringKrullDim N⟩


def unitPoint : Coord (fun _ : Unit ↦ 0) → ℚ := fun _ ↦ 1

theorem mCoordIdeal_unitPoint :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint = ⊥ := by
  rw [mCoordIdeal_eq_ker]
  have h : (eval₂Hom (Int.castRingHom (MvPolynomial Unit ℚ)) fun v : Coord (fun _ : Unit ↦ 0) ↦
      C (unitPoint v) * X v.1) =
      (map (Int.castRingHom ℚ)).comp (rename (Sigma.fst : Coord (fun _ : Unit ↦ 0) → Unit)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp [unitPoint])
  rw [h]
  refine (RingHom.injective_iff_ker_eq_bot _).mp ?_
  refine (map_injective _ Int.cast_injective).comp (rename_injective _ ?_)
  rintro ⟨a, i⟩ ⟨b, j⟩ _
  cases a
  cases b
  have hij : i = j := Subsingleton.elim (α := Fin 1) i j
  rw [hij]

theorem unitPoint_isArithVar :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ 0)
      (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) := by
  rw [mCoordIdeal_unitPoint]
  exact whole_isArithVar 0

theorem unitPoint_birational : Geo.Birational (ι := blockIdx fun _ : Unit ↦ 0) unitPoint := by
  have hC : ∀ a : ℤ, Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ 0)
      (C a : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) 0 := by
    intro a m hm k
    have hm0 : m = 0 := by
      by_contra h0
      exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h0)])
    simp [hm0]
  intro s
  refine ⟨0, C s.num, C (s.den : ℤ), hC _, hC _, ?_, ?_⟩
  · simp
  · have hv : ∀ a : ℤ, aeval unitPoint (C a : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) = (a : ℚ) :=
      fun a ↦ by rw [aeval_C]; simp
    rw [hv, hv]
    push_cast
    exact (Rat.mul_den_eq_num s).symm

theorem form_eq_zero_of_unitPoint {f : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ} {δ : Unit → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ 0) f δ) (h : aeval unitPoint f = 0) : f = 0 := by
  have hm : ∀ m ∈ f.support, m = Finsupp.single ⟨(), 0⟩ (δ ()) := by
    intro m hm
    have h1 := (geoMultiHomog_iff f δ).mpr hf m hm ()
    ext ⟨u, i⟩
    cases u
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) i 0
    subst hi
    have h2 : ∑ i : Fin 1, m ⟨(), i⟩ = m ⟨(), 0⟩ := Fin.sum_univ_one _
    rw [Finsupp.single_eq_same, ← h2]
    exact h1
  by_contra h0
  have hs : f.support = {Finsupp.single ⟨(), 0⟩ (δ ())} := by
    obtain ⟨m, hmem⟩ := Finset.nonempty_of_ne_empty (mt support_eq_empty.mp h0)
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, hm⟩
    rw [← hm m hmem]
    exact hmem
  have hc : coeff (Finsupp.single ⟨(), 0⟩ (δ ())) f ≠ 0 :=
    mem_support_iff.mp (by rw [hs]; exact Finset.mem_singleton_self _)
  rw [aeval_def, eval₂_eq, hs, Finset.sum_singleton] at h
  simp only [unitPoint, one_pow, Finset.prod_const_one, mul_one] at h
  have h3 : ((coeff (Finsupp.single ⟨(), 0⟩ (δ ())) f : ℤ) : ℚ) = 0 := by simpa using h
  exact hc (by exact_mod_cast h3)



omit [Fintype ι] [DecidableEq ι] in
theorem monomialValues_zero [Fintype ι] {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    monomialValues y 0 = {1} := by
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have h0 : ∀ p, μ p = 0 := fun p ↦ by
      have := hμ p.1
      rw [Pi.zero_apply, Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  · rintro rfl
    exact ⟨0, fun k ↦ by simp, by simp⟩

omit [Fintype ι] [DecidableEq ι] in

theorem span_monomialValues_zero [Fintype ι] {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    Submodule.span ℤ (Set.range fun _ : Fin (0 + 1) ↦ (1 : Ω)) =
      Submodule.span ℤ (monomialValues y 0) := by
  rw [monomialValues_zero, Set.range_const]


omit [Fintype ι] in

theorem blockLine_conjInvariant [Fintype ι] (k₀ : ι) : (blockLine n k₀).ConjInvariant :=
  fun z _ ↦ vectorL2Norm_conj (z k₀)



omit [Fintype ι] in

theorem isSmallH_one_wholePoint [Fintype ι] (N : Geo.HermLine (blockIdx n)) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n)) (wholePoint n) N 0 1 := by
  intro dg dh g h z _ _ _ hy _
  have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
  have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
  have hgh : g = h := ArithVariety.whole_mkF_injective n (by
    rw [one_mul] at hy; exact hg.symm.trans (hy.trans hh))
  subst hgh
  simp




end Examples

end

end GroundTheory.Heights₂.Heights
