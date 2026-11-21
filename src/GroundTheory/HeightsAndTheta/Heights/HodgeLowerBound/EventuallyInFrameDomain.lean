import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Values

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def IsValueAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) (v : ℂ) : Prop :=
  ∃ (d : κ → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧
    aeval y g = a * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
    eval z (map (Int.castRingHom ℂ) g) = v * eval z (map (Int.castRingHom ℂ) h)

def RegularAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ v, IsValueAt y a z v

open Classical in

def valAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) : ℂ :=
  if h : RegularAt y a z then h.choose else 0

end Values

section Frames

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
  {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def IsLocSection (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (z : (Σ k, ι k) → ℂ) (e : E) : Prop :=
  ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∃ (m : ℕ) (a : Fin m → Ω) (s : Fin m → E),
    (∀ l, s l ∈ W.lat c) ∧ (∀ l, RegularAt y (a l) z) ∧ e = ∑ l, a l • s l

def IsFrameAt (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (z : (Σ k, ι k) → ℂ) (b : Fin N → E) : Prop :=
  (∀ q, IsLocSection y W z (b q)) ∧
    ∀ e, IsLocSection y W z e → ∃ a : Fin N → Ω, (∀ q, RegularAt y (a q) z) ∧ e = ∑ q, a q • b q

open scoped ComplexOrder in

structure HermMetricOn (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (U : Set ((Σ k, ι k) → ℂ)) where

  H : ((Σ k, ι k) → ℂ) → (Fin N → E) → Matrix (Fin N) (Fin N) ℂ

  posDef : ∀ z ∈ U, ∀ b, IsFrameAt y W z b → (H z b).PosDef

  frameChange : ∀ z ∈ U, ∀ (b : Fin N → E) (g : Matrix (Fin N) (Fin N) Ω) (gz : Matrix (Fin N) (Fin N) ℂ),
    IsFrameAt y W z b → (∀ p q, IsValueAt y (g p q) z (gz p q)) →
    IsFrameAt y W z (fun q => ∑ p, g p q • b p) →
    H z (fun q => ∑ p, g p q • b p) = gz.conjTranspose * H z b * gz

  scale : ∀ z ∈ U, ∀ s : κ → ℂ, (∀ k, s k ≠ 0) → (fun p => s p.1 * z p) ∈ U → ∀ b,
    IsFrameAt y W z b → H (fun p => s p.1 * z p) b = H z b

  conj : ∀ z ∈ U, (fun p => starRingEnd ℂ (z p)) ∈ U → ∀ b, IsFrameAt y W z b →
    H (fun p => starRingEnd ℂ (z p)) b = (H z b).map (starRingEnd ℂ)

  smooth : ∀ (m : ℕ) (O : Set (Fin m → ℂ)) (γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ), IsOpen O →
    AnalyticOnNhd ℂ γ O → (∀ w ∈ O, γ w ∈ U) → ∀ w ∈ O, ∀ b, IsFrameAt y W (γ w) b →
      ∀ p q, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => H (γ w') b p q) w

end Frames

section Charts

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

structure SncChart (y : (Σ k, ι k) → Ω) (bd : Ideal (MRing ι)) (n : ℕ) where

  c : ∀ k, ι k

  φ : (Fin n → ℂ) → (Σ k, ι k) → ℂ

  kb : ℕ
  kb_le : kb ≤ n

  z : Fin n → Ω
  mem : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, φ w ∈ mcPts (mCoordIdeal y)
  normalised : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ k, φ w ⟨k, c k⟩ = 1
  holo : AnalyticOnNhd ℂ φ (Metric.ball 0 1)
  coord : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, IsValueAt y (z i) (φ w) (w i)
  isOpen_image : ∃ O : Set ((Σ k, ι k) → ℂ), IsOpen O ∧
    φ '' Metric.ball 0 1 = O ∩ {x | x ∈ mcPts (mCoordIdeal y) ∧ ∀ k, x ⟨k, c k⟩ = 1}
  boundary : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1,
    φ w ∈ mcPts bd ↔ ∃ i : Fin n, (i : ℕ) < kb ∧ w i = 0

def lwP₂ {n : ℕ} (kb : ℕ) (w : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < kb then Real.log (1 / ‖w i‖ ^ 2) else 0

end Charts

section Subbundles

variable {Ω : Type*} [Field Ω] {τ : Type*} {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def IsSubbundle {x : τ → Ω} (W : ChartBundle ℤ x N E) (V : Submodule Ω E) (r : ℕ) : Prop :=
  r ≤ N ∧ ∀ c, x c ≠ 0 → ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ x c) ∧
    (∀ l, a l ∈ chartRing ℤ x c) ∧ ∑ l, a l * f l = 1 ∧ ∀ l, ∃ b : Fin N → E, LinearIndependent Ω b ∧
      (∀ e, (∃ n : ℕ, f l ^ n • e ∈ W.lat c) ↔
        ∃ a' : Fin N → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a' q ∈ chartRing ℤ x c) ∧ e = ∑ q, a' q • b q) ∧
      Submodule.span Ω (b '' {q | (q : ℕ) < r}) = V

end Subbundles

section Lines

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

def IsAmpleOn (P : Ideal (MRing ι)) (a : κ → ℤ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ NefOnFibres P (fun k => (m : ℤ) * a k - 1)

structure IsVerticalCartier (P : Ideal (MRing ι)) (p : ℕ) (b : κ → ℤ) (f g : MRing ι) : Prop where
  degrees : ∃ bf bg : κ → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  unit_off_special : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
    (C (p : ℤ) : MRing ι) ∉ W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

end Lines

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Homog

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_C (c : ℤ) : IsMultiHomog (C c : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isMultiHomog_prod {σ : Type} (s : Finset σ) (f : σ → MRing ι) (d : σ → κ → ℕ)
    (h : ∀ a ∈ s, IsMultiHomog (f a) (d a)) : IsMultiHomog (∏ a ∈ s, f a) (∑ a ∈ s, d a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ProjLine.isMultiHomog_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ProjLine.mhMul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem isMultiHomog_chartMonomial (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have h := isMultiHomog_prod (Finset.univ : Finset κ) (fun k => (X ⟨k, c k⟩ : MRing ι))
    (fun k => fun k1 => if k1 = k then 1 else 0) (fun k _ => ProjLine.isMultiHomog_X ⟨k, c k⟩)
  have hs : (∑ k : κ, (fun k1 : κ => if k1 = k then 1 else 0 : κ → ℕ)) = fun _ => 1 := by
    funext k1
    simp [Finset.sum_apply]
  rwa [hs] at h

end Homog

section Values

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem mem_mCoordIdeal_of_aeval {f : MRing ι} {d : κ → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]

theorem IsValueAt.unique {a : Ω} {v v' : ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (h : IsValueAt y a z v) (h' : IsValueAt y a z v') : v = v' := by
  obtain ⟨d, g, h1, hg, hh, hy, hyg, hz1, hzg⟩ := h
  obtain ⟨d', g', h1', hg', hh', hy', hyg', hz1', hzg'⟩ := h'
  have hm : IsMultiHomog (g * h1' - g' * h1) (d + d') := by
    rw [sub_eq_add_neg]
    refine ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg ?_)
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  have h0 : aeval y (g * h1' - g' * h1) = 0 := by
    rw [map_sub, map_mul, map_mul, hyg, hyg']
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval hm h0)
  rw [map_sub, map_mul, map_mul, eval_sub, eval_mul, eval_mul, hzg, hzg', sub_eq_zero] at hz0
  have hne : eval z (map (Int.castRingHom ℂ) h1) * eval z (map (Int.castRingHom ℂ) h1') ≠ 0 :=
    mul_ne_zero hz1 hz1'
  apply mul_right_cancel₀ hne
  linear_combination hz0

theorem valAt_eq {a : Ω} {v : ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (h : IsValueAt y a z v) :
    valAt y a z = v := by
  have hr : RegularAt y a z := ⟨v, h⟩
  rw [valAt, dif_pos hr]
  exact IsValueAt.unique hz hr.choose_spec h

theorem RegularAt.isValueAt {a : Ω} (hz : z ∈ mcPts (mCoordIdeal y)) (h : RegularAt y a z) :
    IsValueAt y a z (valAt y a z) := by
  obtain ⟨v, hv⟩ := h
  rwa [valAt_eq hz hv]

theorem IsValueAt.mul {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a * b) z (v * w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  refine ⟨d + d', g * g', h * h', ProjLine.mhMul hg hg', ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_mul, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.add {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a + b) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  have hd : IsMultiHomog (g' * h) (d + d') := by
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  refine ⟨d + d', g * h' + g' * h, h * h', ProjLine.mhAdd (ProjLine.mhMul hg hh') hd,
    ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_add, map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add, map_mul, eval_add, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.neg {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) : IsValueAt y (-a) z (-v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, -g, h, ProjLine.mhNeg hg, hh, hy, ?_, hz, ?_⟩
  · rw [map_neg, hyg]
    ring
  · rw [map_neg, eval_neg, hzg]
    ring

theorem isValueAt_intCast (n : ℤ) : IsValueAt y (n : Ω) z (n : ℂ) := by
  refine ⟨0, C n, 1, isMultiHomog_C n, ProjLine.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_one : IsValueAt y (1 : Ω) z 1 := by
  simpa using isValueAt_intCast (y := y) (z := z) 1

theorem isValueAt_zero : IsValueAt y (0 : Ω) z 0 := by
  simpa using isValueAt_intCast (y := y) (z := z) 0

theorem IsValueAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} {v : σ → ℂ}
    (h : ∀ i ∈ s, IsValueAt y (a i) z (v i)) : IsValueAt y (∑ i ∈ s, a i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem RegularAt.mul {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a * b) z :=
  ⟨_, ha.choose_spec.mul hb.choose_spec⟩

theorem RegularAt.add {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a + b) z :=
  ⟨_, ha.choose_spec.add hb.choose_spec⟩

theorem RegularAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} (h : ∀ i ∈ s, RegularAt y (a i) z) :
    RegularAt y (∑ i ∈ s, a i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using isValueAt_zero⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fintype κ] [∀ k, Fintype (ι k)] in

theorem eval_conj (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => starRingEnd ℂ (z p)) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem IsValueAt.conj {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => starRingEnd ℂ (z p)) (starRingEnd ℂ v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_conj]
    exact (map_ne_zero _).2 hz
  · rw [eval_conj, eval_conj, hzg, map_mul]

theorem IsValueAt.smul {a : Ω} {v : ℂ} (s : κ → ℂ) (hs : ∀ k, s k ≠ 0) (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => s p.1 * z p) v := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)) hz
  · rw [eval_smul_homog h d hh, eval_smul_homog g d hg, hzg]
    ring

theorem regularAt_of_mem_chartRing (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ chartRing ℤ (NumbersDVR.segreVec y) c) :
    RegularAt y a z := by
  have hden : NumbersDVR.segreVec y c ≠ 0 := by
    intro h0
    have hm := mem_mCoordIdeal_of_aeval (y := y) (isMultiHomog_chartMonomial c)
      (by simpa [NumbersDVR.segreVec] using h0)
    have := hz.2 _ hm
    simp only [map_prod, map_X, eval_prod, eval_X] at this
    exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    have hz0 : eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))) ≠ 0 := by
      simp only [map_prod, map_X, eval_prod, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
    refine ⟨eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c' k⟩ : MRing ι))) /
      eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))), fun _ => 1,
      ∏ k, (X ⟨k, c' k⟩ : MRing ι), ∏ k, (X ⟨k, c k⟩ : MRing ι), isMultiHomog_chartMonomial c',
      isMultiHomog_chartMonomial c, ?_, ?_, hz0, ?_⟩
    · simpa [NumbersDVR.segreVec] using hden
    · simp only [map_prod, aeval_X]
      show NumbersDVR.segreVec y c' = NumbersDVR.segreVec y c' / NumbersDVR.segreVec y c *
        NumbersDVR.segreVec y c
      rw [div_mul_cancel₀ _ hden]
    · rw [div_mul_cancel₀ _ hz0]
  | algebraMap r =>
    exact ⟨r, by simpa using isValueAt_intCast (y := y) (z := z) r⟩
  | add a b _ _ ha hb => exact ha.add hb
  | mul a b _ _ ha hb => exact ha.mul hb

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

namespace HermMetricEq

theorem isValueAt_iff {s : Ω} {v : ℂ} :
    IsValueAt y s z v ↔ IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y s z v := by
  constructor
  · rintro ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩
    exact ⟨d, g, h, hg, hh, hy, hyg, hz, by rw [hv, div_mul_cancel₀ _ hz]⟩
  · rintro ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩
    exact ⟨d, g, h, hg, hh, hy, hyg, hz, by rw [hv, mul_div_cancel_right₀ _ hz]⟩

theorem regularAt_inv {f : Ω} (hf0 : f ≠ 0) (hf : IsUnitAt y f z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y f⁻¹ z := by
  obtain ⟨v, ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩, hv0⟩ := hf
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hv
    exact hv0 hv
  have hgy : aeval y g ≠ 0 := by
    rw [hyg]
    exact mul_ne_zero hf0 hy
  refine ⟨v⁻¹, d, h, g, hh, hg, hgy, ?_, hgz, ?_⟩
  · rw [hyg, inv_mul_cancel_left₀ hf0]
  · rw [hv, inv_div, div_mul_cancel₀ _ hgz]

theorem regularAt_pow {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) (n : ℕ) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (a ^ n) z := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨1, IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one⟩
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul ha

theorem segreCoord_ne_zero (hz : z ∈ mcPts (mCoordIdeal y)) {c : (k : K) → ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) : segreCoord y c ≠ 0 := by
  intro h0
  have hm := IndefiniteRowSideFullHecke.LowerBoundFree.mem_mCoordIdeal_of_aeval (y := y)
    (IndefiniteRowSideFullHecke.LowerBoundFree.isMultiHomog_chartMonomial c) (by simpa [segreCoord] using h0)
  have := hz.2 _ hm
  simp only [map_prod, map_X, eval_X] at this
  exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this

variable {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem isFrameAt_of_isFrameOver {W : ChartBundle ℤ (segreCoord y) N E} {c : (k : K) → ι k} {f : Ω}
    {b : Fin N → E} (hb : IsFrameOver y W c f b) (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : InFrameDomain y c f z) : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b := by
  obtain ⟨hx, -, hf0, -, hiff⟩ := hb
  have hfi : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y f⁻¹ z := regularAt_inv hf0 hd.2
  have hloc : ∀ a : Ω, (∃ n : ℕ, f ^ n * a ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z := by
    rintro a ⟨n, hn⟩
    have h1 := (regularAt_pow hfi n).mul (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have hsec : ∀ c' : (k : K) → ι k, (∀ k, z ⟨k, c' k⟩ ≠ 0) → ∀ s ∈ W.lat c',
      ∃ a : Fin N → Ω, (∀ q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (a q) z) ∧ s = ∑ q, a q • b q := by
    intro c' hc' s hs
    have hx' := segreCoord_ne_zero hz hc'
    obtain ⟨m, hm⟩ := W.overlap c' c hx' hx s hs
    obtain ⟨a, ha, hae⟩ := (hiff _).1 ⟨0, by rwa [pow_zero, one_smul]⟩
    have hr : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y ((segreCoord y c / segreCoord y c') ^ m) z :=
      regularAt_pow (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc'
        (Algebra.subset_adjoin ⟨c, rfl⟩)) m
    refine ⟨fun q => (segreCoord y c / segreCoord y c') ^ m * a q,
      fun q => hr.mul (hloc _ (ha q)), ?_⟩
    have hone : (segreCoord y c / segreCoord y c') ^ m * (segreCoord y c' / segreCoord y c) ^ m = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (segreCoord y c) (segreCoord y c'),
        div_self (mul_ne_zero hx' hx), one_pow]
    calc s = ((segreCoord y c / segreCoord y c') ^ m * (segreCoord y c' / segreCoord y c) ^ m) • s := by
          rw [hone, one_smul]
      _ = (segreCoord y c / segreCoord y c') ^ m • ∑ q, a q • b q := by rw [mul_smul, hae]
      _ = ∑ q, ((segreCoord y c / segreCoord y c') ^ m * a q) • b q := by
          rw [Finset.smul_sum]
          simp only [mul_smul]
  refine ⟨fun q => ?_, fun e he => ?_⟩
  · have hex : ∃ n : ℕ, f ^ n • b q ∈ W.lat c := by
      refine (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · rw [pow_zero, one_mul]
        rcases eq_or_ne q' q with rfl | h
        · rw [Pi.single_eq_same]
          exact one_mem _
        · rw [Pi.single_eq_of_ne h]
          exact zero_mem _
      · simp [Pi.single_apply, ite_smul]
    obtain ⟨n, hn⟩ := hex
    refine ⟨c, hd.1, 1, fun _ => (f ^ n)⁻¹, fun _ => f ^ n • b q, fun _ => hn, fun _ => ?_, ?_⟩
    · rw [← inv_pow]
      exact regularAt_pow hfi n
    · rw [Fin.sum_univ_one]
      exact (inv_smul_smul₀ (pow_ne_zero _ hf0) _).symm
  · obtain ⟨c', hc', m, a, s, hs, ha, rfl⟩ := he
    choose α hα hαe using fun l => hsec c' hc' (s l) (hs l)
    refine ⟨fun q => ∑ l, a l * α l q,
      fun q => IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt.sum _ fun l _ => (ha l).mul (hα l q), ?_⟩
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hαe l, Finset.smul_sum]

theorem coeff_unique {b : Fin N → E} (hli : LinearIndependent Ω b) {S S' : Matrix (Fin N) (Fin N) Ω}
    (h : ∀ q, ∑ p, S p q • b p = ∑ p, S' p q • b p) : S = S' := by
  ext p q
  exact Fintype.linearIndependent_iffₛ.1 hli (fun p => S p q) (fun p => S' p q) (h q) p

theorem exists_coeff {W : ChartBundle ℤ (segreCoord y) N E} {c : (k : K) → ι k} {f : Ω}
    {b : Fin N → E} (hb : IsFrameOver y W c f b) (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : InFrameDomain y c f z) {b' : Fin N → E}
    (hb' : ∀ q, IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z (b' q)) :
    ∃ S : Matrix (Fin N) (Fin N) Ω, (∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z) ∧
      ∀ q, b' q = ∑ p, S p q • b p := by
  choose a ha hae using fun q => (isFrameAt_of_isFrameOver hb hz hd).2 _ (hb' q)
  exact ⟨Matrix.of fun p q => a q p, fun p q => ha q p, fun q => hae q⟩

def valM (y : (Σ k, ι k) → Ω) (S : Matrix (Fin N) (Fin N) Ω) (z : (Σ k, ι k) → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun p q => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y (S p q) z

theorem isValueAt_mul {S T : Matrix (Fin N) (Fin N) Ω} {Sz Tz : Matrix (Fin N) (Fin N) ℂ}
    (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (S p q) z (Sz p q))
    (hT : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (T p q) z (Tz p q)) (p q : Fin N) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y ((S * T) p q) z ((Sz * Tz) p q) := by
  simp only [Matrix.mul_apply]
  exact IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun r _ => (hS p r).mul (hT r q)

theorem isValueAt_one_matrix (p q : Fin N) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y ((1 : Matrix (Fin N) (Fin N) Ω) p q) z
      ((1 : Matrix (Fin N) (Fin N) ℂ) p q) := by
  rcases eq_or_ne p q with rfl | h
  · simpa using IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one (y := y) (z := z)
  · simpa [Matrix.one_apply_ne h] using IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero (y := y) (z := z)

theorem valM_eq (hz : z ∈ mcPts (mCoordIdeal y)) {S : Matrix (Fin N) (Fin N) Ω}
    {Sz : Matrix (Fin N) (Fin N) ℂ} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (S p q) z (Sz p q)) :
    valM y S z = Sz := by
  ext p q
  exact IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (hS p q)

theorem regularAt_smul {a : Ω} (s : K → ℂ) (hs : ∀ k, s k ≠ 0)
    (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (fun p => s p.1 * z p) :=
  ⟨_, ha.choose_spec.smul s hs⟩

theorem regularAt_conj {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (fun p => starRingEnd ℂ (z p)) :=
  ⟨_, ha.choose_spec.conj⟩





theorem inFrameDomain_smul {c : (k : K) → ι k} {f : Ω} (s : K → ℂ) (hs : ∀ k, s k ≠ 0)
    (hd : InFrameDomain y c f z) : InFrameDomain y c f (fun p => s p.1 * z p) := by
  obtain ⟨hc, v, hv, hv0⟩ := hd
  exact ⟨fun k => mul_ne_zero (hs k) (hc k), v, isValueAt_iff.2 ((isValueAt_iff.1 hv).smul s hs), hv0⟩

theorem inFrameDomain_conj {c : (k : K) → ι k} {f : Ω} (hd : InFrameDomain y c f z) :
    InFrameDomain y c f (fun p => starRingEnd ℂ (z p)) := by
  obtain ⟨hc, v, hv, hv0⟩ := hd
  exact ⟨fun k => (map_ne_zero _).2 (hc k), starRingEnd ℂ v, isValueAt_iff.2 (isValueAt_iff.1 hv).conj,
    (map_ne_zero _).2 hv0⟩

theorem eventually_regularAt {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ} {w : Fin m → ℂ}
    (hγ : ContinuousAt γ w) {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w)) :
    ∀ᶠ w' in 𝓝 w, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w') := by
  obtain ⟨v, d, g, h, hg, hh, hy, hyg, hz, -⟩ := ha
  have hc : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) h)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) h)).continuousAt.comp hγ
  filter_upwards [hc.eventually_ne hz] with w' hw'
  exact ⟨_, d, g, h, hg, hh, hy, hyg, hw', (div_mul_cancel₀ _ hw').symm⟩

theorem eventually_inFrameDomain {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ} {w : Fin m → ℂ}
    (hγ : ContinuousAt γ w) {c : (k : K) → ι k} {f : Ω} (hd : InFrameDomain y c f (γ w)) :
    ∀ᶠ w' in 𝓝 w, InFrameDomain y c f (γ w') := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩, hv0⟩ := hd
  have hgz : eval (γ w) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hv
    exact hv0 hv
  have hG : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) g)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)).continuousAt.comp hγ
  have hH : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) h)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) h)).continuousAt.comp hγ
  have hC : ∀ᶠ w' in 𝓝 w, ∀ k, γ w' ⟨k, c k⟩ ≠ 0 := Filter.eventually_all.2 fun k =>
    ((continuous_apply (⟨k, c k⟩ : Σ k, ι k)).continuousAt.comp hγ).eventually_ne (hc k)
  filter_upwards [hG.eventually_ne hgz, hH.eventually_ne hz, hC] with w' hg' hh' hc'
  exact ⟨hc', _, ⟨d, g, h, hg, hh, hy, hyg, hh', rfl⟩, div_ne_zero hg' hh'⟩

end HermMetricEq

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
