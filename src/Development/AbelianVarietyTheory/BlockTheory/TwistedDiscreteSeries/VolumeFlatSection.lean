import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Blocks

variable (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

def parahoric : Subgroup (GL (A ⊕ D) k) :=
  ((parab 𝓀[k] (two (Equiv.refl (A ⊕ D)))).comap
      (GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]))).map
    (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k))

variable {k A D D'}

theorem mem_parahoric {g : GL (A ⊕ D) k} : g ∈ parahoric k A D ↔
    g ∈ KO k (A ⊕ D) ∧ ∀ i j, valuation k (g.1 (.inr i) (.inl j)) < 1 := by
  have hl : ∀ x : A, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D))) (Sum.inl x) = false := by
    intro x
    have e : (Sum.inl x : A ⊕ D) = GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D)) ⟨false, x⟩ := by simp
    rw [e, GlobalTheory.SmGL.blk_apply]
  have hr : ∀ x : D, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D))) (Sum.inr x) = true := by
    intro x
    have e : (Sum.inr x : A ⊕ D) = GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D)) ⟨true, x⟩ := by simp
    rw [e, GlobalTheory.SmGL.blk_apply]
  have hval : ∀ z : 𝒪[k], IsLocalRing.residue 𝒪[k] z = 0 ↔ valuation k (z : k) < 1 := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, rfl⟩, fun i j => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_parab] at hh
    have h0 := hh (Sum.inr i) (Sum.inl j) (by rw [hl, hr]; decide)
    simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at h0 ⊢
    exact (hval _).mp h0
  · rintro ⟨⟨h, rfl⟩, hv⟩
    refine ⟨h, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_parab]
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;> simp only [hl, hr, lt_self_iff_false] at hij
    · exact absurd hij (by decide)
    · have h0 := hv i j
      simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at h0 ⊢
      exact (hval _).mpr h0

def typeSpace {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) :
    Submodule ℂ V where
  carrier := {f | ∀ g ∈ parahoric k A D, ∀ d : kˣ, (d : k) = g.1.toBlocks₂₂.det → π g f = (ξ d : ℂ) • f}
  add_mem' hf hf' g hg d hd := by rw [map_add, hf g hg d hd, hf' g hg d hd, smul_add]
  zero_mem' g _ d _ := by simp
  smul_mem' c f hf g hg d hd := by rw [map_smul, hf g hg d hd, smul_comm]

def InSupp (x : Matrix (A ⊕ D) (A ⊕ D') k) : Prop :=
  (∀ i j, x i j ∈ 𝒪[k]) ∧ valuation k x.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (x (.inr i) (.inl j)) < 1

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype D] [DecidableEq D] [Fintype D']
  [DecidableEq D'] in
theorem InSupp.det_ne {x : Matrix (A ⊕ D) (A ⊕ D') k} (h : InSupp x) : x.toBlocks₁₁.det ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

open Classical in

def datum (ξ : kˣ →* ℂˣ) (x : Matrix (A ⊕ D) (A ⊕ D') k) : ℂ :=
  if h : InSupp x then (((ξ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

end Blocks

section Section

variable {k} {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [MeasurableSpace k]

def dblDatum (Φ₁ Φ₂ : Matrix b a k → ℂ) (y : Matrix b (a ⊕ a) k) : ℂ :=
  Φ₁ y.toCols₁ * starRingEnd ℂ (Φ₂ (-y.toCols₂))

end Section

abbrev Blocks (l t : ℕ) : Type := Σ _ : Fin l, Fin t

variable {k}

abbrev blockRep {l : ℕ} (t : ℕ) (μ : Fin l → kˣ →* ℂˣ) :=
  multiProd (m := fun _ : Fin l => Fin t) (X := fun _ => ℂ) (Equiv.refl (Blocks l t)) fun i => detRep (Fin t) (μ i)

def blockParam {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ) (μ' : kˣ →* ℂˣ) (x : Blocks l t) : ℂˣ :=
  μ x.1 ϖ / μ' ϖ * absPow k (((x.2 : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ

def blockL {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ) (μ' : kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  lFactor (resCard k) (blockParam t ϖ μ μ') s * lFactor (resCard k) (blockParam t ϖ μ μ')⁻¹ s

def zetaAt (q i : ℕ) : ℝ := (1 - ((q : ℝ) ^ i)⁻¹)⁻¹

def volAdd [MeasurableSpace k] (ν : Measure k) (r : ℕ) : ℝ :=
  (volM ν (Fin r) (Fin r)).real (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)))

example {A D D' : Type} [Fintype A] [DecidableEq A] (ξ : kˣ →* ℂˣ) :
    datum ξ (fromBlocks 1 0 0 0 : Matrix (A ⊕ D) (A ⊕ D') k) = 1 := by
  have h : InSupp (fromBlocks 1 0 0 0 : Matrix (A ⊕ D) (A ⊕ D') k) := by
    refine ⟨?_, by simp, fun i j => by simp⟩
    rintro (i | i) (j | j)
    · exact one_int i j
    all_goals exact zero_mem _
  rw [datum, dif_pos h]
  have : Units.mk0 _ h.det_ne = 1 := by ext; simp
  simp [this]

example {D : Type} [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ) :
    (1 : ℂ) ∈ typeSpace (A := Fin 0) (detRep (Fin 0 ⊕ D) ξ) ξ := fun g _ d hd => by
  have : GeneralLinearGroup.det g = d := by
    ext
    rw [hd, GeneralLinearGroup.val_det_apply, ← det_submatrix_equiv_self (Equiv.emptySum (Fin 0) D).symm]
    rfl
  simp [detRep, this]

end GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
