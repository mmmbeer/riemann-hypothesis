import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.Model

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas



open Pointwise in

theorem covol_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (D : Set G) (hD : IsFundamentalDomain Γ D μ)
    (hm : MeasurableSet D) (hc : ∀ x, ∃ γ ∈ (Γ : Set G), γ * x ∈ D) :
    covol (Γ : Set G) μ Set.univ = μ D := by
  apply le_antisymm
  · exact iInf_le_of_le D (iInf_le_of_le hm (iInf_le_of_le (fun x _ => hc x) le_rfl))
  · refine le_iInf fun D' => le_iInf fun hm' => le_iInf fun hc' => ?_
    rw [hD.measure_eq_tsum D']
    have : D ⊆ ⋃ g : Γ, (g • D' ∩ D) := by
      intro x hx
      obtain ⟨γ, hγ, h⟩ := hc' x trivial
      refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
      rw [Set.mem_inv_smul_set_iff]
      exact h
    exact (measure_mono this).trans (measure_iUnion_le _)

def e2 : Fin 2 → Bool := ![true, false]

def W2 : Fin 2 → Submodule ℂ (Fin 2 → ℂ) := ![⊥, Submodule.span ℂ {![1, 1]}]

theorem isIsotropicFlag_unitary_one_one : IsIsoFlag e2 ![1] W2 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [W2]
  · intro i
    fin_cases i
    have : (![1, 1] : Fin 2 → ℂ) ≠ 0 := by
      intro h; simpa using congrFun h 0
    change Module.finrank ℂ (Submodule.span ℂ {(![1, 1] : Fin 2 → ℂ)}) =
      Module.finrank ℂ (⊥ : Submodule ℂ (Fin 2 → ℂ)) + 1
    rw [finrank_span_singleton this, finrank_bot]
  · intro x hx y hy
    change x ∈ Submodule.span ℂ {![1, 1]} at hx
    change y ∈ Submodule.span ℂ {![1, 1]} at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [Formalism.REAL.Jm, e2, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.diagonal]

def nM (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 + t * Complex.I / 2, -(t * Complex.I / 2); t * Complex.I / 2, 1 - t * Complex.I / 2]

theorem nM_add (s t : ℝ) : nM s * nM t = nM (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem nM_zero : nM 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nM]

def nU (t : ℝ) : Formalism.REAL.UJ e2 :=
  ⟨⟨nM t, nM (-t), by rw [nM_add]; simp [nM_zero], by rw [nM_add]; simp [nM_zero]⟩, by
    change Formalism.REAL.inUJ e2 (nM t)
    unfold Formalism.REAL.inUJ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nM, Formalism.REAL.Jm, e2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        map_ofNat] <;>
      ring⟩

theorem nU_add (s t : ℝ) : nU s * nU t = nU (s + t) :=
  Subtype.ext (Units.ext (nM_add s t))


theorem continuous_nM : Continuous nM := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [nM] <;> fun_prop

theorem continuous_nU : Continuous nU := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨continuous_nM, ?_⟩
  exact continuous_nM.comp continuous_neg



def mU : Formalism.REAL.UJ e2 :=
  ⟨⟨!![5 / 4, 3 / 4; 3 / 4, 5 / 4], !![5 / 4, -3 / 4; -3 / 4, 5 / 4],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num⟩, by
    change Formalism.REAL.inUJ e2 !![5 / 4, 3 / 4; 3 / 4, 5 / 4]
    unfold Formalism.REAL.inUJ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.REAL.Jm, e2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        map_ofNat] <;> norm_num⟩

theorem mU_act (a : ℂ) : uMat mU *ᵥ (a • ![1, 1]) = (2 * a) • ![1, 1] := by
  change !![5 / 4, 3 / 4; 3 / 4, 5 / 4] *ᵥ (a • ![1, 1]) = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem mU_herm : (uMat mU)ᴴ = uMat mU := by
  change (!![5 / 4, 3 / 4; 3 / 4, 5 / 4] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![5 / 4, 3 / 4; 3 / 4, 5 / 4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, map_ofNat]

theorem mU_mem : mU ∈ flagM e2 W2 := by
  intro i y hy
  rw [mU_herm, and_self]
  fin_cases i
  · change y ∈ (⊥ : Submodule ℂ (Fin 2 → ℂ)) at hy
    rw [Submodule.mem_bot] at hy
    subst hy
    simp
  · change y ∈ Submodule.span ℂ {![1, 1]} at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mU_act]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem locSize_mU : locSize ![1] W2 (uMat mU) 0 = 1 / 2 := by
  have hne : (![1, 1] : Fin 2 → ℂ) ≠ 0 := by
    intro h; simpa using congrFun h 0
  have h0 : detOn (uMat mU) ⊥ = 1 := by
    unfold detOn
    rw [dif_pos (by intro y hy; rw [Submodule.mem_bot] at hy; subst hy; simp)]
    rw [LinearMap.det_eq_one_of_subsingleton]; simp
  have h1 : detOn (uMat mU) (Submodule.span ℂ {![1, 1]}) = 2 := by
    have hs : ∀ y ∈ Submodule.span ℂ {(![1, 1] : Fin 2 → ℂ)},
        Matrix.toLin' (uMat mU) y ∈ Submodule.span ℂ {(![1, 1] : Fin 2 → ℂ)} := fun y hy =>
      (mU_mem 1 y hy).1
    unfold detOn
    rw [dif_pos hs]
    have : (Matrix.toLin' (uMat mU)).restrict hs = (2 : ℂ) • LinearMap.id := by
      ext ⟨y, hy⟩ : 1
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      apply Subtype.ext
      change uMat mU *ᵥ (a • ![1, 1]) = (2 : ℂ) • a • ![1, 1]
      rw [mU_act, mul_smul]
    rw [this, LinearMap.det_smul, finrank_span_singleton hne]
    simp
  change (detOn (uMat mU) (Submodule.span ℂ {![1, 1]}) / detOn (uMat mU) ⊥) ^ (-(1 : ℝ) / ((1 : ℕ) : ℝ)) = 1 / 2
  rw [h0, h1]
  norm_num [Real.rpow_neg_one]

end GlobalTheory.FlagMeas.Model
