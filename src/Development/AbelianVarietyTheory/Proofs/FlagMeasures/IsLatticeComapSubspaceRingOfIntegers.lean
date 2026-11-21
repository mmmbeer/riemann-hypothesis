import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Mathlib

section
namespace GlobalTheory.TargetStatementBis

open NumberField

theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V)
    (h : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h₁⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩
    have key : ((b : 𝓞 K)) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, key, smul_comm d a x]
    exact Λ.smul_mem a h₁

theorem target : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v

end GlobalTheory.TargetStatementBis
end

section
namespace GlobalTheory.SmulMemComapLattice

open NumberField

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (v : V) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hax
    · rw [mul_smul]; exact L.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap R K q ≠ 0 := by
      simpa using hq0
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have : (q * a) • (algebraMap R K p / algebraMap R K q) • x = p • a • x := by
      rw [← algebraMap_smul K (q * a), ← algebraMap_smul K p, ← algebraMap_smul K a x,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hax

theorem isLattice_comap_subtype {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Submodule.comap (LinearMap.restrictScalars (𝓞 K) W.subtype) Λ) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (LinearMap.restrictScalars (𝓞 K) W.subtype) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro w _
    obtain ⟨a, ha, haw⟩ := exists_smul_mem Λ hΛ.span_eq_top (w : V)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    have hw : w = (algebraMap (𝓞 K) K a)⁻¹ • (a • w) := by
      rw [← algebraMap_smul K a w, smul_smul, inv_mul_cancel₀ haK, one_smul]
    rw [hw]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simpa using haw

end GlobalTheory.SmulMemComapLattice
end

section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isLattice_comap_subtype_ringOfIntegers {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first
  | exact @_root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
  | exact _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
  | (apply _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype ..)

end GlobalTheory
end
