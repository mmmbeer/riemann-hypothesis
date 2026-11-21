import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.ThK.SmoothLev
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThK.SmoothLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsSmModOn (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Γ : Set (GAd σ J)) (φ : GAd σ J → ℂ) :
    Prop where
  left : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod)
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr GlobalTheory.SiegelSet.lineDer φ g‖ ≤ C * (GlobalTheory.AdelicU.height σ J g : ℝ) ^ N

theorem IsSmModOn.of_isSmoothModerate {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Γ : Set (GAd σ J)}
    {φ : GAd σ J → ℂ} (h : GlobalTheory.SiegelSet.IsSmoothModerate σ J φ) (hΓ : Γ ⊆ ratPts σ J) : IsSmModOn σ J Γ φ :=
  ⟨fun γ hγ g => h.left γ (hΓ hγ) g, h.level, h.cont, h.smooth, h.growth⟩

theorem isSmModOn_const (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Γ : Set (GAd σ J)) (c : ℂ) :
    IsSmModOn σ J Γ fun _ => c :=
  have h := GlobalTheory.SiegelSet.isSmoothModerate_const σ J c
  ⟨fun _ _ _ => rfl, h.level, h.cont, h.smooth, h.growth⟩

end GlobalTheory.ThK.SmoothLev

end
