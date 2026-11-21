import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ConclRankZeroRight

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published.HoweDualityFiniteModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}


theorem acts_zero {κ : Type} [Fintype κ] (v : Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ)) (φ₁ : (κ → Fv F v) → ℂ)
    (hs : Function.Surjective (evFin F v)) (h : Acts (evFin F v) T 0 φ₁) : φ₁ = 0 := by
  have e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) (1 : (κ → AF F) → ℂ) = 0 := by funext x; simp [tens]
  have := h 1 ⟨fun _ _ _ => rfl, e ▸ (schA F κ).zero_mem⟩
  rw [e, map_zero] at this
  funext y
  choose s hs using hs
  have := congrFun this (fun i => s (y i))
  simpa [tens, hs] using this.symm


section Triv

variable {R : Type} [CommRing R] [Invertible (2 : R)] {S : Type} [CommRing S] [Algebra R S] {c : S →ₐ[R] S}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
  [TopologicalSpace R] [TopologicalSpace S] [IsModuleTopology R S] {C : TestClass R}

omit [IsModuleTopology R S] [DecidableEq α] in
theorem split_one (ψ : AddChar R ℂ) {ξ : S} {JA : Matrix α α S} {JB : Matrix β β S} [IsEmpty κ]
    (co : Darboux (symp c ξ JA JB) κ) : IsUSplitting C ψ co (actB c) (1 : UG c JB →* Module.End ℂ ((κ → R) → ℂ)) := by
  refine ⟨⟨fun g φ h => h, fun g w φ _ => ?_, fun g l h => h⟩, fun μ _ g φ _ => rfl, fun l _ φ _ => continuous_const (y := l φ)⟩
  funext x
  simp [Darboux.rho, schr, dotProduct, Subsingleton.elim (x + _) x]

omit [DecidableEq α] in
theorem weilB_one (ψ : AddChar R ℂ) {ξ : S} {JA : Matrix α α S} {JB : Matrix β β S} [IsEmpty κ] [IsEmpty (α × β)]
    (co : Darboux (symp c ξ JA JB) κ) : IsUWeilB c C ψ ξ JA JB co 1 1 := by
  haveI : IsEmpty (α × (β ⊕ β)) := ⟨fun ⟨a, b⟩ => b.elim (fun b => isEmptyElim (a, b)) fun b => isEmptyElim (a, b)⟩
  refine ⟨split_one ψ co, GlobalTheory.WeilM.SiegelModel.darbZero ξ JA (dbl JB) _, 1, fun _ _ => Subsingleton.elim _ _,
    ⟨isLagr_diagCols c JB, split_one ψ _, fun l _ _ p t hp φ _ => ?_⟩, fun g gd h φ₁ _ φ₂ _ => rfl⟩
  rcases isEmpty_prod.1 (inferInstance : IsEmpty (α × β)) with h | h
  · simp
  · have : Matrix.GeneralLinearGroup.det t = 1 := by ext; simp
    simp [this]

end Triv


section LocalTests

open scoped TensorProduct

variable {G H Y V T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup T]
  [Module ℂ T]







end LocalTests

end GlobalTheory.Published.HoweDualityFiniteModel

end
