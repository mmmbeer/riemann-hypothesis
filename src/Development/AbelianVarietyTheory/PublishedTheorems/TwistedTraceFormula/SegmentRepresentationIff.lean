import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published
open GlobalTheory.Parabolic (isIrreducible_of_equiv)

namespace GlobalTheory.SegmentRepModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Concl {d : ℕ} (σ : Representation ℂ (GL (Fin d) k) V) (l : ℕ) : Prop :=
  ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
    S.toRepresentation.IsIrreducible ∧
    (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      S'.toRepresentation.IsIrreducible → S' = S) ∧
    Nonempty ((jac (consecBlocks l d) S.toRepresentation).Equiv (piTensor (segTerm σ l)))


def jacCongr {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) : (jac e π).Equiv (jac e τ) :=
  equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap,
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v),
      fun y => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem concl_of_isSocle {d l : ℕ} {σ : Representation ℂ (GL (Fin d) k) V}
    {τ : Representation ℂ (GL (Fin (l * d)) k) W}
    (h : IsSocle τ (multiProd (consecBlocks l d) (segTerm σ l)))
    (hj : Nonempty ((jac (consecBlocks l d) τ).Equiv (piTensor (segTerm σ l)))) : Concl σ l := by
  obtain ⟨hi, f, hf, hS⟩ := h
  have inc : ∀ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ l)),
      ∃ g : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ l)),
        Function.Injective g ∧ g.range = S := fun S =>
    ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective,
      Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)⟩
  obtain ⟨g, hg, hr⟩ := inc f.range
  obtain ⟨φ⟩ := nonempty_equiv_of_range_eq f hf g hg hr.symm
  obtain ⟨ψ⟩ := hj
  refine ⟨f.range, isIrreducible_of_equiv φ hi, fun S' hS' => ?_, ⟨(jacCongr _ φ.symm).trans ψ⟩⟩
  obtain ⟨g', hg', hr'⟩ := inc S'
  exact hS _ (hr' ▸ isAtom_range hS' g' hg')

theorem concl_two {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Concl (detRep (Fin 1) χ) 2 := by
  classical
  have he : consecBlocks 2 1 = (ProjLine.pts : (Σ _ : Fin 2, Fin 1) ≃ Fin (2 * 1)) := by
    ext ⟨a, j⟩
    rw [consecBlocks_val, ProjLine.pts_apply]
    omega
  have hη : IsSmoothChar (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  obtain ⟨ψ⟩ := nonempty_jac_det_equiv (consecBlocks 2 1) χ
  refine concl_of_isSocle (τ := detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))) ?_ ⟨ψ⟩
  obtain ⟨X, _, _, π, f, ⟨φ⟩, hf, h0, h, -⟩ := ProjLine.exists_line hη
  let a : (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))).Equiv
      (jac (consecBlocks 2 1) (detRep (Fin (2 * 1)) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2)))) :=
    .mk (Submodule.quotEquivOfEqBot _ (twKer_detRep _ _)).symm fun g => LinearMap.ext fun c => by
      simp only [LinearMap.comp_apply]
      rw [Model.jac_detRep, ofChar_apply]
      exact map_smul _ (_ : ℂ) c
  have b := parIndEquiv (consecBlocks 2 1) (a.trans ψ)
  have φ' : π.Equiv (parInd (consecBlocks 2 1)
      (ofChar (detLevi (consecBlocks 2 1) (χ * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))))) := by
    rw [he]; exact φ
  exact (ProjLine.isSocle_of_le (isIrreducible_ofChar _) f hf h0 h).of_equiv (.refl _) (φ'.trans b)

example {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsCuspidal (IrrRep.det (Fin 1) χ hχ).ρ ∧ Concl (IrrRep.det (Fin 1) χ hχ).ρ 2 :=
  ⟨isCuspidal_detRep_one hχ, concl_two hχ⟩

example (p : ℕ) [Fact p.Prime] : Concl (detRep (Fin 1) (1 : ℚ_[p]ˣ →* ℂˣ)) 2 := concl_two isSmoothChar_one

end GlobalTheory.SegmentRepModel

end
