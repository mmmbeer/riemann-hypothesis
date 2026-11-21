import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL.Tests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_parInd_zero {d : Fin 0 → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prodIrr x hd)) :=
  nonempty_equiv_parInd_zero _ _ (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm

theorem empty_spec : IsZ (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ∧
    IsL (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  have ho : IsOrderedForm (k := k) (Fin.elim0 : Fin 0 → Segment k) 0 := ⟨rfl, fun i => i.elim0⟩
  exact ⟨⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isSocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩,
    ⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩⟩






end GlobalTheory.LocGL.Tests
