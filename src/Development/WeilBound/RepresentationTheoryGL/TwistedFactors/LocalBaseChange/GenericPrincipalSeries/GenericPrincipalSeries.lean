import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Lbc

def torusChar {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ))
    (t : ∀ _ : Fin n, GL (Fin 1) k) : ℂ :=
  ∏ a, ((ξ a (Matrix.GeneralLinearGroup.det (t a)) : ℂˣ) : ℂ)

def GenericPrincipalSeries : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (x : IrrGL k)
    (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = x.1),
    IsGeneric x.rep → HasSupport x.rep (Finset.univ.val.map fun a => IrrGL.ofChar (ξ a) (hξ a)) →
    (∀ a b, ξ a / ξ b ≠ absPow k 1) →
    Nonempty (x.rep.Equiv (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd))

def PinLift : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [CharZero E]
    (Nm : Eˣ →* Fˣ), (∀ x, absPow F 1 (Nm x) = absPow E 1 x) →
    ∀ (n : ℕ) (ξ : Fin n → (Fˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a))
      (hξN : ∀ a, IsSmoothChar ((ξ a).comp Nm)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n),
    (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd).IsIrreducible →
    IsUnitarisable (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd) →
    IsGeneric (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd) →
    ∀ (x : IrrGL E) (hdE : ∑ a, (IrrGL.ofChar ((ξ a).comp Nm) (hξN a)).1 = x.1),
    IsGeneric x.rep → HasSupport x.rep (Finset.univ.val.map fun a => IrrGL.ofChar ((ξ a).comp Nm) (hξN a)) →
    Nonempty (x.rep.Equiv (prodIrr (fun a => IrrGL.ofChar ((ξ a).comp Nm) (hξN a)) hdE))

end PositivityTheory.Lbc

end
