import Formalism.CharacterColumnKernels.Statement

open Finset

noncomputable section

namespace Formalism.NG

def bigRect {R O : Type*} [CommRing O] {m g d : Type*} (ρ : R → Matrix d d O) (P : Matrix m g R) :
    Matrix (m × d) (g × d) O :=
  fun p q => ρ (P p.1 q.1) p.2 q.2

def StatGeneric : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    [Infinite (IsLocalRing.ResidueField O)]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)]
    (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))

def StatGenericFin : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)],
    ((Fintype.card g * ∑ w, Fintype.card (d w) : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))

end Formalism.NG
