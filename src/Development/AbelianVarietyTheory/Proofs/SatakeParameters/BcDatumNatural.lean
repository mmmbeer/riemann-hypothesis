import Mathlib
open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.DescentLocal

abbrev Datum {X U Y : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) :=
  ∀ (T : Scheme.{0}) (a b : T ⟶ U), a ≫ u = b ≫ u → {y : T ⟶ Y // y ≫ p = a} → {y : T ⟶ Y // y ≫ p = b}

variable {X U Y X' : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) (j : X' ⟶ X)

end GlobalTheory.DescentLocal

namespace GlobalTheory.DescentLocal

variable {X U Y X' : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) (j : X' ⟶ X)

end GlobalTheory.DescentLocal

namespace GlobalTheory.DescentLocal

variable {X U Y X₁ X₂ X₃ : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) {j₁ : X₁ ⟶ X} {j₂ : X₂ ⟶ X}
  {j₃ : X₃ ⟶ X}

def cmpU (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) : pullback u j₁ ⟶ pullback u j₂ :=
  pullback.lift (pullback.fst u j₁) (pullback.snd u j₁ ≫ k)
    (by rw [Category.assoc, hk, pullback.condition])

@[reassoc (attr := simp)]
theorem cmpU_fst (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpU u k hk ≫ pullback.fst u j₂ = pullback.fst u j₁ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmpU_snd (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpU u k hk ≫ pullback.snd u j₂ = pullback.snd u j₁ ≫ k := pullback.lift_snd _ _ _

def cmpY (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    pullback p (pullback.fst u j₁) ⟶ pullback p (pullback.fst u j₂) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ cmpU u k hk)
    (by rw [Category.assoc, cmpU_fst, pullback.condition])

@[reassoc (attr := simp)]
theorem cmpY_fst (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpY u p k hk ≫ pullback.fst p (pullback.fst u j₂) = pullback.fst p (pullback.fst u j₁) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmpY_snd (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpY u p k hk ≫ pullback.snd p (pullback.fst u j₂) =
      pullback.snd p (pullback.fst u j₁) ≫ cmpU u k hk :=
  pullback.lift_snd _ _ _

end GlobalTheory.DescentLocal
