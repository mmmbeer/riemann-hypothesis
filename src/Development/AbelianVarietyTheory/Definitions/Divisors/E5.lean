import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC

def E5 : Prop :=
  (∀ (q : ℕ) [NeZero q] (n : ℕ), ∃ e : ∀ X : Scheme.{0}, IsUnit (q : Γ(X, ⊤)) → (GlobalTheory.Et.H (ZMod q) n X ≃+ Ht q (sch.obj X) n 0),
    ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (hX : IsUnit (q : Γ(X, ⊤))) (hY : IsUnit (q : Γ(Y, ⊤))) (x : GlobalTheory.Et.H (ZMod q) n X),
      e Y hY (GlobalTheory.Et.pull (ZMod q) n f x) = pull _ (sch.map f) _ _ (e X hX x)) ∧
  (∀ (q : ℕ) [NeZero q] (i n : ℕ), ∃ e : ∀ X : Scheme.{0}, IsUnit (q : Γ(X, ⊤)) → (GlobalTheory.Et.HMu q i n X ≃+ Ht q (sch.obj X) n i),
    ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (hX : IsUnit (q : Γ(X, ⊤))) (hY : IsUnit (q : Γ(Y, ⊤))) (x : GlobalTheory.Et.HMu q i n X),
      e Y hY (GlobalTheory.Et.pullS (ZMod q) (GlobalTheory.Et.muSheaf q i) n f x) = pull _ (sch.map f) _ _ (e X hX x)) ∧
  ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsSepClosed k], IsUnit (l : k) → ∀ n : ℕ,
    ∃ e : ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)), LocallyOfFiniteType p → QuasiCompact p → QuasiSeparated p →
      (GlobalTheory.Et.H ℤ_[l] n X ≃ₗ[ℤ_[l]] Hl l (sch.obj X) n 0),
    ∀ {Y X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X) h1 h2 h3 h1' h2' h3' (x : GlobalTheory.Et.H ℤ_[l] n X),
      e Y (f ≫ p) h1' h2' h3' (GlobalTheory.Et.pull ℤ_[l] n f x) = pullHl l (sch.map f) n 0 (e X p h1 h2 h3 x)

end GlobalTheory.EtC

end
