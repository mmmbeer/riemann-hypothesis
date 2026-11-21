import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces

section Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)
  (bkP : BlochKatoReduction.Gen.BKPh X) (E : IntegralHeckeForms.ExpDat Y)

def GoodAll (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (A Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, IsCoprime a (X.l i : ℤ) → IntegralHeckeForms.GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

def LemmaAllAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk Y E i j b (IntegralHeckeForms.SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf Y i j b (IntegralHeckeForms.SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    GoodAll Y bkP E N0 i eps' S A Q k' ψ'

abbrev Reading (i : X.Tw) : Type :=
  ∀ (j : ℕ) (b : Bool) (k : ℕ) (_ : Finset (PlE D.host)) (_ : G D.host.E N.Om →* (X.Ok i k)ˣ),
    Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) × Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)

variable {Y bkP E}

theorem GoodAll.goodTw {N0 : X.Tw → ℕ} {i : X.Tw} {eps' : ℝ}
    {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)} {A Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ' : X.RCG i Q →* (X.Ok i k')ˣ} (h : GoodAll Y bkP E N0 i eps' S A Q k' ψ') :
    IntegralHeckeForms.GoodTw Y bkP E N0 i eps' S A Q k' ψ' := by
  have := h 1 isCoprime_one_left
  rwa [zpow_one] at this

end Gen

def LemmaAll (D : Formalism.BasicNotions.D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → LemmaAllAt D.nexp (BlochKatoReduction.pin bkP) E N0 i

theorem LemmaAll.aux₃ {D : Formalism.BasicNotions.D7} {bkP : BlochKatoReduction.BK D} {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ}
    (h : LemmaAll D bkP E N0) : IntegralHeckeForms.aux₃ D bkP E N0 := by
  intro i hi hs eps' he hF S hS A
  obtain ⟨Q, k', ψ', hg⟩ := h i hi hs eps' he hF S hS A
  exact ⟨Q, k', ψ', hg.goodTw⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces

end
