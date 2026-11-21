import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qk46.colH :
    {n : Nat} → (Fin n → Int) → Int → Nat :=
    fun {n : Nat} (mu : Fin n → Int) (c : Int) ↦ @Finset.card (Fin n) {m : Fin n | @LE.le Int Int.instLEInt c (mu m)}

theorem UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH :
    ∀ {r : ℕ} {μ : Fin r → ℤ},
      Antitone μ →
        ∀ (c : ℤ) (m : Fin r), c ≤ μ m ↔ ↑m < UpperTheory.Reformulated.B.Qk46.colH μ c := by
  intro r μ h c m
  unfold UpperTheory.Reformulated.B.Qk46.colH
  exact (Tuple.lt_card_ge_iff_apply_ge_of_antitone h).symm
