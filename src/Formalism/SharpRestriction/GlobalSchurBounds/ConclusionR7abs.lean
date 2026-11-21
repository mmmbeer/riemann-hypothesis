import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Ideal
open scoped Pointwise

abbrev gl (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) : D.R.GG :=
  D.host.galE σ

open Classical in

def SmallOrderPrimeLogSumBound (D : D7) : Prop :=
  ∀ J : ℝ, 1 ≤ J → ∀ Y : ℝ,
    ∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
        (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J),
      Real.log l / (l : ℝ) ≤ J * Real.log (((2 ^ D.R.e : ℕ) : ℝ) * Y) ^ 2 / ((2 ^ D.R.e : ℕ) : ℝ)

open Classical in

def WeightBudgetBound (D : D7) : Prop :=
  ∀ Lw : ℕ, 2 ≤ Lw → ∀ T₂ : Finset ℕ,
    (∀ s ∈ T₂, (s : ℝ) < (D.R.n0 : ℝ) / (4 * Lw)) → NoThreeTermRelation T₂ Lw →
    ∀ u₀ t h : HH D,
      (Lw < addOrderOf h → ∀ i₀ : ℤ,
        ((Finset.Icc i₀ (i₀ + Lw)).filter (fun i : ℤ => t + i • h ∈ transl T₂ u₀)).card ≤ 2) ∧
      (addOrderOf h ≤ 4 * Lw → (coset t h ∩ transl T₂ u₀).ncard ≤ 1)

open Classical in

def SecondMomentBadEventsBound (D : D7) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 16 ≤ δ * D.R.n →
  ∀ β : ℝ, 0 ≤ β → ∀ H₀ : Set (HH D), ∀ BAD : HH D → HH D → Finset (HH D) → Prop,
    (∀ h ∈ H₀, ∀ t : HH D,
      (∑ T : Finset (HH D), if t ∈ T ∧ BAD h t T then bern δ T else 0) ≤ β * δ) →
    ∀ (P : Finset ℕ) (hp : ℕ → HH D) (ω : ℕ → ℝ),
      (∀ p ∈ P, hp p ∈ H₀) → (∀ p ∈ P, 0 ≤ ω p) →
      ∃ T : Finset (HH D), δ * D.R.n / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 3 / 2 * δ * D.R.n ∧
        ∑ p ∈ P, ω p * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) ≤
          4 * β * δ * D.R.n * ∑ p ∈ P, ω p

theorem classMap_estimate_of_partial (D : D7) (sc : Scale) (h : SecondMomentBadEventsBound D) : Conclusion6 D sc := by
  classical
  intro δ h0 h1 h16 β BAD _ hb P hp ω hP hω
  by_cases hβ : 0 ≤ β
  · obtain ⟨T, a, b, c⟩ := h δ h0 h1 h16 β hβ {h | sc.x ^ (sc.eps / 4) ≤ (addOrderOf h : ℝ)} BAD
      (fun h hh t => hb h hh t) P hp ω hP hω
    refine ⟨T, a, le_trans b ?_, c⟩
    have : 0 ≤ δ * D.R.n := by linarith
    nlinarith
  · rcases P.eq_empty_or_nonempty with rfl | ⟨p, hp'⟩
    · obtain ⟨T, a, b, _⟩ := h δ h0 h1 h16 0 le_rfl ∅ BAD (fun h hh => absurd hh (by simp)) ∅ hp ω
        (by simp) (by simp)
      refine ⟨T, a, le_trans b ?_, by simp⟩
      have : 0 ≤ δ * D.R.n := by linarith
      nlinarith
    · exfalso
      have h2 := hb (hp p) (hP p hp') 0
      have h3 : 0 ≤ ∑ T : Finset (HH D), if (0 : HH D) ∈ T ∧ BAD (hp p) 0 T then bern δ T else 0 := by
        refine Finset.sum_nonneg fun T _ => ?_
        split_ifs
        · exact mul_nonneg (pow_nonneg h0.le _) (pow_nonneg (by linarith) _)
        · exact le_rfl
      have : β * δ < 0 := mul_neg_of_neg_of_pos (not_le.mp hβ) h0
      linarith

open Classical in

def PairwiseIndependentOrbitPoints (D : D7) : Prop :=
  (∀ t h : HH D, ∀ i i' : ℕ, i < addOrderOf h → i' < addOrderOf h → t + i • h = t + i' • h → i = i') ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    (∀ S A : Finset (HH D), A ⊆ S →
      (∑ T : Finset (HH D), if T ∩ S = A then bern δ T else 0) =
        δ ^ A.card * (1 - δ) ^ (S.card - A.card)) ∧
    (∀ (t : HH D) (S A : Finset (HH D)), t ∉ S → A ⊆ S →
      (∑ T : Finset (HH D), if t ∈ T ∧ T ∩ S = A then bern δ T else 0) =
        δ * (δ ^ A.card * (1 - δ) ^ (S.card - A.card)))

def ProPrimeIwahoriSubgroupExists : Prop :=
  ∀ (g k : ℕ) [Fact g.Prime], ∃ P : Subgroup (GL (Fin k) ℤ_[g]),
    (∀ M : GL (Fin k) ℤ_[g], M ∈ P ↔ ∀ i j : Fin k,
      (j < i → PadicInt.toZMod ((M : Matrix (Fin k) (Fin k) ℤ_[g]) i j) = 0) ∧
      PadicInt.toZMod ((M : Matrix (Fin k) (Fin k) ℤ_[g]) i i) = 1) ∧
    IsProG g P

def DoubleCosetFreeActionOfNormal : Prop :=
  ∀ (G : Type) [Group G] (Γ U₀ U₁ : Subgroup G), U₁ ≤ U₀ →
    (∀ u ∈ U₀, ∀ v ∈ U₁, u⁻¹ * v * u ∈ U₁) →
    (∀ y : G, Γ ⊓ U₀.map (MulAut.conj y).toMonoidHom = ⊥) →
    (∀ y y' u : G, u ∈ U₀ → (∃ γ ∈ Γ, ∃ v ∈ U₁, y' = γ * y * v) →
      ∃ γ ∈ Γ, ∃ v ∈ U₁, y' * u = γ * (y * u) * v) ∧
    (∀ y u : G, u ∈ U₁ → ∃ γ ∈ Γ, ∃ v ∈ U₁, y * u = γ * y * v) ∧
    (∀ y u : G, u ∈ U₀ → (∃ γ ∈ Γ, ∃ v ∈ U₁, y * u = γ * y * v) → u ∈ U₁) ∧
    (∀ y y' : G, (∃ γ ∈ Γ, ∃ u ∈ U₀, y' = γ * y * u) ↔
      ∃ u ∈ U₀, ∃ γ ∈ Γ, ∃ v ∈ U₁, y' = γ * (y * u) * v)

def DoubleCosetIndexFormula : Prop :=
  ∀ (G : Type) [Group G] (Γ U₀ U₁ : Subgroup G), U₁ ≤ U₀ →
    (∀ u ∈ U₀, ∀ v ∈ U₁, u⁻¹ * v * u ∈ U₁) →
    (∀ y : G, Γ ⊓ U₀.map (MulAut.conj y).toMonoidHom = ⊥) →
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (U₁ : Set G)) =
      U₁.relIndex U₀ * Nat.card (DoubleCoset.Quotient (Γ : Set G) (U₀ : Set G))

def EquivariantFunctionsByDoubleCosetValues : Prop :=
  ∀ (G : Type) [Group G] (Γ U : Subgroup G) (W : Type) [MulAction U W] (ι : Type) (y : ι → G),
    (∀ x : G, ∃! c : ι, ∃ γ ∈ Γ, ∃ u ∈ U, x = γ * y c * u) →
    (∀ φ : G → W, (∀ γ ∈ Γ, ∀ (x : G) (u : U), φ (γ * x * u) = u⁻¹ • φ x) →
      ∀ (c : ι) (u : U), (∃ γ ∈ Γ, (u : G) = (y c)⁻¹ * γ * y c) → u • φ (y c) = φ (y c)) ∧
    (∀ w : ι → W,
      (∀ (c : ι) (u : U), (∃ γ ∈ Γ, (u : G) = (y c)⁻¹ * γ * y c) → u • w c = w c) →
      ∃! φ : G → W, (∀ γ ∈ Γ, ∀ (x : G) (u : U), φ (γ * x * u) = u⁻¹ • φ x) ∧ ∀ c, φ (y c) = w c)

abbrev cA (D : D7) (cc : Ideal (𝓞 D.host.K))
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * aa

def ConclusionR7abs : Prop := ProPrimeIwahoriSubgroupExists ∧ DoubleCosetFreeActionOfNormal ∧ DoubleCosetIndexFormula ∧ EquivariantFunctionsByDoubleCosetValues

end Formalism.MainNotions.UnusedSlot33

end
