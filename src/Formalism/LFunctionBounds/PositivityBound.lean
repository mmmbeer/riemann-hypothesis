import Formalism.StatementFL

section
open Complex

noncomputable section

namespace Formalism.FX

open Classical

def triples (l : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 l ×ˢ Finset.Icc 1 l ×ˢ Finset.Icc 1 l).filter (fun S => S.1 + S.2.1 + S.2.2 = l)

def IsProb (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) : Prop :=
  (∀ S ∈ triples l, 0 ≤ ν S) ∧ ∑ S ∈ triples l, ν S = 1

def W (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ S ∈ triples l, ν S *
    ((if S.1 = x then 1 else 0) + (if S.2.1 = x then 1 else 0) + (if S.2.2 = x then 1 else 0))

def Snu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  ∑ x ∈ Finset.Ioo 0 l, (W l ν x : ℂ) * (starRingEnd ℂ) (χ (x : ZMod l))

def cW (l : ℕ) [NeZero l] (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  DirichletCharacter.LFunction χ 0 * Snu l ν χ / ((((l : ℝ) - 1) / 2 : ℝ) : ℂ)

def oddChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => χ.Odd) (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))

def saw (y : ℝ) : ℝ := if Int.fract y = 0 then 0 else Int.fract y - 1 / 2

def gam (s : ℝ) : ℝ := Real.Gamma s / Real.Gamma (1 - s)

def logOm1 (l : ℕ) (S : ℕ × ℕ × ℕ) : ℝ :=
  -Real.log l + (Real.log (gam ((S.1 : ℝ) / (l : ℝ))) + Real.log (gam ((S.2.1 : ℝ) / (l : ℝ))) +
    Real.log (gam ((S.2.2 : ℝ) / (l : ℝ))))

def inCM (l : ℕ) (S : ℕ × ℕ × ℕ) (n : ℕ) : Prop :=
  Int.fract ((n * S.1 : ℝ) / l) + Int.fract ((n * S.2.1 : ℝ) / l) < 1

open ArithmeticFunction in

def AS (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    if ¬ l ∣ n ∧ ¬ inCM l S n then Λ n * max 0 (y / (n : ℝ) - 1) else 0

def Al (l : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, Real.log l * max 0 (y / (l : ℝ) ^ i - 1)

def logPiV (l : ℕ) : ℝ := Real.log (2 * Real.pi / l) + Real.log l / ((l : ℝ) - 1)

def tripleMainTerm (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  y * (Real.log y - 1 - logOm1 l S + logPiV l)

example : triples 3 = {(1, 1, 1)} := by decide
example : saw (1 / 2) = 0 := by norm_num [saw]
example (y : ℝ) : saw (y + 1) = saw y := by simp [saw]

def Theorem7 : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ S ∈ triples l, ∀ x : ℝ, (l : ℝ) ^ (1 / ε) ≤ x → x ≤ (l : ℝ) ^ (1300 / ε) →
      AS l S x + 2 * Al l x ≤ tripleMainTerm l S x + x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

end Formalism.FX
end
end

section
open Complex

noncomputable section

namespace Formalism.FX

open Classical

def allChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) := @Finset.univ _ (Fintype.ofFinite _)

def IX {l : ℕ} (χ : DirichletCharacter ℂ l) (X : ℕ) : ℂ := ∑ x ∈ Finset.Icc 1 X, χ (x : ZMod l)

def Lerch : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 →
    HasDerivAt (fun s : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s)
      (((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ)) : ℂ) 0

def PositivityBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ l : ℕ, 3 ≤ l → Odd l → ∀ φ : ℕ → ℝ,
    (∀ x, 0 < x → x < l → φ (l - x) = -φ x) →
    (∀ S ∈ triples l, 0 < φ S.1 + φ S.2.1 + φ S.2.2) →
    ∃ X : ℕ, 1 ≤ X ∧ X ≤ (l - 1) / 2 ∧
      (X : ℝ) * ∑ x ∈ Finset.Ioo 0 l, φ x ^ 2 ≤
        K * (1 + Real.log l) * (∑ x ∈ Finset.Icc 1 X, φ x) ^ 2

def DivisorBound : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ e

def M4 : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ (l : ℕ) [NeZero l], l.Prime → ∀ X : ℕ, X ≤ l →
    ∑ χ ∈ (allChars l).filter (· ≠ 1), ‖IX χ X‖ ^ 4 ≤ C * (l : ℝ) ^ (1 + e) * (X : ℝ) ^ 2

def LPartialSum : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ B : ℝ,
    (∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q)‖ ≤ B) →
    ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
        2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)

end Formalism.FX
end
end
