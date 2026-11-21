import Formalism.ThetaLogCoordinates.PartnerDischarge.PartnerDischargeProofs.GammaZeroIntegralLogBound

namespace Formalism.InvariantFactorPaths.MC

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.InvariantFactorPaths.OddLevelGainBounds.TB

def GamIntC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ PolZ p r LL → f' ∈ PolZ p r LL →
    ∃ c : ℕ → ℤ_[p], ∀ n, LL.total ≤ n →
      ((p : ℚ_[p]) ^ ((N + 4) * (r * Nat.log p (LL.total + LL.deg (Fin.last N) + r)) +
          6 * Nat.log p (LL.total + LL.deg (Fin.last N) + r))) * tieGam p LL ρ z n f f' =
        ∑ i ∈ range (LL.total + LL.deg (Fin.last N) + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])

def YPartnerC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → HypP p LL ρ e1 →
    ∀ z ∈ YZ p (r := r) LL J M,
      (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) →
      ∃ z'' ∈ YZ p (r := r) LL J M, (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) ≤ ‖fockN p LL z z''‖

def TheoremMCB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a : ℕ) (E κ κ4 : ℝ) (e1 : ℕ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    (3 / 2 : ℝ) * (((N + 2) * r ^ 2 : ℝ) * lgB p a r) ≤ κ → ((e1 * (N + 2) : ℕ) : ℝ) ≤ κ → 3 * lgB p a r + κ4 ≤ κ →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      HypP p (LL.setTies T n) ρ e1 ∧ HypW p (r := r) (LL.setTies T n) e1 ∧
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ4) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * lgB p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)

end Formalism.InvariantFactorPaths.MC
