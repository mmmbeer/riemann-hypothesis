import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace

noncomputable section

open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.BCFL

variable {p : ℕ} [Fact p.Prime]

def muSet (G : HTGroup p) (r : ℕ) (w₀ : Fin G.m) : Set (Gr G r) :=
  {δ | GlobalTheory.LKLoc.KotInv p (Q0 p) 1 r δ.1 (-1) ∧
    (∀ w, (∀ i j, ((δ.2 w)⁻¹).val i j ∈ intKQ p (G.Fw w) r) ∧
      ‖Algebra.norm ℚ_[p] (δ.2 w).val.det‖ = (p : ℝ) ^ (r * if w = w₀ then 1 else 0)) ∧
    1 < ‖GlobalTheory.LKGeo.mulKQ (G.Fw w₀) r ((sigKQ p (G.Fw w₀) r)^[r - 1] (δ.2 w₀).val.det)‖}

def phiMu (G : HTGroup p) (r : ℕ) (w₀ : Fin G.m) (δ : Gr G r) : ℂ :=
  if δ ∈ muSet G r w₀ then 1 else 0

def MatchMu : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ w₀ : Fin G.m,
    ∃ f' : Gr G 1 → ℂ, IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) (KHT p G.m G.n 1 G.Fw) f' ∧
      (∀ k₁ ∈ KHT p G.m G.n 1 G.Fw, ∀ k₂ ∈ KHT p G.m G.n 1 G.Fw, ∀ g, f' (k₁ * g * k₂) = f' g) ∧
      Match G r (KHT p G.m G.n r G.Fw) (phiMu G r w₀) (KHT p G.m G.n 1 G.Fw) f'

variable (p)

def phiW (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r c : ℕ) (δ : GL (Fin n) (KQ p K r)) : ℂ :=
  if (∀ i j, (δ⁻¹).val i j ∈ intKQ p K r) ∧ ‖Algebra.norm ℚ_[p] δ.val.det‖ = (p : ℝ) ^ (r * c) ∧
      (c = 1 → 1 < ‖GlobalTheory.LKGeo.mulKQ K r ((sigKQ p K r)^[r - 1] δ.val.det)‖) then 1 else 0

end GlobalTheory.BCFL
