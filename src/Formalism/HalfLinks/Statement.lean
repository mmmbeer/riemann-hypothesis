import Formalism.ZetaNonvanishingChebyshevWeights
import Formalism.ProductFormula.StatementOCCM

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.CMTypeGaloisData

open Formalism

abbrev Gal3 := Fin 3 → ℤˣ

def cc : Gal3 := fun _ => -1

def oddSet : Fin 4 → Finset (Fin 3) := ![{0}, {1}, {2}, Finset.univ]

def oddChar (i : Fin 4) (g : Gal3) : ℤ := ∏ j ∈ oddSet i, ((g j : ℤˣ) : ℤ)

def frob (chi : Fin 4 → ℕ → ℝ) (n : ℕ) : Gal3 := fun i => if chi (Fin.castSucc i) n = -1 then -1 else 1

def Unram (chi : Fin 4 → ℕ → ℝ) (X : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X → Λ n ≠ 0 →
    (∀ i : Fin 3, chi (Fin.castSucc i) n = 1 ∨ chi (Fin.castSucc i) n = -1) ∧
      chi 3 n = chi 0 n * chi 1 n * chi 2 n

def AT (chi : Fin 4 → ℕ → ℝ) (Ψ : Finset Gal3) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, if frob chi n ∉ Ψ then Λ n * (y / n - 1) else 0

def Schi4 (χ : ℕ → ℝ) (y : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * χ n * (y / n - 1)

def Gch (χ : ℕ → ℝ) (ell y : ℝ) : ℝ := Schi4 χ y + y * ell

def tp (x ε B : ℝ) (k : ℕ) (r : ℕ → ℕ) (p : ℕ) : ℝ :=
  x * B / (p : ℝ) ^ (2 * r p) + x ^ ε * (k + x * B / (p * k))

def classC (x ε B : ℝ) (m k : ℕ) (Pc : Finset ℕ) (κ : ℕ → ℝ) (r : ℕ → ℕ) (y0 : ℝ) : ℝ :=
  (∑ p ∈ Pc, Real.log p * (tp x ε B k r p / B + x ^ ε * m * κ p * x / p))
    + (∑ p ∈ Pc.filter (fun p : ℕ => (p : ℝ) ≤ y0), (r p : ℝ) * Real.log p)

structure HrData (θ ε x X : ℝ) (m : ℕ) where

  Pc : Finset ℕ
  κ : ℕ → ℝ
  r : ℕ → ℕ
  Pc_prime : ∀ p ∈ Pc, p.Prime
  Pc_le : ∀ p ∈ Pc, (p : ℝ) ≤ X
  κ_nonneg : ∀ p ∈ Pc, 0 ≤ κ p
  κ_sum : (∑ p ∈ Pc, κ p * Real.log p / p) ≤ x ^ (θ - 1 - ε) / m
  r_pos : ∀ p ∈ Pc, 1 ≤ r p
  r_le : ∀ p ∈ Pc, (r p : ℝ) ≤ x ^ ε
  r_small : ∀ p ∈ Pc, (p : ℝ) ≤ x ^ (1 - θ) → x ^ (1 - θ) * x ^ (1 - θ) ≤ (p : ℝ) ^ (2 * r p)
  r_large : ∀ p ∈ Pc, x ^ (1 - θ) < p → r p = 1

def ATg {G : Type} [DecidableEq G] (frob : ℕ → G) (Bad : Finset ℕ) (Ψ : Finset G) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, if n.minFac ∉ Bad ∧ frob n ∉ Ψ then Λ n * (y / n - 1) else 0

structure HostSizeData (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (X : ℝ) where
  c : G
  c_ne : c ≠ 1
  c_sq : c * c = 1
  nT : ℕ
  types : Fin nT → Finset G
  cm : ∀ t s, s ∈ types t ↔ c * s ∉ types t
  w : Fin nT → ℝ
  w_nonneg : ∀ t, 0 ≤ w t
  w_sum : (∑ t, w t) = 2
  chars : Finset (G →* ℂˣ)
  odd : ∀ ψ ∈ chars, ψ c = -1
  coef : (G →* ℂˣ) → ℝ
  decomp : ∀ s : G, (∑ t, w t * (if s ∉ types t then (1 : ℝ) else 0))
    = 1 - (∑ ψ ∈ chars, coef ψ * ((ψ s : ℂˣ) : ℂ).re)
  Bad : Finset ℕ
  frob : ℕ → G
  chi : (G →* ℂˣ) → ℕ → ℝ
  unram : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X → Λ n ≠ 0 → ∀ ψ ∈ chars,
    chi ψ n = if n.minFac ∈ Bad then 0 else ((ψ (frob n) : ℂˣ) : ℂ).re

structure HalfLinksCore (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (C ε θ x B D : ℝ)
    (m k f : ℕ) where
  host : HostSizeData G (4 * x * (m : ℝ) ^ 2)

  ell : (G →* ℂˣ) → ℝ

  ramP : Finset ℕ
  ram_ge : ∀ q ∈ ramP, D ≤ q
  ram_card : (ramP.card : ℝ) ≤ Real.log D

  L0 : ℝ
  initialLengthNonneg : 0 ≤ L0
  initialLengthLe : L0 ≤ 2 * (k + 2 * m) * f * B
  top : Fin m → ℝ
  low : Fin m → ℝ
  cls : Fin m → ℝ
  ram : Fin m → ℝ

  lift : ∀ j : Fin m,
    B * chebNode m j * (∑ t, host.w t * ATg host.frob host.Bad (host.types t) (x / chebNode m j))
      ≤ x * B * (Real.log (x / chebNode m j) - 1 - Real.eulerMascheroniConstant
          + (∑ ψ ∈ host.chars, host.coef ψ * ell ψ))
        + (top j + low j + cls j + ram j)

  top_le : (∑ j, top j) ≤ C * x ^ ε * (m * B) * (x / m + x * m / k)

  div : ∀ j, low j ≤ C * x ^ ε * f * m * B

  hr : HrData θ ε x (4 * x * (m : ℝ) ^ 2) m

  cls_le : (∑ j, cls j) ≤ C * x ^ ε * (m * B) * classC x ε B m k hr.Pc hr.κ hr.r (x ^ (1 - θ))

  ram_le : ∀ j, ram j ≤ ∑ q ∈ ramP, C * (x * B + L0) * Real.log q / ((q : ℝ) - 1)

structure HalfLinks (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (C ε θ x B D : ℝ)
    (m k f : ℕ) extends HalfLinksCore G C ε θ x B D m k f where

  landau : (∑ ψ ∈ host.chars, host.coef ψ * chebyshevWeightedAverage m x (Gch (host.chi ψ) (ell ψ)))
    ≤ C * Real.sqrt (x * Real.log x) * Real.log D ^ 2

end Formalism.CMTypeGaloisData
