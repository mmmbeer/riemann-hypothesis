import Mathlib

section
noncomputable section

open Finset Matrix Filter Topology MeasureTheory

namespace PositivityTheory.RgTw

def prev {R : Type} [Zero R] (q : ℕ → R) : ℕ → R
  | 0 => 0
  | k + 1 => q k

def IsMQ {ι R : Type} [Fintype ι] [CommRing R] [Algebra ℂ R] (D : ι → Derivation ℂ R R) (s : ι → R) (P : ℕ → R)
    (Q : ι → ℕ → R) : Prop :=
  (∀ k : ℕ, (∑ a, s a ^ 2) * P k + (2 * (k : ℤ) + 2 - Fintype.card ι) • P (k + 1) =
      ∑ i, (D i (Q i k) + (∑ a, s a * D i (s a)) * prev (Q i) k)) ∧
    (∀ k, (2 * k < Fintype.card ι ∨ Fintype.card ι < k) → P k = 0) ∧
    ∀ i k, (2 * k + 1 < Fintype.card ι ∨ Fintype.card ι ≤ k) → Q i k = 0


end PositivityTheory.RgTw
end
end

section
noncomputable section

open MvPolynomial Matrix
open scoped ContDiff

namespace PositivityTheory.RgTw

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev G (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℂ

abbrev Poly (n : ℕ) := MvPolynomial (Fin 4 × Fin n × Fin n) ℂ

def Xm (j : Fin 4) : Matrix (Fin n) (Fin n) (Poly n) := fun a b => X (j, a, b)

def ev (d : Mat n) : Poly n →+* ℂ := MvPolynomial.eval fun x => ![d, dᴴ, d⁻¹, dᴴ⁻¹] x.1 x.2.1 x.2.2

def dZ (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  MvPolynomial.mkDerivation ℂ fun x =>
    (if (x.1 : ℕ) < 2 then -1 else 1 : Poly n) * (Z.map C * Xm x.1 + Xm x.1 * Z.map C : Matrix (Fin n) (Fin n) (Poly n)) x.2.1 x.2.2

def sigP (n : ℕ) : Matrix (Fin n) (Fin n) (Poly n) := Xm 0 * Xm 1 - Xm 3 * Xm 2

def hb (p : Fin n × Fin n) : Mat n :=
  if p.1 = p.2 then Matrix.single p.1 p.1 1
  else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) • (Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1)
  else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)

def sP (p : Fin n × Fin n) : Poly n := Matrix.trace (sigP n * (hb p).map C)

def uM (d : Mat n) : ℝ := (∑ p, (ev d (sP p)).re ^ 2) / 2

def th (g : G n) : G n := (star g)⁻¹

theorem th_one : th (1 : G n) = 1 := by simp [th]

def tw (x d : G n) : G n := x⁻¹ * d * th x

def twCent (d : G n) : Subgroup (G n) where
  carrier := {x | d * th x = x * d}
  one_mem' := by simp [th]
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, th, star_mul, _root_.mul_inv_rev] at *
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, th, star_inv, inv_inv] at *
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hx, inv_mul_cancel_right]

def IsInv (τ : Poly n) : Prop :=
  (∀ p, dZ (hb p) τ = 0) ∧ ∀ (x d : G n), ev (tw x d : G n).val τ = ev d.val τ

def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0

def bas (H : ℝ → ℝ) (P : Poly n) (d : G n) : ℂ := (H (uM d.val) : ℂ) * ev d.val P

def Shape (n m : ℕ) : Submodule ℂ (G n → ℂ) :=
  Submodule.span ℂ {φ | ∃ H P, IsCutFn H ∧ P.totalDegree ≤ m ∧ φ = bas H P}

def fam (F : ℝ → ℝ) (τ : Poly n) (P : ℕ → Poly n) (t : ℝ) (d : G n) : ℂ :=
  ∑ k ∈ Finset.range (n * n + 1), ((t ^ (2 * (k : ℤ) - (n * n : ℕ)) : ℝ) : ℂ) *
    bas (fun x => iteratedDeriv k F (t ^ 2 * x)) (τ * P k) d

def topP (n : ℕ) : Poly n := (Matrix.of fun p q : Fin n × Fin n => dZ (hb p) (sP q)).det

end PositivityTheory.RgTw
end
end
