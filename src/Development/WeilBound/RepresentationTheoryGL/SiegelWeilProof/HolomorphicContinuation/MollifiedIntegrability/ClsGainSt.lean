import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

abbrev MC (n : ℕ) := Fin n → Fin n → ℂ

def eU (a b : Fin n) : MC n := fun i j => if i = a ∧ j = b then 1 else 0

def cay (F : MC n → ℂ) (B : MC n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F B (fun k => eU (σ k) k)

def OmS (s : ℂ) : Set (MC n) :=
  {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0 ∧ (1 + (Complex.I * s) • Matrix.of B).det ≠ 0 ∧
    (1 + Matrix.of B * Matrix.of B).det ∈ Complex.slitPlane}

def clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) : ℂ :=
  Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) *
    ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p * ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) R

def Ext : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → IsOpen (OmS (n := n) s) ∧ (∀ y : E n, (herm y : MC n) ∈ OmS s) ∧
    ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
      AnalyticOnNhd ℂ (clsC s z p q R) (OmS s) ∧ ∀ y, clsC s z p q R (herm y) = cls s z p q R y

def Chain : Prop :=
  ∀ (n : ℕ) (U : Set (MC n)) (F : MC n → ℂ), IsOpen U → (∀ y : E n, (herm y : MC n) ∈ U) → AnalyticOnNhd ℂ F U →
    ∀ N y, (Delta^[N] (fun y : E n => F (herm y))) y = (cay^[N] F) (herm y)

end PositivityTheory.Rg.Sw.WR.Z
