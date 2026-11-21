import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames

variable {D : D7}

section Local

variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

def rowMat (c p : ℕ) (u : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = p then u s else 0) 0

def scal (γ : kˣ) (κ : ℕ → k) (t₁ : kˣ) (i : ℕ) : k := (t₁ : k) * ∏ j ∈ Finset.range i, κ j * ((γ⁻¹ : kˣ) : k)

def coef (σ : ℕ) (a : k) (i : ℕ) : k := if i < σ then 1 else if i = σ then a else -1

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def opRow (χ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin 1) n' k) : ℂ :=
  GlobalTheory.RootEx.opE χ ν p (fun y => Φ (y + rowMat c p (x (Sum.inr 0)))) (x.submatrix Sum.inl id)

end Local

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def loc (p : SplitPt D k) (a : D.host.E) : k := p.pr (incA D a)

def up {S T : HSp D} (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : WO S T :=
  Matrix.map ((β.b * x : Matrix (Fin T.rank) n' k) * α.b' : Matrix (Fin T.rank) (Fin S.rank) k) p.sec

end Frames

example {k : Type} [Field k] (γ t₁ : kˣ) (κ : ℕ → k) (i : ℕ) : (γ : k) * scal γ κ t₁ (i + 1) = κ i * scal γ κ t₁ i := by
  simp only [scal, Finset.prod_range_succ, Units.val_inv_eq_inv_val]
  field_simp

example {k : Type} [Field k] (a : k) : (scal 1 (coef 1 a) 1 0, scal 1 (coef 1 a) 1 1, scal 1 (coef 1 a) 1 2,
    scal 1 (coef 1 a) 1 3) = (1, 1, a, -a) := by
  simp [scal, coef, Finset.prod_range_succ]

end GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames

end
