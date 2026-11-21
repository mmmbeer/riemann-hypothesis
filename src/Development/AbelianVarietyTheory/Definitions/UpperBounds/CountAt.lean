import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

noncomputable section

namespace GlobalTheory.UpTie

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def domSpan (X : Data E r) (A : Set (Frame X.Ψ r → ℂ)) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  Submodule.span ℂ ((fun f => X.dom.indicator f) '' A)

def deepM (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  domSpan X {P | ∃ (α : Fin (nd X) → ℕ) (g : Frame X.Ψ r → ℂ), ∑ i, α i = Xa.T - nd X ∧
    g ∈ X.SS (Xa.Fp + nd X • Xa.L) ∧ P = fun x => monoM X Fl.s α x * g x}

def JetInj (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Prop :=
  ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L), VanS X Fl.xs Fl.s (Xa.T + nd X + 7) f → ∀ x ∈ X.dom, f x = 0

end Model

section Record

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def Vc (h : LawsP T) (j : ℕ) (u : WeightFamilies.Wt D j) : Submodule ℂ (∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  Submodule.span ℂ (Set.range fun F : (recB h.toLawsCore).Cusp j u =>
    (fun k => rdR h j F k : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ))

def Wc (h : LawsP T) (j : ℕ) (u : WeightFamilies.Wt D j) (c1 : ℝ) :
    Submodule ℂ (∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  Submodule.span ℂ {P | P ∈ Vc h j u ∧ ∀ k, P k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA u) u.n k) c1}

def mono (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (io : KT T j G.N →+* ℂ) (α : Fin (WeightFamilies.dimY D j) → ℕ) (e : ℕ) (k : (T.U j T.σ₀).Comp)
    (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) : ℂ :=
  (∏ i, rdSec h j hj G io i.succ k x ^ α i) * rdSec h j hj G io 0 k x ^ e

structure Gen (h : LawsP T) (j : ℕ) where
  u : WeightFamilies.Wt D j
  α : Fin (WeightFamilies.dimY D j) → ℕ
  e : ℕ
  θ : (recB h.toLawsCore).Cusp j u

def Zc (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ) (S : Scal (recB h.toLawsCore)) (TT : ℕ) :
    Submodule ℂ (∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  Submodule.span ℂ {P : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ |
      ∃ (α : Fin (WeightFamilies.dimY D j) → ℕ) (θ : (recB h.toLawsCore).Cusp j ((recPlus h j hj).wF0 wL wF)),
        ∑ i, α i = a0 D j TT ∧ θ ∈ (recPlus h j hj).Thc S.s0 ((recPlus h j hj).wF0 wL wF) ∧
        P = fun k x => mono h j hj G io α 0 k x * rdR h j θ k x}

def CountAt (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ) (S : Scal (recB h.toLawsCore)) (TT d : ℕ) : Prop :=
  (Module.finrank ℂ (Zc h j hj G io S TT) : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / TT

end Record

end GlobalTheory.UpTie
