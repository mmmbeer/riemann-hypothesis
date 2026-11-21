import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rootPair (X : Data E r) (v : X.Ψ → Fin r → ℝ) (e : Ent X) : ℝ :=
  if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then v e.1 e.2.1.1 - v e.1 e.2.1.2
  else v e.1 e.2.1.2 - v e.1 e.2.1.1

def vdeg (X : Data E r) (v : X.Ψ → Fin r → ℝ) : ℝ := ∏ e : Ent X, rootPair X v e

open Classical in

def covol (X : Data E r) : ℝ≥0∞ :=
  if h : ∃ FF, IsFundSet X (x0F X) FF then muF X (x0F X) h.choose else 0

def ChartSpec (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) : Prop :=
  ∀ i : X.dom, q X i ∈ (e i).source ∧ e i (q X i) = 0 ∧
    ∀ z ∈ (e i).target, ∃ h : cpt X i.1 z ∈ X.dom, (e i).symm z = q X ⟨_, h⟩

def frE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (i : X.dom) (y : Yq X) : Frame X.Ψ r :=
  cpt X i.1 (e i y)

open Classical in

def tgE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (i j : X.dom) (y : Yq X) :
    GL (Fin r) E :=
  if h : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, frE X e i y = lact γ (rmul (frE X e j y) b) then h.choose else 1

open Classical in

def tbE (X : Data E r) (e : X.dom → OpenPartialHomeomorph (Yq X) (V (nd X))) (i j : X.dom) (y : Yq X) :
    Frame X.Ψ r :=
  if h : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, frE X e i y = lact γ (rmul (frE X e j y) b)
  then h.choose_spec.2.choose else 0

end GlobalTheory.CompanionTheory.Ar.Deg
