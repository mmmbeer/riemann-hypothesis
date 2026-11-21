import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound

namespace GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zAt {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (u : V (nd X)) : V (nd X) :=
  WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) u) / Fl.w0 (cpt X (Fl.xs j) u)

def VanOrd {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (a : ℕ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∀ j : Fin Fl.δ, (fun u : V (nd X) => f (cpt X (Fl.xs j) u)) =O[𝓝 0] fun u => ‖zAt Fl j u‖ ^ a

def GapsPairing (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i) ∧
    ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)

theorem VanOrd.add {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ}
    {f g : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (hg : VanOrd Fl a g) :
    VanOrd Fl a fun x => f x + g x := fun j => (hf j).add (hg j)

theorem VanOrd.eq_zero {X : Data E r} {Xa : ArchInM X} {Fl : FlatM X Xa} {a : ℕ} (ha : a ≠ 0)
    {f : Frame X.Ψ r → ℂ} (hf : VanOrd Fl a f) (j : Fin Fl.δ)
    (hs : ∀ k, Fl.s k (cpt X (Fl.xs j) 0) = 0) : f (cpt X (Fl.xs j) 0) = 0 := by
  obtain ⟨C, hC⟩ := (hf j).bound
  have h := hC.self_of_nhds
  have hz : zAt Fl j 0 = 0 := by
    ext k
    simp [zAt, hs k]
  simp only [hz, norm_zero, zero_pow ha, mul_zero] at h
  exact norm_le_zero_iff.mp h

end

end GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction
