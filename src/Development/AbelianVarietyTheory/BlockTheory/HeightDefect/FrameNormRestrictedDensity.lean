import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Core D}

abbrev FrameNorms (T : Core D) (j : ℕ) : Type :=
  ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ

abbrev GenericFrames (T : Core D) (j : ℕ) : Type :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))

def ProdInLattice (h : LawsCore T) (j : ℕ) (wL : WeightFamilies.Wt D j) {N : ℕ} (w : Fin (N + 1) → T.R j) (n : ℕ) : Prop :=
  ∀ s : Fin n → Fin (N + 1), ∃ F : (recB h).Cusp j (WeightAlgebra.wsmul n wL),
    F ∈ (recB h).Mlat j (WeightAlgebra.wsmul n wL) ∧ F.1 = ∏ k, w (s k)

def genNorm {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
    (ka : WeightFamilies.Wt D j) (f : T.R j) (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) : ℝ :=
  nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC hG (wtA ka) ka.n f Z) P

def genSup {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
    (ka : WeightFamilies.Wt D j) (f : T.R j) (Z : Comp (T.Q.Xo j) T.Q.c) (σ : T.Q.c.F →+* ℂ) : ℝ :=
  ⨆ P : ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) σ, genNorm hG fn yP ka f Z P

def IsRestr {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c) (Z : Comp (T.Q.Xo j) T.Q.c) (f f' : T.R j) : Prop :=
  evC hG Z f' = evC hG Z f ∧ ∀ Z' : Comp (T.Q.Xo j) T.Q.c, Z' ≠ Z → evC hG Z' f' = 0

def RestrDensity (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : (recB h).Cusp j ka, F ∈ (recB h).Mlat j ka → ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z F.1 ≠ 0 →
    ∃ F' : (recB h).Cusp j ka, F' ∈ (recB h).Mlat j ka ∧ IsRestr hG Z F.1 F'.1 ∧
      ∀ σ : T.Q.c.F →+* ℂ, (recB h).supN j ka σ F' ≤ genSup hG fn yP ka F.1 Z σ

def ConstBound (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) (C A P : ℝ) (n : ℕ) (wL : WeightFamilies.Wt D j) : Prop :=
  WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size ≤ P * n * wL.size

def LamInputs (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (large₂ : SizeData₂ D) (C A P : ℝ) (wL : WeightFamilies.Wt D j) {N : ℕ} (w : Fin (N + 1) → T.R j)
    (n : ℕ) : Prop :=
  ProdInLattice h j wL w n ∧ RestrDensity h j hG fn yP (WeightAlgebra.wsmul n wL) ∧
    ConstBound large₂ (WeightAlgebra.wsmul n wL) C A P n wL

end GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity
