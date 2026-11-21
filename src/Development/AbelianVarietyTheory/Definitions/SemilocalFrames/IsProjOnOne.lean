import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

def frame (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  I.P v * uMat (x.1 v)

def crd (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (y : Fin I.n → I.E) : EuclideanSpace ℂ (Fin I.n) :=
  WithLp.toLp 2 ((frame I x v)⁻¹ *ᵥ fun i => I.φ v (y i))

def act {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (M *ᵥ y.ofLp)

def SatX (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def SizesGe (I : AutInst) (x : I.GA) (B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), B' < N → N ≤ B → lo ≤ Formalism.HN.sizeQ (bas I) (frm I x) N B'

def SizesLe (I : AutInst) (x : I.GA) (A A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), A' ≤ N →
    Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A N → N ≠ A →
      Formalism.HN.sizeQ (bas I) (frm I x) A N ≤ hi

def Maps (I : AutInst) (Y : Matrix (Fin I.n) (Fin I.n) I.E) (A B : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  ∀ y ∈ A, Y *ᵥ y ∈ B

def omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ) : Set I.GA :=
  {y | y.2 = x.2 ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ,
    (∀ v, Formalism.REAL.inG (I.ε v) (A v) ∧ Formalism.REAL.inG (I.ε v) (Z v)) ∧
    Real.sqrt (∑ v, Formalism.REAL.hs (A v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)) ≤ ρ ∧
    (∀ v, uMat (y.1 v) = uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧
    ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v)}

def IsReps (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) (Fr : B.Hs → B.I.GA → ℂ) : Prop :=
  ∀ P : ℕ, ∀ u ∈ VP B P, GlobalTheory.Dec.IsContRep B (T u) (Fr u) ∧
    (∀ k ∈ B.I.Kg B.g, ∀ y, Fr u (y * (1, k)) = Fr u y) ∧
    ∀ (E : gInf B) (y : B.I.GA),
      HasDerivAt (fun t : ℝ => Fr u (y * ((fun v => expU (t • E v)), 1))) (Fr (dAct B E u) y) 0

def vv (B : RowsAut) {D : ℕ} (Fr : Fin D → B.Hs → B.I.GA → ℂ) (u : B.Hs) (y : B.I.GA) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun i => Fr i u y

end GlobalTheory.Deep
