import Mathlib
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HerGenC

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB Finset NumberField MeasureTheory Formalism.QuantumDeterminants

noncomputable section

open Classical

def ThresholdProductsBounded {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (Θ : ℝ) : Prop :=
  (∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i : ℕ, 2 ≤ i → i ≤ G.r + 1 →
    ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i s : ℕ, 1 ≤ i → 2 ≤ s → s + i ≤ G.r + 2 →
    ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ G.r →
    ∏ w, Sz.lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') ≤ (Θ ^ G.f)⁻¹)

def arData (E : Type) [Field E] [NumberField E] [IsCMField E] (g r : ℕ) (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ)
    (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) : TB.Data E Unit where
  r := r
  f := 0
  K := 5
  av := fun _ _ => 0
  wt := fun _ => 1
  cnt := fun _ => 0
  Wall := {()}
  emp := ()
  emp_mem := by simp
  cnt_emp := rfl
  wt_emp := rfl
  gram := fun _ _ _ _ _ => 0
  Kr := Kr
  K0 := hK0
  Th := fun _ _ _ _ _ => 0
  e := e
  La := fun b s => J.LaB E g r b s
  Lap := fun b s => J.LapB E g r b s
  Lad := fun b => J.LadB E g r b
  Nhat := fun _ _ _ _ _ _ => 0
  szD := fun _ _ => 0
  szL := fun _ _ _ => 0
  vol := fun _ _ => 0

def frS (rd : ℝ) (r b s : ℕ) : ℝ := rd ^ (-(S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ))

abbrev parG {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (x : ι) : M.Par :=
  ⟨G.k, G.r, T, T', (G.place x).u de, (G.place x).u de'⟩

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def vStd {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g rd : ℝ) (p : C.LPt) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  ((√(C.nLoc k r (frS rd r) (D.ptGG (Tz k r Bs.z * Tz k r Bs.z')) p) * (D.bSt (D.kapG g rd) p)⁻¹ : ℝ) : ℂ) •
    B.hsVec (D.vecV Bs ν' m₀ F (D.toStd r g 1 p))

structure PlaceOK {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (x : ι)
    (Bs : B.RealPlaceData G.k G.r Wp Wq) (ν' : Fin (2 * G.r + G.k + 1) → ℂ) (m₀ : B.Mat G.k G.r)
    (F : B.Mat G.k G.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) : Prop where
  hW : Bs.μW Set.univ = 1
  hW' : Bs.μW' Set.univ = 1
  hN : Bs.μN = D.muN G.k G.r
  frame : D.IsBaseFrame Bs ν' m₀
  place : Q.IsPlace (parG G de de' T T' x) Bs.z Bs.z' Bs.π Bs.π'
  smooth : B.CkOn ⊤ (B.GV G.k G.r) F
  decay : ∀ m : ℕ, B.InCC A₀ m F
  eigen : ∀ Y : ℝ, ∀ g ∈ B.GV G.k G.r, Q.CV G.k G.r (Y : ℂ) F g = (((G.place x).P Y : ℝ) : ℂ) • F g

end place

def PlExists : Prop :=
  ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (l0 : ℕ),
    1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.μW Set.univ = 1 → Bs.μW' Set.univ = 1 → Bs.μN = D.muN P.k P.r →
    D.IsBaseFrame Bs ν' m₀ → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∃ p : Pl P Wp Wq, p.l0 = l0 ∧ p.T.base = Bs ∧ p.ν' = ν' ∧ p.m₀ = m₀ ∧ InDDplus2 P l0 p.T.base Cb p.Θ

end

end GlobalTheory.ThA
