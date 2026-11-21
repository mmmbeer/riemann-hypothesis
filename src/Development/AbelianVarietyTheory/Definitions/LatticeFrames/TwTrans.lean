import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} (p : ι → SplitPt (I.rec7 l Z) k)
    (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)) : Prop :=
  (∃ e : ι ≃ (B.primes X).vT u, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (e i).1) ∧
    ∀ j, j ≤ B.R.m → (∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) ∧ ∀ i, (β j i).IsLat (L j) (Q j i).lat ∧
      ∀ z ∈ L j, ∀ r : Fin ((I.rec7 l Z).sp.X j).rank, r.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∃ s : 𝒪[k],
        (s : k) = (p i).pr (incA (I.rec7 l Z) ((show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)) * z r)) ∧
        (Q j i).HasVal ((β j i).b' *ᵥ fun r' => (p i).pr (incA (I.rec7 l Z) (z r'))) (residue 𝒪[k] s)

def TwLev : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ j, j ≤ B.R.m → ∀ b,
      (∀ i g, g • Q j i = Q j i → ∃ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1) ∧
      ∀ κ ∈ A.U j b, ∃ g : ι → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ i, g i • Q j i = Q j i) ∧
        ∃ κ' ∈ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β j i).gl (g i)).prod * κ'

def TwTrans : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∃ φ' ∈ (I.fm l u a).Fi j, ∀ b y, A.rd θ j hj b φ' y = trc c (A.rd θ j hj b φ y)

end GlobalTheory.AdForm

end
