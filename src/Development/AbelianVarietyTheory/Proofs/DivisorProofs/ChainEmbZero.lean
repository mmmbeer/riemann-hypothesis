import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup

noncomputable section

namespace GlobalTheory.ThK.FlagCT

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def chainEmb {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (k : ℕ) : Matrix (Fin d) (Fin (d₁ - 2 * k)) E :=
  Nat.rec (motive := fun k => Matrix (Fin d) (Fin (d₁ - 2 * k)) E) H'.ι (fun k M => M * (pl k).ι) k

def flagX {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) (r : ℕ) :
    Matrix (Fin d) (Fin r) E :=
  Matrix.of fun a k => if k.1 = 0 then H'.x a else (chainEmb H' pl (k.1 - 1) *ᵥ (pl (k.1 - 1)).x) a

def flagY {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) (r : ℕ) :
    Matrix (Fin d) (Fin r) E :=
  Matrix.of fun a k => if k.1 = 0 then H'.y a else (chainEmb H' pl (k.1 - 1) *ᵥ (pl (k.1 - 1)).y) a

variable (σ) in

def unipFlag {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) : Subgroup (UA σ W.J) :=
  Subgroup.closure {u | (∃ A : Matrix (Fin (i + 1)) (Fin (i + 1)) (AE F E), A.BlockTriangular id ∧ (∀ k, A k k = 1) ∧
      mat u * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) * A) ∧
    ∀ z, ∃ a : Fin (i + 1) → AE F E,
      mat u *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) = incM F (chainEmb H' pl i) *ᵥ z + incM F (flagX H' pl (i + 1)) *ᵥ a}

def IsLeviFlag {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) {Y : Spc F E (d₁ - 2 * i)} (h₁ : UA σ Y.J) (h : UA σ W.J) : Prop :=
  mat h * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) ∧
    mat h * incM F (flagY H' pl (i + 1)) = incM F (flagY H' pl (i + 1)) ∧
    mat h * incM F (chainEmb H' pl i) = incM F (chainEmb H' pl i) * mat h₁

end GlobalTheory.ThK.FlagCT

end
