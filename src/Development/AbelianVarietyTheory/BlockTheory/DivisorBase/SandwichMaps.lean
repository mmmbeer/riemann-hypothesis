import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

section Eigen

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Λ : Type} [CommRing Λ] {h : ℕ}

def eig (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) : Submodule C (Fin h → C) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
    (algebraMap O C (σ a))

def quotLattice (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) : Set (eig C ρ τ) :=
  {x | ∃ t : Fin h → O, (fun i => algebraMap O C (t i)) - (x : Fin h → C) ∈
    ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1}

abbrev detLine (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) : Type :=
  ⋀[C]^N (eig C ρ τ)

def detLattice (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) :
    Submodule O (detLine C ρ τ N) :=
  Submodule.span O
    {w | ∃ x : Fin N → eig C ρ τ, (∀ i, x i ∈ quotLattice C ρ τ) ∧ w = exteriorPower.ιMulti C N x}

example (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) (a : O) (w : detLine C ρ τ N) :
    a • w = algebraMap O C a • w := (algebraMap_smul C a w).symm

end Eigen

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h h' : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def actT (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρT a).map (padicToO p O)

def actH (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρM a).map (fontaineTheta O p)

def redC {m n : ℕ} (X : Matrix (Fin m) (Fin n) (Ainf p O)) : (Fin n → C) →ₗ[C] (Fin m → C) :=
  Matrix.toLin' (X.map ((algebraMap O C).comp (fontaineTheta O p)))

def alC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.F

def bC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.G

def IsIota (D : Datum ε h Λ) (τ : Λ →+* O) (N : ℕ)
    (ι : detLine C (actT D) τ N →ₗ[C] detLine C (actH D) τ N) : Prop :=
  ∀ (x : Fin N → eig C (actT D) τ) (y : Fin N → eig C (actH D) τ),
    (∀ i : Fin N, (i : ℕ) < D.lieRank τ → (x i : Fin h → C) = bC C D (y i)) →
    (∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) → (y i : Fin h → C) = alC C D (x i)) →
    ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y

end Datum

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
