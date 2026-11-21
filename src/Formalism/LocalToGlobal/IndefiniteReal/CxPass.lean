import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement

section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.IndefiniteEpsilonOperator

structure Pair (G K : Type) [Group G] [Field K] where

  H : Subgroup G

  χ : H →* Kˣ

section Ops

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module K U]

def epOp [Finite G] (σ : Representation K G U) (P : Pair G K) : U →ₗ[K] U :=
  letI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ • ∑ h : P.H, ((P.χ h⁻¹ : Kˣ) : K) • σ (h : G)

def epSp [Finite G] (σ : Representation K G U) (P : Pair G K) : Submodule K U :=
  LinearMap.range (epOp σ P)

def charOf (σ : Representation K G U) (g : G) : K :=
  LinearMap.trace K U (σ g)

def eOp [Fintype G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (ρ : Representation K G U) : U →ₗ[K] U :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, charOf τ x⁻¹ • ρ x

def nOf [Finite G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (P : Pair G K) : ℕ :=
  finrank K (epSp τ P)

end Ops

def la (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G)

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]

def latAt {G : Type} [Group G] [Finite G] (ρ : Representation K G V) (A : Submodule (𝓞 K) V)
    (P : Pair G K) : Submodule (𝓞 K) V :=
  A ⊓ (epSp ρ P).restrictScalars (𝓞 K)

def HtLe (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (U : Submodule K V) (t : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v, 0 < c v) ∧
    (∀ v, ∀ x ∈ U, Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v x) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (c v ^ 2) ≤ t

structure GoodTransferSetting {G : Type} [Group G] [Fintype G] {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V)
    (R : Submodule (𝓞 K) V) (τ : ∀ s, Representation K G (Ws s)) : Prop where

  frame : ∀ v, IsUnit (X v).det

  fg : R.FG

  span : Submodule.span K (R : Set V) = ⊤

  ne_bot : R ≠ ⊥

  roots : ∃ ζ : K, IsPrimitiveRoot ζ (Fintype.card G)

  stable : ∀ g : G, ∀ x ∈ R, ρ g x ∈ R

  unitary : ∀ (g : G) (v : InfinitePlace K) (x : V),
    Formalism.HermitianLatticesTheory.normAt b X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt b X v x

  irred : ∀ s, (τ s).IsIrreducible

  split : ∀ s (f : Ws s →ₗ[K] Ws s), (∀ g, f ∘ₗ τ s g = τ s g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id

  distinct : Function.Injective fun s => charOf (τ s)

  good : ∀ x : V, (∑ s, eOp (τ s) ρ) x = x

end Lat

def M1 {K : Type} [Field K] {G : Type} [Group G] [Finite G] {S : Type} {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 : Pair G K) : Prop :=
  ∀ s, nOf (τ s) P0 = 1

def M2 {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] {S : Type} {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (ρ : Representation K G V) (τ : ∀ s, Representation K G (Ws s)) (P1 : Pair G K)
    (nbar de : ℝ) : Prop :=
  ∀ s, LinearMap.range (eOp (τ s) ρ) ≠ ⊥ →
    (1 - de) * nbar ≤ (nOf (τ s) P1 : ℝ) ∧ (nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Formalism.IndefR.IndefiniteEpsilonOperator
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def prin {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) : CxData A := { X with nP := fun _ => 1 }

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section Prims

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def GUnit (gE : Representation ℂ G X.EE) : Prop := ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

def GEquiv (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), X.Θ t (X.jR t (A.fam.amb.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

def typeSp (gE : Representation ℂ G X.EE) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ X.EE :=
  ⨅ h : P, LinearMap.ker (gE (h : G) - (A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
    {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

def EEg : Submodule ℂ X.EE :=
  LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

def PrincipalInjectiveCommonRange : Prop :=
  Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

def LevType (gE : Representation ℂ G X.EE) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  X.EEl b = EEg A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp A X gE P ψ

end Prims

section Group

variable {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]

def CharsX (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K)) : Prop :=
  ∀ χ : G → K, χ ∈ Xc ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ

def NearConstantMultiplicities (τ : ∀ s, Representation K G (Ws s)) (P1 : Formalism.IndefR.IndefiniteEpsilonOperator.Pair G K) (nbar de : ℝ) : Prop :=
  ∀ s, (1 - de) * nbar ≤ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ∧ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Group

end Formalism.IndefR.CxPass
end
end
