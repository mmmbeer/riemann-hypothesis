import Mathlib
import Formalism.ResultantValuation.KoszulSecondDifferential
import Formalism.ResultantValuation.BoundedCubic
import Formalism.CyclotomicNorms.StatementA
import Formalism.CyclotomicNorms.DiscardKernel
import Formalism.CyclotomicNorms.TWAbsUniform

open Finset Polynomial Formalism.CyclotomicNorms Formalism.ResultantValuation

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.TW

def CentralIdempotentIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G]
    (e : MonoidAlgebra K G), e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * e.coeff g)

def CutOperator : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K]
    [Algebra O K] [IsFractionRing O K] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ρ : Representation K G V) (Msup : Submodule O V) (U : Subgroup G) (ψU : U →* Kˣ)
    (e : MonoidAlgebra K G),
    (∀ g, ∀ v ∈ Msup, ρ g v ∈ Msup) → e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ v ∈ Msup, (∀ u : U, ρ u v = ((ψU u : Kˣ) : K) • v) →
      ρ.asAlgebraHom ((Fintype.card G : K) • e) v ∈ Msup ∧
      (∀ u : U, ρ u (ρ.asAlgebraHom ((Fintype.card G : K) • e) v) =
        ((ψU u : Kˣ) : K) • ρ.asAlgebraHom ((Fintype.card G : K) • e) v) ∧
      ρ.asAlgebraHom e (ρ.asAlgebraHom ((Fintype.card G : K) • e) v) =
        ρ.asAlgebraHom ((Fintype.card G : K) • e) v ∧
      (ρ.asAlgebraHom e v = v →
        ρ.asAlgebraHom ((Fintype.card G : K) • e) v = (Fintype.card G : K) • v) ∧
      ∀ T : V →ₗ[K] V, (∀ g w, T (ρ g w) = ρ g (T w)) →
        T (ρ.asAlgebraHom ((Fintype.card G : K) • e) v) =
          ρ.asAlgebraHom ((Fintype.card G : K) • e) (T v)

def IsLat (O K : Type) {V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V]
    [Module O V] [Module K V] (M : Submodule O V) : Prop :=
  M.FG ∧ Submodule.span K (M : Set V) = ⊤

def relLen {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℕ∞ :=
  Module.length O (↥M ⧸ N.comap M.subtype)

def sIdx {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℤ :=
  ((relLen M N).toNat : ℤ) - ((relLen N M).toNat : ℤ)

def scaleLat {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (c : O)
    (N : Submodule O V) : Submodule O V :=
  N.map (LinearMap.lsmul O V c)

def IndexAdditive : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M N P : Submodule O V),
    IsLat O K M → IsLat O K N → IsLat O K P →
    relLen M N ≠ ⊤ ∧ sIdx M N + sIdx N P = sIdx M P

def IndexScale : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M N : Submodule O V) (ϖ : O) (u : Oˣ) (n : ℕ),
    IsLat O K M → IsLat O K N → Irreducible ϖ →
    sIdx M (scaleLat ((u : O) * ϖ ^ n) N) = sIdx M N + (Module.finrank K V : ℤ) * n

def IndexDet : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (d : ℕ) (b : Module.Basis (Fin d) K V) (w : Fin d → V)
    (ϖ : O) (u : Oˣ) (n : ℤ), Irreducible ϖ →
    b.det w = algebraMap O K (u : O) * (algebraMap O K ϖ) ^ n →
    sIdx (Submodule.span O (Set.range b)) (Submodule.span O (Set.range w)) = n

def ExportTransfer : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] (M B N N' : Submodule O V) (c : O) (e : ℕ) (ε : ℝ),
    IsLat O K M → IsLat O K B → IsLat O K N → IsLat O K N' → c ≠ 0 → 0 < e →
    (sIdx B (scaleLat c N') : ℝ) / e ≤ (sIdx B (scaleLat c N) : ℝ) / e + ε →
    (sIdx M N' : ℝ) / e ≤ (sIdx M N : ℝ) / e + ε

def LengthBaseChange : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ),
    Irreducible ϖ → Irreducible ϖ' → algebraMap O O' ϖ = (u : O') * ϖ' ^ e → 0 < e →
    ∀ (X : Type) [AddCommGroup X] [Module O X], Module.length O X ≠ ⊤ →
      Module.length O' (TensorProduct O O' X) = (e : ℕ∞) * Module.length O X

abbrev GLrt (F : Type) [Field F] (r t : ℕ) : Type := GL (Fin r ⊕ Fin t) F

def inU {F : Type} [Field F] {r t : ℕ} (g : GLrt F r t) : Prop :=
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₁ = 0 ∧
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ = 1 ∧
  (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₂ = 1

open Classical in

def chiVal {F R : Type} [Field F] [CommRing R] {r t : ℕ} (ψ : Fˣ →* Rˣ) (g : GLrt F r t) : R :=
  if h : (g : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₂.det ≠ 0 then
    ((ψ (Units.mk0 _ h) : Rˣ) : R) else 0

open Classical in

def idemOf {F K : Type} [Field F] [Fintype F] [Field K] {r t : ℕ} (ψ : Fˣ →* Kˣ)
    (S : GLrt F r t → Prop) : MonoidAlgebra K (GLrt F r t) :=
  ((Nat.card {g : GLrt F r t // S g} : K))⁻¹ •
    ∑ᶠ p : {g : GLrt F r t // S g}, MonoidAlgebra.single (p : GLrt F r t) (chiVal ψ (p : GLrt F r t))⁻¹

open Classical in

def ComplementCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (r t : ℕ), Module.finrank F V = r + t → ∀ v : Fin r → V,
    Nat.card {U : Submodule F V //
        Module.finrank F U = t ∧ Submodule.span F (Set.range v) ⊔ U = ⊤} =
      if LinearIndependent F v then Fintype.card F ^ (r * t) else 0

def HeckeDetFactors : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (d r : ℕ) (A : Fin (r + 1) → Matrix (Fin d) (Fin d) k),
    A 0 = 1 →
    ∃ (n : ℕ) (α : Fin n → k), n ≤ r * d ∧
      (∑ j : Fin (r + 1), (Polynomial.X : k[X]) ^ (j : ℕ) • (A j).map Polynomial.C).det =
        ∏ i, (1 - Polynomial.C (α i) * Polynomial.X)

def BoundedCubic : Prop :=
  ∀ (G : Type) [AddCommGroup G] (φ : G → ℝ), (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
    (∃ c : ℝ, ∀ x y z, thirdDiff φ x y z = c) → ∀ x, φ x = φ 0

def UnitBallLattice : Prop :=
  ∀ (K V : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V] [FiniteDimensional K V]
    (ϖ : K), ‖ϖ‖ < 1 → (∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) →
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ v : V, ‖v‖ ≤ 1 ↔ ∀ i, ‖b.repr v i‖ ≤ 1

end Formalism.IrreducibleCountingLemmas.TW
