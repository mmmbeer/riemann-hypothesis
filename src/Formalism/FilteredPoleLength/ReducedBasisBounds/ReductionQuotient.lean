import Mathlib
import Formalism.LogFactorialIndices.StatementIdx

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Polynomial
open scoped ComplexOrder

def ReductionQuotient : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (X Θ N₀ T : Submodule O V), N₀ ≤ Θ → T ≤ Θ → T ≤ X →
    let NK : Submodule O V := (Submodule.span K (N₀ : Set V)).restrictScalars O
    let M₁ : Submodule O V := (X ⊓ NK) ⊔ N₀
    Module.length O (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype) ≤
      Module.length O (↥M₁ ⧸ N₀.comap M₁.subtype) +
        Module.length O (↥X ⧸ ((X ⊓ NK) ⊔ T).comap X.subtype)

def QuotientLength : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (X : Submodule O V) (e be : ℕ) (th : Fin n → V),
    (∀ x ∈ X, ∀ i, ∃ a : O, c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)

def FilteredLength : Prop :=
  ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (n : ℕ) (F : ℕ → Submodule O A),
    F 0 = ⊤ → F n = ⊥ → (∀ k, F (k + 1) ≤ F k) → ∀ N : Submodule O A,
      Module.length O (A ⧸ N) =
        ∑ k ∈ Finset.range n,
          Module.length O (↥(F k) ⧸ (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype)

def LocalAssembly : Prop :=
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' : Submodule O V) (e be n : ℕ) (th : Fin n → V)
    (c : V →ₗ[K] (Fin n → K)) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W) (a a' : O),
    let X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V))
    let NK : Submodule O V := (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    LinearMap.ker c ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    (∀ x ∈ M, ∀ i, ∃ u : O, c x i = (algebraMap O K ϖ) ^ (-(be : ℤ)) * algebraMap O K u) →
    a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
    X ⊓ NK ≤ N' → N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
      Module.length O (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype) ≤
        Module.length O (↥AA' ⧸ AA.comap AA'.subtype) +
          Module.length O (↥AA ⧸ N₁'.comap AA.subtype) +
          Module.length O (↥Zm ⧸ Z.comap Zm.subtype) +
          (((((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)).toNat : ℕ) : ℕ∞)

def OrdCeil : Prop :=
  ∀ (n : ℤ) (x : ℝ), -(x + 1) < (n : ℝ) → -⌈x⌉ ≤ n

def PoleOrderGood : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ) (e : ℤ), 1 ≤ ep → 0 ≤ c' → 0 ≤ vet →
    ν ≤ νs + c' * vet → (∃ n : ℤ, (ep : ℝ) * ν = n) → (T : ℝ) * νs ≤ e →
      ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def PoleOrderBad : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ), 1 ≤ ep → 1 ≤ T → 0 ≤ c' → 0 ≤ vet → ν ≤ νs + c' * vet →
    let e : ℤ := ⌈(T : ℝ) * (νs + 1)⌉
    ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def LevelsSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (mm : ι → ℤ) (v : ι → ℝ) (T : ℕ) (c' : ℝ),
    (∀ z, (mm z : ℝ) ≤ ep z * T * c' * v z) →
      ∑ z, (mm z : ℝ) * f z ≤ T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

def JetRank : Prop :=
  ∀ D T : ℕ, D + 1 ≤ T → Set.ncard {α : Fin D → ℕ | ∑ i, α i ≤ T - D - 1} = (T - 1).choose D

def ShareExponent : Prop :=
  ∀ (D T : ℕ) (δ xL xF : ℝ), 0 < δ → xL ≤ δ + xL / 4 → xF ≤ ((D : ℝ) + 4) * xL →
    xF + T * δ ≤ ((T : ℝ) + 2 * D + 6) * δ

def ShareRho : Prop :=
  ∀ (D T : ℕ) (d ρ ρ' m δ : ℝ), 0 ≤ δ → ρ ≤ d - ((T - 1).choose D : ℝ) * δ → d = ρ' + m →
    m ≤ δ * ((T + 3 * D + 6).choose D : ℝ) → ((T - 1).choose D : ℝ) * δ ≤ d →
    (D : ℝ) * (3 * D + 7) ≤ (T : ℝ) - D →
      ρ ≤ ρ' + 2 * D * (3 * D + 7) * d / ((T : ℝ) - D)

def SFChain : Prop :=
  ∀ (ξn lam d' ρ φ t p RR T c : ℝ), 0 < ξn → 0 ≤ lam → ξn * lam ≤ d' → 0 ≤ ρ → 0 ≤ φ →
    φ ≤ 2 * ρ * lam ^ 2 → t ≤ ξn ^ 2 * p / 4 → 1 ≤ RR → 0 ≤ T * c →
    RR * T * c * d' ^ 2 * ρ / 2 < t →
      T * c * φ < p

def FilIntegerStep : Prop :=
  ∀ (νF νE : ℤ) (T : ℕ) (c φ μ : ℝ), μ ≤ νF → (T : ℝ) * c * φ < μ → (νE : ℝ) ≤ c * φ →
    (T : ℤ) * νE + 1 ≤ νF

def HeightAbsorb : Prop :=
  ∀ (HL Hde X Y a : ℝ), 0 ≤ a → a ≤ 1 / 2 → 0 ≤ Y → HL ≤ X + a * Hde → Hde ≤ HL + Y →
    HL ≤ 2 * max X 0 + Y

end Formalism.LatticeBaseChangeAlt
