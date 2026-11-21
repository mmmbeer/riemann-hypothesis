import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusThetaNorms

open NumberField Complex ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def riem (D : FD.Data E r) (v w : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-(D.κ0 / 2) * FD.herm D.Gm v w)

def embR (D : FD.Data E r) (v : Fin r → E) : D.Ψ → Fin r → ℂ := fun τ => FD.Data.emb τ.1 v

def IsAdaptedON (D : FD.Data E r) (x e : FD.Frame D.Ψ r) : Prop :=
  (∃ b ∈ FD.Bor D.Ψ r, e = FD.rmul x b) ∧
    ∀ (τ : D.Ψ) (a b : Fin r),
      (D.c τ : ℂ) * FD.hermC τ.1 D.Gm (FD.col (FD.mat e τ) a) (FD.col (FD.mat e τ) b) =
        if a = b then ((FD.sgn D.p0 a : ℝ) : ℂ) else 0

structure TorusAt (D : FD.Data E r) (w0 : 𝓞 E) (x : FD.Frame D.Ψ r) where

  X : I2.PT E
  rank_eq : X.r = r

  dim_mem : ∀ τ : D.Ψ, X.dim τ.1 = r - D.p0

  dim_conj : ∀ τ : D.Ψ, X.dim (ComplexEmbedding.conjugate τ.1) = D.p0

  e : FD.Frame D.Ψ r
  e_adapted : IsAdaptedON D x e

  φ : (D.Ψ → Fin r → ℂ) → I2.Vsp X.dim

  φ_mem : ∀ (w : D.Ψ → Fin r → ℂ) (τ : D.Ψ) (i : Fin (X.dim τ.1)) (a : Fin r),
    (a : ℕ) = D.p0 + i →
      φ w ⟨τ.1, i⟩ = -((D.c τ : ℂ) * FD.hermC τ.1 D.Gm (w τ) (FD.col (FD.mat e τ) a))

  φ_conj : ∀ (w : D.Ψ → Fin r → ℂ) (τ : D.Ψ)
    (i : Fin (X.dim (ComplexEmbedding.conjugate τ.1))) (a : Fin r),
    (a : ℕ) + i + 1 = D.p0 →
      φ w ⟨ComplexEmbedding.conjugate τ.1, i⟩ =
        conj ((D.c τ : ℂ) * FD.hermC τ.1 D.Gm (w τ) (FD.col (FD.mat e τ) a))

  lattice : ∀ y : I2.Vsp X.dim, y ∈ X.L ↔ ∃ v ∈ D.Λ, y = φ (embR D v)

  eps_eq : ∀ v ∈ D.Λ,
    (X.eps (φ (embR D v)) : ℝ) = Real.cos (Real.pi * (riem D v ((w0 : E) • v) : ℝ))

  s : (Fin 1 → I2.Vsp X.dim) → ℂ
  s_mem : s ∈ X.Sec 1 1
  s_ne : s ≠ 0
  s_gen : ∀ F ∈ X.Sec 1 1, ∃ z : ℂ, F = z • s

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : I2.Vsp dim →ₗ[ℂ] I2.Vsp dim where
  toFun := I2.act α
  map_add' v w := by ext i; simp [I2.act, mul_add]
  map_smul' z v := by ext i; simp [I2.act, mul_left_comm]

namespace TorusAt

variable {D : FD.Data E r} {w0 : 𝓞 E} {x : FD.Frame D.Ψ r} (T : TorusAt D w0 x)

end TorusAt

end

end GlobalTheory.IndefiniteRowSideFullHecke.TorusThetaNorms
