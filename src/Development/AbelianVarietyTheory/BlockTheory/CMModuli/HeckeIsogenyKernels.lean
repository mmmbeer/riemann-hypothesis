import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjIdeal (H : Host E) (P : Ideal (𝓞 E)) : Ideal (𝓞 E) := P.map (H.bar : 𝓞 E →+* 𝓞 E)

def IsSplitPrimeOff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : 𝓞 E) ∈ P ∧ conjIdeal H P ≠ P ∧ ¬ p ∣ l.M'

section Fibre

variable {k : Type} [Field k]

abbrev Pts (t : SAB H (Sp k)) : Type := 𝟙_ (Over (Sp k)) ⟶ t.G

def KilledBy (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∀ a ∈ I, x ≫ t.act.act a = 1

def KilledByPow (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∃ n : ℕ, KilledBy t (I ^ n) x

def IsHeckeDatum (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) (i : ℕ) (C₀ : Subgroup (Pts t)) : Prop :=
  (∀ a, ∀ x ∈ C₀, x ≫ t.act.act a ∈ C₀) ∧ (∀ x ∈ C₀, KilledBy t (conjIdeal H P) x) ∧
    Finite C₀ ∧ Nat.card C₀ = Ideal.absNorm P ^ i

def heckeKernel (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) : Set (Pts t) :=
  {x | ∃ x₁ x₂ x₃ : Pts t, x = x₁ * x₂ * x₃ ∧
    (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ conjIdeal H P ∧ x₁ ≫ t.act.act a = 1) ∧
    (KilledByPow t (conjIdeal H P) x₂ ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ KilledByPow t P x₃ ∧ ∀ c ∈ C₀, Out.WeilIs t.G t.PP.L (p : ℤ) x₃ c 1)}

end Fibre

example {k : Type} [Field k] (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) : IsHeckeDatum t P 0 ⊥ := by
  refine ⟨fun a x hx => ?_, fun x hx a _ => ?_, inferInstance, by simp⟩
  · have := t.act.hom a
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, MonObj.one_comp]
  · have := t.act.hom a
    rw [Subgroup.mem_bot] at hx
    rw [hx, MonObj.one_comp]

example {k : Type} [Field k] (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (x : Pts t)
    (hx : x ∈ heckeKernel t p P ⊥) : x ^ p = 1 := by
  obtain ⟨x₁, x₂, x₃, rfl, ⟨h₁, -⟩, ⟨-, h₂⟩, ⟨h₃, -⟩⟩ := hx
  rw [Subgroup.mem_bot] at h₂
  have hc : ∀ u v : Pts t, Commute u v := fun u v => mul_comm u v
  rw [(hc _ _).mul_pow, (hc _ _).mul_pow, h₁, h₂, h₃, _root_.mul_one, _root_.mul_one]

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels
