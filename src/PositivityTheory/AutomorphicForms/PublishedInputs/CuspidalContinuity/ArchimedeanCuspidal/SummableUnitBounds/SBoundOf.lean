import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology Finset
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.LU

def hc (w : Fin 3 → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ Icc 0 m, ∑ z ∈ Icc 0 x, w 0 ^ z * w 1 ^ (x - z) * w 2 ^ (m - x)

def SPsi : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ x ∈ 𝒪[F], Circle.coeHom.compAddChar ψ x = 1

def SDg : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ a b c : Fˣ, ∃ k ∈ integralGL F 3,
      (dg a b c : GL (Fin 3) F) = torusPow F 3 ![ord (a : F), ord (b : F), ord (c : F)] * k

def SGT : Prop :=
  ∀ (A B : ℕ), B ≤ A → ∀ w : Fin 3 → ℂˣ,
    evalAt w (schur ![(A : ℤ), B, 0]) =
      ∑ x ∈ Icc B A, ∑ y ∈ range (B + 1), ∑ z ∈ Icc y x,
        (w 0 : ℂ) ^ z * (w 1 : ℂ) ^ (x + y - z) * (w 2 : ℂ) ^ (A + B - x - y)

def SBound : Prop :=
  ∀ w : Fin 3 → ℂˣ, (∀ i, ‖(w i : ℂ)‖ = 1) → ∀ l : Fin 3 → ℤ, Antitone l →
    ‖evalAt w (schur l)‖ ≤ 4 ^ (l 0 - l 2).toNat

def SShell : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ g : ℤ → ℂ, Summable (fun k => ‖g k‖) →
      Integrable (fun a : Fˣ => g (ord (a : F))) (multHaar F) ∧
        ∫ a : Fˣ, g (ord (a : F)) ∂multHaar F = ∑' k, g k

def SBoundOf : Prop := SGT → SBound

end Ad3.LU
