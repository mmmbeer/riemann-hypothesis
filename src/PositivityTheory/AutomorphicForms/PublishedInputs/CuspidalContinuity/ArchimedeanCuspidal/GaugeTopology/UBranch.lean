import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

def Φ0 : Matrix (Fin 2) (Fin 3) F → ℂ := Set.indicator {X | ∀ i j, X i j ∈ 𝒪[F]} 1

def s2 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 2) F → ℂ :=
  sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![ν (unifUnit F), ν⁻¹ (unifUnit F)]

def W0 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 3) F → ℂ := Wp ψ (s2 ψ ν) (Φ0 F)

end D

def UDomA : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν →
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ l : Fin 3 → ℤ, Antitone l →
      W0 ψ ν (torusPow F 3 l) = c₀ * halfModulus F l *
        ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1),
          evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])

def UBranch : Prop :=
  ∀ (α : ℂˣ) (l : Fin 3 → ℤ), Antitone l →
    evalAt ![α, 1, α⁻¹] (schur l) =
      ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1), evalAt ![α, α⁻¹] (schur ![a, b])

end Ad3.LFS
