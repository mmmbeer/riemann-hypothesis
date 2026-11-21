import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
  NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnifIdele (P : HeightOneSpectrum (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧
    (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)

def IsUnramAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ e f : AE D, IsPrimeIdem P e f ∧ ∀ x : (AE D)ˣ, (x : AE D) = e * (x : AE D) + (1 - e) →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

open Classical in

def chiAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : ℂ :=
  if h : IsUnramAt χ P ∧ ∃ x, IsUnifIdele P x then ((χ h.2.choose : Circle) : ℂ) else 0

def normP (P : HeightOneSpectrum (𝓞 D.host.E)) : ℕ := Ideal.absNorm P.asIdeal

def lfac (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) (s : ℂ) : ℂ :=
  (1 - chiAt χ P * (normP P : ℂ) ^ (-s))⁻¹

def lEuler (χ : (AE D)ˣ →* Circle) (s : ℂ) : ℂ := ∏' P : HeightOneSpectrum (𝓞 D.host.E), lfac χ P s

def NotRootUnity (D : D7) : Prop :=
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a : (AF D.host.F)ˣ, χ (idF D a) = 1) →
    (∃ τ a, HasInfExp D χ τ a ∧ a ≠ 0) →
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), Nat.Prime (normP P) →
      ((normP P : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 →
      IsUnramAt χ P → ∀ n : ℕ, 0 < n → chiAt χ P ^ n ≠ 1

end Formalism.IndefR.Mi

end
