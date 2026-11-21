import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.PropEG2

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace Ad3P

def Lifts (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ) (π : TR.CuspSub ℚ 2) : Prop :=
  (∀ v, π.HasInfChar v (infOf ![0, 1 - (k : ℤ)])) ∧
  ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => X - C b).prod =
    X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))

def SEig : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    Ad3.IsForm k N χ g.f g.a ∧ Ad3.IsEig k N χ g.a

def AdjEig : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (π : TR.CuspSub ℚ 2),
    Lifts k N χ g π → (∃ η : HChar ℚ, η ≠ 1 ∧ η ^ 2 = 1 ∧ SelfTw π.HasSat η) ∨ ∃ P : TR.CuspSub ℚ 3,
      (∀ v (x y : ℂ), π.HasInfChar v {x, y} → P.HasInfChar v {x - y, 0, y - x}) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, adSys π.HasSat w B ∧ P.HasSat w B

end Ad3P
