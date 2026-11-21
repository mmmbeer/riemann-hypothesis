import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def RootSys (l : ℕ) (ζ : ℕ → Ω) : Prop := ∀ n, IsPrimitiveRoot (ζ n) (l ^ n) ∧ ζ (n + 1) ^ l = ζ n

def cyclotomicUnit (l : ℕ) (r : ℕ) : (ZMod (l ^ r))ˣ :=
  ZMod.unitOfCoprime (1 + l) (Nat.Coprime.pow_right r (by simp))

def smoothedLayer {r : ℕ} (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l :=
  fun s x => z s x - ((1 + l : ℕ) : Qbar l) * z s (x * cyclotomicUnit l r)

example (j : Ω →+* Qbar l) (ζ : Ω) (hζ : ζ ≠ 0) (b : ℕ) : htv j ζ (fun _ : Unit => Polynomial.X) (fun _ => 1) b = 1 := by
  simp [htv, hζ]

example (r : ℕ) (s : G ℚ Ω) (x : (ZMod (l ^ r))ˣ) :
    smoothedLayer (fun (_ : G ℚ Ω) (_ : (ZMod (l ^ r))ˣ) => (1 : Qbar l)) s x = -((l : ℕ) : Qbar l) := by
  simp [smoothedLayer]

end GlobalTheory.KZ

end
