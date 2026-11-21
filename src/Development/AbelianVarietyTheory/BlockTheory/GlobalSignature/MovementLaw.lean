import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def AgreeOff (T : ℕ) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((T : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂

def InRangeOf {K : Type} [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x

def relOrd (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : ℤ := ordDet P N₁ - ordDet P N₂

end Generic

open Classical in

def JetsIn {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (deg : X.Tau → ℤ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) : Prop :=
  ∀ x, Ξ x ≠ 0 → ∀ m : DVar X.Tau a b →₀ ℕ,
    (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
    ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

section Scalar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def muVp (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ := (mUof Ch mu i P)⁻¹

def moveScal (u : Pr.Word) (i : ℕ) {a b : ℕ} (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  ∏ P ∈ Pr.vT u, ((muVp Ch mu i P ^ (-relOrd P N₁ N₂ + relOrd P N₁' N₂') : X.Kˣ) : X.K) *
    ((Pr.T u : ℕ) : X.K) ^ (((a / 2 : ℕ) : ℤ) * relOrd P N₁' N₂' - ((b / 2 : ℕ) : ℤ) * relOrd P N₁ N₂)

end Scalar

end GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw
