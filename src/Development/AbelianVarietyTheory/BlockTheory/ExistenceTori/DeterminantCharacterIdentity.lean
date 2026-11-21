import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight MvPolynomial
open scoped nonZeroDivisors Classical

section Minors

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (R : Type) [CommRing R]

def ColsDisjoint (col : ∀ σ : T, Fin (r σ) → Fin n) : Prop :=
  Function.Injective fun x : (Σ σ : T, Fin (r σ)) => col x.1 x.2

def leadMinor (col : ∀ σ : T, Fin (r σ) → Fin n) (σ : T) (i : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  Matrix.det (Matrix.of fun s t : Fin (i.val + 1) =>
    (X ⟨σ, Fin.castLE (Nat.succ_le_of_lt i.isLt) s, col σ (Fin.castLE (Nat.succ_le_of_lt i.isLt) t)⟩ :
      MvPolynomial (Letter T r n) R))

def gap (a : T × ℕ → ℕ) (σ : T) (i : Fin (r σ)) : ℕ :=
  a (σ, i.val) - if i.val + 1 < r σ then a (σ, i.val + 1) else 0

def minorProd (col : ∀ σ : T, Fin (r σ) → Fin n) (a : T × ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ : T, ∏ i : Fin (r σ), leadMinor r n R col σ i ^ gap r a σ i

example (col : ∀ σ : T, Fin (r σ) → Fin n) : minorProd r n R col 0 = 1 := by
  simp [minorProd, gap]

end Minors

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def ratMat (γ : ratPts E n) : Matrix (Fin n) (Fin n) E := fun a b => Classical.choose (γ.2.1 a b)

def conjMat (g : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  fun a b => IsCMField.complexConj E (g a b)

def moveLat (g : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) : GenLat E n where
  La := Λ.La.map ((Matrix.mulVecLin g).restrictScalars (𝓞 E))

def InPlainLat (h : UA E n) (x : Fin n → E) : Prop :=
  ∃ u : Fin n → AdE E, (∀ b, u b ∈ intAd E) ∧ ∀ a, diagE E (x a) = ∑ b, h.1 a b * u b

variable (E n) in

def LatOfClass : Prop :=
  (∀ h : UA E n, (latOf h).Unimod) ∧
  (∀ (h : UA E n) (x : Fin n → E), x ∈ (latOf h).La ↔ InPlainLat h fun a => IsCMField.complexConj E (x a)) ∧
  ∀ (h : UA E n) (γ : ratPts E n), ∀ k ∈ maxCpt E n,
    (latOf (γ.1 * h * k)).La = (moveLat (conjMat (ratMat γ)) (latOf h)).La

def conjId (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

def overId (v : Plc E) : Ideal (𝓞 E) := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))

def PrimeTo (S : Finset (Plc E)) (𝔞 : Ideal (𝓞 E)) : Prop := 𝔞 ≠ ⊥ ∧ ∀ v ∈ S, 𝔞 ⊔ overId v = ⊤

end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def HidaSetting (Dw : Datum H) (n : ℕ) : Prop := IsGalois ℚ E ∧ Even n ∧ Odd (Dw.p + Dw.q)

def push {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB c ℓ.1 ℓ.2.1 (fun k => g k ℓ.2.2)

example {n : ℕ} (g : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (j : Fin n) :
    push c g (X (⟨σ, i, j⟩ : LtN Dw n)) = ∑ k, C (embF c σ (g k j)) * X (⟨σ, i, k⟩ : LtN Dw n) := by
  simp [push, letB]

def pushRat {n : ℕ} (γ : ratPts E n) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  push c (conjMat (ratMat γ))

def psiSet (H : Host E) : Finset (E →+* ℂ) := Finset.univ.filter (InPsi H)

def idK (τ : E →+* ℂ) (𝔞 : Ideal (𝓞 E)) : FractionalIdeal (𝓞 c.F)⁰ c.F :=
  ((𝔞.map (RingOfIntegers.mapRingHom (embF c τ)) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F)

def infType (nt : (E →+* ℂ) → ℤ) (z : 𝓞 E) : c.F :=
  ∏ τ ∈ psiSet H, embK c τ z ^ nt τ * embK c τ (H.bar z) ^ (1 - nt τ)

def IsHecke (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) : Prop :=
  B ⊤ = 1 ∧ (∀ 𝔞 𝔟, PrimeTo S 𝔞 → PrimeTo S 𝔟 → B (𝔞 * 𝔟) = B 𝔞 * B 𝔟) ∧
  (∀ 𝔞, PrimeTo S 𝔞 → ∀ s : c.F →+* ℂ, ‖s (B 𝔞)‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ)) ∧
  (∀ 𝔞, PrimeTo S 𝔞 → FractionalIdeal.spanSingleton (𝓞 c.F)⁰ (B 𝔞) =
    ∏ τ ∈ psiSet H, idK c τ 𝔞 ^ nt τ * idK c τ (conjId H 𝔞) ^ (1 - nt τ)) ∧
  (∃ m : ℕ, ∀ z : 𝓞 E, PrimeTo S (Ideal.span {z}) → z - 1 ∈ (∏ v ∈ S, overId v) ^ m →
    B (Ideal.span {z}) = infType c nt z) ∧
  ∀ v : Plc E, v ∉ S →
    B (overId v) = (if (overId v).IsPrime then -1 else 1) * (Ideal.absNorm v.asIdeal : c.F)

def Unram (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) : Prop :=
  ∀ z : 𝓞 E, PrimeTo S (Ideal.span {z}) → B (Ideal.span {z}) = infType c nt z

def detChar (d : (E →+* ℂ) → ℤ) {n : ℕ} (γ : ratPts E n) : c.F :=
  ∏ τ ∈ psiSet H, embF c τ (ratMat γ).det ^ d τ

section Coeff

variable {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T] [IsScalarTower (𝓞 c.F) c.F T]

def LatLaw (ρ : Representation c.F (ratPts E n) T) (L : UA E n → Submodule (𝓞 c.F) T) : Prop :=
  (∀ h, (L h).FG ∧ Submodule.span c.F (L h : Set T) = ⊤) ∧
  ∀ (h : UA E n) (γ : ratPts E n), ∀ k ∈ maxCpt E n, (L (γ.1 * h * k) : Set T) = ρ γ '' (L h : Set T)

def IsForm (J : Subgroup (UA E n)) (ty : J →* c.Fˣ) (ρ : Representation c.F (ratPts E n) T) (f : UA E n → T) : Prop :=
  ∀ (h : UA E n) (γ : ratPts E n) (k : J), f (γ.1 * h * k.1) = ((ty k : c.Fˣ) : c.F) • ρ γ (f h)

end Coeff

def MovesDatum {n : ℕ} (J : Subgroup (UA E n)) (ψ : J →* c.Fˣ) (ph : (Fin n → ConjQ Dw l) → c.F) : Prop :=
  ∀ (k : J) (κ : Fin n → Fin n → 𝓞 E),
    (∀ a b, ∃ u ∈ intAd E, star (k.1.1 a b) - diagE E (κ a b : E) = (l.M : AdE E) * u) →
      ∀ x, ph (fun a => ∑ b, κ a b • x b) = ((ψ k : c.Fˣ) : c.F) * ph x

example {n : ℕ} (J : Subgroup (UA E n)) (ph : (Fin n → ConjQ Dw l) → c.F) :
    MovesDatum c J 1 ph ↔ FixesDatum c J ph := by
  simp [MovesDatum, FixesDatum]

def RamPart (S : Finset (Plc E)) (B : Ideal (𝓞 E) → c.F) (nt : (E →+* ℂ) → ℤ) {n : ℕ} (γ : ratPts E n) (w : c.F) :
    Prop :=
  ∃ z : 𝓞 E, PrimeTo S (Ideal.span {z}) ∧ (ratMat γ).det * (H.bar z : E) = (z : E) ∧
    w * infType c nt z = B (Ideal.span {z})

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity
