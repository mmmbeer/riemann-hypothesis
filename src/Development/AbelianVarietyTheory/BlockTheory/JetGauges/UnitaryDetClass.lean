import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IsUnitary (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map (IsCMField.complexConj E)).transpose * γ = 1

def Carries (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) : Prop :=
  ∀ v' : Fin n → E, v' ∈ Λ'.La ↔ ∃ v ∈ Λ.La, γ.mulVec v = v'

def CongrAt (Q : ℕ) (u v : Fin n → E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k Q ∧ ∀ j, ∃ s : 𝓞 E, (k : E) * (u j - v j) = (Q : E) * (s : E)

abbrev StdMod (E : Type) [Field E] [NumberField E] (n Q : ℕ) : Type :=
  Fin n → 𝓞 E ⧸ Ideal.span {(Q : 𝓞 E)}

def IsMarking (Q : ℕ) (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n Q) : Prop :=
  Function.Surjective κ ∧
  (∀ v : Λ.La, κ v = 0 ↔ ∃ u : Λ.La, v = Q • u) ∧
  ∀ (v w : Λ.La) (x y : Fin n → 𝓞 E),
    (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) → (∀ j, κ w j = Ideal.Quotient.mk _ (y j)) →
      ∃ s : 𝓞 E, ∑ j, IsCMField.complexConj E ((v : Fin n → E) j) * (w : Fin n → E) j -
        ∑ j, IsCMField.complexConj E (x j : E) * (y j : E) = (Q : E) * (s : E)

def IsRepOf (bad Q : ℕ) (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n Q) (Λ' : GenLat E n) : Prop :=
  Λ'.TrivAt bad ∧ Λ'.TrivAt Q ∧
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUnitary γ ∧ Carries γ Λ Λ' ∧
    ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) →
      CongrAt Q (γ.mulVec v) fun j => (x j : E)

def IsTrivRep (bad Q : ℕ) (Λ : GenLat E n) : Prop := Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt Q

def SameClass (bad Q : ℕ) (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) : Prop :=
  IsTrivRep bad Q Λ ∧ IsTrivRep bad Q Λ' ∧ IsUnitary γ ∧ Carries γ Λ Λ' ∧
    ∀ v ∈ Λ.La, CongrAt Q (γ.mulVec v) v

example : IsUnitary (1 : Matrix (Fin n) (Fin n) E) := by
  simp [IsUnitary, Matrix.map_one]

example (Λ : GenLat E n) : Carries 1 Λ Λ := fun v => by simp

example (Q : ℕ) (v : Fin n → E) : CongrAt Q v v := ⟨1, by simp, fun _ => ⟨0, by simp⟩⟩

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def push {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ : LtN Dw n => letB c ℓ.1 ℓ.2.1 fun k => γ k ℓ.2.2

example {n : ℕ} (ℓ : LtN Dw n) : push c (1 : Matrix (Fin n) (Fin n) E) (X ℓ) = X ℓ := by
  obtain ⟨σ, i, j⟩ := ℓ
  simp [push, letB, Matrix.one_apply, apply_ite, ite_mul]

def PushOnto (Dw : Datum H) (n : ℕ) : Prop :=
  ∀ (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) (a : (E →+* ℂ) × ℕ → ℕ),
    IsUnitary γ → Carries γ Λ Λ' → push (Dw := Dw) c γ '' harmL c Λ a = harmL c Λ' a

def IsBeta (Dw : Datum H) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

def ThEq (nab : NabV Xo c) {n : ℕ} (ζ : c.F) (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (β : c.F)
    (Λ' : GenLat E n) (β' : c.F) : Prop :=
  ∀ (w : (Fin n → LevQ Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (N N' : ℕ),
    P ∈ harmL c Λ a → Λ.LevOK N l.M → Λ'.LevOK N' l.M →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ v : k,
      (∀ x : k, ShortValAt Xo c nab w Λ β N P y x ↔ x = v) ∧
      ∀ x : k, ShortValAt Xo c nab w Λ' β' N' (push c γ P) y x ↔ x = algebraMap c.F k ζ * v

open Classical in

def detChar {n : ℕ} (d : (E →+* ℂ) → ℤ) (γ : Matrix (Fin n) (Fin n) E) : c.F :=
  ∏ τ ∈ Finset.univ.filter (InPsi H), embF c τ γ.det ^ d τ

open Classical in

def ScalarLaw (Dw : Datum H) {n : ℕ} (bad Q : ℕ) (u : GenLat E n → c.F) (e : (E →+* ℂ) → ℤ) : Prop :=
  u ⟨stdLat E n⟩ = betaH (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) ∧
  ∀ Λ : GenLat E n, IsTrivRep bad Q Λ →
    (∀ σ : c.F →+* ℂ, ‖σ (u Λ)‖ = 1) ∧
    Submodule.span (𝓞 c.F) {u Λ} * ∏ τ ∈ Finset.univ.filter (InPsi H), idealAt c Λ.La τ ^ (-e τ).toNat =
      ∏ τ ∈ Finset.univ.filter (InPsi H), idealAt c Λ.La τ ^ (e τ).toNat

def RootOfUnityChange (nab : NabV Xo c) (n bad : ℕ) : Prop :=
  ∀ (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) (β β' : c.F), SameClass bad l.M γ Λ Λ' →
    IsBeta c Dw Λ β → IsBeta c Dw Λ' β' →
      ∃ ζ : c.F, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ThEq Xo c nab ζ γ Λ β Λ' β'

def HidaSetting (Dw : Datum H) (n bad : ℕ) : Prop :=
  IsGalois ℚ E ∧ Even n ∧ Odd (Dw.p + Dw.q) ∧ KPsiIn (Dw := Dw) c ∧ 0 < bad ∧
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * discr E → p ∣ bad

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
