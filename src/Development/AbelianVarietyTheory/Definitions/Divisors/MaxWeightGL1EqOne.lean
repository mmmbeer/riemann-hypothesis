import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

section Generic

variable {G : Type} [Group G]

def locPart (T K : Subgroup G) (x : G) : Subgroup G := T ⊓ K.map (MulAut.conj x).toMonoidHom

def volRat (U V : Subgroup G) : ℝ := (V.relIndex U : ℝ) / (U.relIndex V : ℝ)

def maxWt (T K : Subgroup G) (x : G) : ℝ := ⨆ h : G, volRat (locPart T K h) (locPart T K x)

def orbSum (θ : G →* G) (K : Subgroup G) (δ : G) (w : G → ℝ) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    (w (Quotient.out q) : ℂ) * GlobalTheory.BCT.avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def twOrbM (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (maxWt (GlobalTheory.BCT.twCent θ δ) K) f

def twOrbU (θ : G →* G) (K : Subgroup G) (δ : G) (U : Subgroup G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (fun x => volRat U (locPart (GlobalTheory.BCT.twCent θ δ) K x)) f


end Generic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def frobR (r : ℕ) : Kn p K r →+* Kn p K r where
  toFun x := ⟨frobK p K (x : PadicAlgCl p), Kn_stable p K r (frobK p K) x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def intR (r : ℕ) : Subring (Kn p K r) := (Obar p).toSubring.comap (algebraMap (Kn p K r) (PadicAlgCl p))

def intK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

def sig (n r : ℕ) : GL (Fin n) (Kn p K r) →* GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.map (frobR p K r)

def Kint (n r : ℕ) : Subgroup (GL (Fin n) (Kn p K r)) :=
  (GeneralLinearGroup.map (intR p K r).subtype).range

def KintK (n : ℕ) : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.map (intK p K).subtype).range

def nrm (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) : GL (Fin n) (Kn p K r) :=
  (List.map (fun i => (⇑(sig p K n r))^[i] δ) (List.range r)).prod

def TO (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (φ : GL (Fin n) (Kn p K r) → ℂ) : ℂ :=
  twOrbM (sig p K n r) (Kint p K n r) δ φ

def Orb (n : ℕ) (γ : GL (Fin n) K) (f : GL (Fin n) K → ℂ) : ℂ :=
  twOrbM (MonoidHom.id _) (KintK p K n) γ f

def KotInv (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (m : ℤ) : Prop :=
  ‖((GeneralLinearGroup.det δ : (Kn p K r)ˣ) : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ m

def unif : Kˣ :=
  if h : ∃ π : Kˣ, vK p K π = 1 then h.choose
  else Units.mk0 (p : K) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

def unifR (r : ℕ) : (Kn p K r)ˣ :=
  Units.map (IntermediateField.inclusion (show K ≤ Kn p K r from le_sup_left)).toRingHom.toMonoidHom (unif p K)

end GlobalTheory.LKLoc
