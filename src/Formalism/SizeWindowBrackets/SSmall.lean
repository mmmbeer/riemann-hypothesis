import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
import Formalism.SizeWindowBrackets.GaloisToProductIsIso

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LSmall

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def NodeWindows {m : ℕ} (TT T2 : Finset H) (b η w'' off : ℝ) (bt : H → ℝ) (w : H → Fin m → E0 × H → ℝ) : Prop :=
  (∀ u0 j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + (η + 1)) ∧
  (∀ u0 j t, t ∈ TT → bt t + off ≤ w u0 j (topPl t) ∧ w u0 j (topPl t) ≤ bt t + off + η) ∧
  (∀ u0 j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → (∀ t ∈ TT, ρ ≠ topPl t) → w'' ≤ w u0 j ρ ∧ w u0 j ρ ≤ w'' + η)

def WindowSizes (TT : Finset H) (x b b' η κ w'' off : ℝ) (bt : H → ℝ) : Prop :=
  0 < b ∧ 0 < b' ∧ 0 ≤ η ∧ 0 ≤ κ ∧ 0 < x ∧ 0 ≤ off ∧ off ≤ b' / x ∧ 0 < w'' ∧ w'' ≤ b' / x ∧
  (∀ t ∈ TT, b' ≤ bt t ∧ bt t ≤ b' + κ * b') ∧ κ * b' + b' / x + η ≤ b'

def NodeSizesOfWindows : Prop :=
  ∀ {m : ℕ} (TT T2 : Finset H) (x b b' η κ w'' off : ℝ) (bt : H → ℝ) (w : H → Fin m → E0 × H → ℝ),
    WindowSizes TT x b b' η κ w'' off bt → NodeWindows TT T2 b η w'' off bt w → NodeSizes T2 b b' η w

def WindowSizesText : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (TT : Finset H) (x b b' η κ off : ℝ) (bt : H → ℝ),
    3 ≤ x → 0 < b → 0 < b' → 0 ≤ η → η ≤ b' / 4 → 0 ≤ κ → κ ≤ 1 / 4 →
    (off = b' / x ∨ off = (⌊b' / x⌋ : ℝ)) → (∀ t ∈ TT, b' ≤ bt t ∧ bt t ≤ b' + κ * b') →
    WindowSizes TT x b b' η κ (b' / (x * (Fintype.card H : ℝ))) off bt

def NodeSizesText : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) (TT T2 : Finset H) (x b b' η κ off : ℝ) (bt : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ),
    3 ≤ x → 0 < b → 0 < b' → 0 ≤ η → η ≤ b' / 4 → 0 ≤ κ → κ ≤ 1 / 4 →
    (off = b' / x ∨ off = (⌊b' / x⌋ : ℝ)) → (∀ t ∈ TT, b' ≤ bt t ∧ bt t ≤ b' + κ * b') →
    NodeWindows TT T2 b η (b' / (x * (Fintype.card H : ℝ))) off bt w → NodeSizes T2 b b' η w

end

section Conj

open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

def cj {m n : Type} (M : Matrix m n ℂ) : Matrix m n ℂ := M.map (starRingEnd ℂ)

def Bconj {ι : Type} {D : ℕ} {d : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) :
    ∀ u, Matrix (Fin D) (Fin (d u)) ℂ := fun u => cj (B u)

def ConjInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ),
    (∀ η, F1 (Bconj B) ga η ↔ F1 B ga η) ∧
    (∀ e, F2 (Bconj B) ga e ↔ F2 B ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Bconj B) ga Dstar η0 η1 e0 ↔ InputS B ga Dstar η0 η1 e0)

end Conj

section Host

open Formalism.LFunctionChainParameters.LHost

def hOf (e m : ℕ) : HA e :=
  if h : m.Coprime (2 ^ (e + 2)) then Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime m h)) else 0

def decomp {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (p : ℕ) : AddSubgroup (E0 × H) :=
  D.inertia p ⊔ AddSubgroup.zmultiples (D.frob p)

def Sloc {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (g : E0 × H) (n : ℕ) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * primVal D ψ n

def gI (e d i : ℕ) : E0 × HA e := (if Odd i then (1, 1) else (1, 0), i • hOf e d)

def omV (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) (m : ℕ) : ℂ := by
  classical
  exact if ∀ t : HA e, ψ ((0, 0), t) = 1 then 1 else if Odd m then ψ ((0, 0), hOf e m) else 0

def laV (s : ℂ) (l m : ℕ) : ℂ := by
  classical
  exact if s = 1 then 1 else ((jacobiSym (m : ℤ) l : ℤ) : ℂ)

def ProductFormula : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (ψ : AddChar (E0 × HA e) ℂ) (m : ℕ), m ≠ 0 →
    primVal (hostData e q d) ψ m = omV e ψ m * laV (ψ sg) q m * laV (ψ sgc0) d m

end Host

end Formalism.LFunctionChainParameters.LSmall
