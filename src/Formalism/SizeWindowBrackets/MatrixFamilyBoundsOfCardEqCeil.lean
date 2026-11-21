import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv

open Matrix Module NumberField
open scoped ComplexOrder

namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

noncomputable section

def IsUni {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) : Prop :=
  Vᴴ * V = 1 ∧ V * Vᴴ = 1

def Btwist {ι : Type} {D D' : ℕ} {d : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ) :
    ∀ u, Matrix (Fin D') (Fin (d u)) ℂ :=
  fun u => c u • (V * B u * U u)

def gaTw {ι : Type} (ga : ι → ℝ) (c : ι → ℂ) : ι → ℝ :=
  fun u => ga u / ‖c u‖ ^ 2

def phase {ι : Type} (c : ι → ℂ) (u u' : ι) : ℂ :=
  (starRingEnd ℂ (c u) * c u') / ((‖c u‖ * ‖c u'‖ : ℝ) : ℂ)

def Gram {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Y⁻¹)ᴴ * Y⁻¹

def OrthFrame {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    Prop :=
  Jᴴ * J = 1 ∧ J1ᴴ * J1 = 1 ∧ J * Jᴴ + J1 * J1ᴴ = 1

def Wfr {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    Matrix (Fin (D + D1)) (Fin Dall) ℂ :=
  (Matrix.fromRows Jᴴ J1ᴴ).submatrix finSumFinEquiv.symm id

def Brow {ι : Type} {D D' : ℕ} {d : ι → ℕ} (W : Matrix (Fin D') (Fin D) ℂ)
    (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) : ∀ u, Matrix (Fin D') (Fin (d u)) ℂ :=
  fun u => W * B u

def UniDim : Prop :=
  ∀ (m n : ℕ) (V : Matrix (Fin m) (Fin n) ℂ), IsUni V → m = n

def HsUni : Prop :=
  ∀ (a b a' b' : ℕ) (M : Matrix (Fin a) (Fin b) ℂ) (S : Matrix (Fin a') (Fin a) ℂ)
    (T : Matrix (Fin b) (Fin b') ℂ), Sᴴ * S = 1 → T * Tᴴ = 1 → hsSq (S * M * T) = hsSq M

def TwHS : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    (∀ u u', hsSq (Kp (Btwist B c V U) (gaTw ga c) u u') = hsSq (Kp B ga u u')) ∧
    (∀ u, hsSq (Kd (Btwist B c V U) (gaTw ga c) u - 1) = hsSq (Kd B ga u - 1))

def TwQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    Qm (Btwist B c V U) (gaTw ga c) = V * Qm B ga * Vᴴ ∧
    (Qm (Btwist B c V U) (gaTw ga c)).trace = (Qm B ga).trace ∧
    (Qm (Btwist B c V U) (gaTw ga c) * Qm (Btwist B c V U) (gaTw ga c)).trace
      = (Qm B ga * Qm B ga).trace

def TwInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (D D' : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin D') (Fin D) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) →
    (∀ u, 0 < gaTw ga c u ↔ 0 < ga u) ∧
    (∀ η, F1 (Btwist B c V U) (gaTw ga c) η ↔ F1 B ga η) ∧
    (∀ e, F2 (Btwist B c V U) (gaTw ga c) e ↔ F2 B ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Btwist B c V U) (gaTw ga c) Dstar η0 η1 e0 ↔
      InputS B ga Dstar η0 η1 e0)

def RowsCount : Prop :=
  ∀ (Dall D : ℕ) (del : ℝ), del < 1 →
    ((1 - del) * (Dall : ℝ) ≤ (D : ℝ) ↔ (Dall : ℝ) ≤ (D : ℝ) / (1 - del))

def FrameFacts : Prop :=
  ∀ (Dall D D1 : ℕ) (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ),
    OrthFrame J J1 →
    Jᴴ * J1 = 0 ∧ J1ᴴ * J = 0 ∧ Dall = D + D1 ∧
    (J * Jᴴ)ᴴ = J * Jᴴ ∧ (J * Jᴴ) * (J * Jᴴ) = J * Jᴴ ∧ (J * Jᴴ) * (J1 * J1ᴴ) = 0 ∧
    IsUni (Wfr J J1) ∧
    Wfr J J1 * (J * Jᴴ) * (Wfr J J1)ᴴ =
      (Matrix.fromBlocks (1 : Matrix (Fin D) (Fin D) ℂ) 0 0 (0 : Matrix (Fin D1) (Fin D1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm

def RowsBlock : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ),
    OrthFrame J J1 →
    (∀ u k j, Brow (Wfr J J1) B u (Fin.castAdd D1 k) j = (Jᴴ * B u) k j) ∧
    (∀ u k j, Brow (Wfr J J1) B u (Fin.natAdd D k) j = (J1ᴴ * B u) k j) ∧
    (∀ η, F1 (Brow (Wfr J J1) B) ga η ↔ F1 B ga η) ∧
    (∀ e, F2 (Brow (Wfr J J1) B) ga e ↔ F2 B ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Brow (Wfr J J1) B) ga Dstar η0 η1 e0 ↔ InputS B ga Dstar η0 η1 e0)

def CorTransport : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d : ι → ℕ) (P : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ) (η e del : ℝ),
    (∀ u, 0 < ga u) → (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) → OrthFrame J J1 →
    del < 1 → (1 - del) * (Dall : ℝ) ≤ (D : ℝ) →
    (∀ u, Y'⁻¹ * A u * Y u = c u • (Jᴴ * (V * P u * U u))) →
    F1 P ga η → F2 P ga e →
    (∀ u, 0 < gaTw ga c u) ∧
    (∀ u k j, Brow (Wfr J J1) (Btwist P c V U) u (Fin.castAdd D1 k) j = (Y'⁻¹ * A u * Y u) k j) ∧
    F1 (Brow (Wfr J J1) (Btwist P c V U)) (gaTw ga c) η ∧
    F2 (Brow (Wfr J J1) (Btwist P c V U)) (gaTw ga c) e ∧
    (1 - del) * ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) ∧ ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) / (1 - del)

def WordCount : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (C0 Gam sg Dstar : ℝ),
    0 < C0 → 0 < Gam → 0 < sg → 0 ≤ Dstar →
    Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ →
    (∀ u, Dstar / Gam ^ 2 / C0 ≤ (d u : ℝ)) →
    Dstar / sg ≤ Rs d

def WordLogReal : Prop :=
  ∀ (k X : ℝ), 0 ≤ X → X + 1 ≤ (2 : ℝ) ^ (k - 3) →
    Real.log (⌈X⌉₊ : ℝ) ≤ (k - 3) * Real.log 2

def MatrixFamilyBoundsOfCardEqCeil : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar sg η0 η1 e0 C0 Gam : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → 0 < C0 → 0 < Gam →
    Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ → (∀ u, Dstar / Gam ^ 2 / C0 ≤ (d u : ℝ)) →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputS B ga Dstar η0 η1 e0 →
    F1 B ga (5 * sg) ∧ F2 B ga e0 ∧ e0 ≤ 1 / 4

def ChainHyp {ι : Type} [Fintype ι] {Dall D D1 : ℕ} {d r : ι → ℕ}
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ) : Prop :=
  (∀ u, 0 < ga u) ∧ 0 < Dstar ∧ 0 < sg ∧ sg ≤ 1 / 20 ∧ 0 < C0 ∧ 0 < Gam ∧
  Fintype.card ι = ⌈C0 * Gam ^ 2 / sg⌉₊ ∧ (∀ u, Dstar / Gam ^ 2 / C0 ≤ (d u : ℝ)) ∧
  -1 ≤ η0 ∧ η0 ≤ sg / 2 ∧ η1 ≤ sg / 2 ∧ 0 ≤ e0 ∧ Real.sqrt e0 ≤ sg / 2 ∧
  InputS Pf ga Dstar η0 η1 e0 ∧
  Isom Vr ∧ 0 ≤ de ∧ de ≤ 1 / 4 ∧ ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d ∧
  (∀ u, c u ≠ 0) ∧ IsUni V ∧ (∀ u, IsUni (U u)) ∧ OrthFrame J J1 ∧
  del < 1 ∧ (1 - del) * (Dall : ℝ) ≤ (D : ℝ) ∧
  IsUnit Y'.det ∧ (∀ u, IsUnit (Y u).det) ∧
  (∀ u, Y'⁻¹ * A u * Y u = c u • (Jᴴ * (V * Bram Pf Vr u * U u)))

def CorChain : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ),
    ChainHyp Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam →
    (∀ u, 0 < gaTw ga c u) ∧
    (∀ u k j, Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U) u (Fin.castAdd D1 k) j
      = (Y'⁻¹ * A u * Y u) k j) ∧
    F1 (Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U)) (gaTw ga c) (5 * sg + 3 * Real.sqrt de) ∧
    F2 (Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U)) (gaTw ga c) (2 * e0) ∧ 2 * e0 ≤ 1 / 4 ∧
    (1 - del) * ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) ∧ ((D + D1 : ℕ) : ℝ) ≤ (D : ℝ) / (1 - del) ∧
    0 < Rs r ∧ 0 ≤ 5 * sg + 3 * Real.sqrt de ∧ 0 ≤ 2 * e0 ∧ 0 < Dall ∧ 0 ≤ del

def WfrS {Dall D D1 : ℕ} (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    Matrix (Fin D ⊕ Fin D1) (Fin Dall) ℂ :=
  Matrix.fromRows Jᴴ J1ᴴ

def BfS {ι : Type} {Dall D D1 : ℕ} {d : ι → ℕ} (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ)
    (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) :
    ∀ u, Matrix (Fin D ⊕ Fin D1) (Fin (d u)) ℂ :=
  fun u => c u • (WfrS J J1 * (V * Pf u))

def VrS {ι : Type} {d r : ι → ℕ} (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ :=
  fun u => Vr u * U u

def TwRamFactor : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D' : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (W : Matrix (Fin D') (Fin Dall) ℂ),
    (∀ u, c u ≠ 0) → IsUni V → (∀ u, IsUni (U u)) → IsUni W → Isom Vr →
    (∀ u, Brow W (Btwist (Bram Pf Vr) c V U) u
      = Brow W (Btwist Pf c V (fun _ => 1)) u * VrS Vr U u) ∧
    Isom (VrS Vr U) ∧
    (∀ Dstar η0 η1 e0, InputS (Brow W (Btwist Pf c V (fun _ => 1))) (gaTw ga c) Dstar η0 η1 e0 ↔
      InputS Pf ga Dstar η0 η1 e0)

def ChainCondition : Prop :=
  ∀ (ι : Type) [Fintype ι] (Dall D D1 : ℕ) (d r : ι → ℕ)
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (Vr : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (U : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (A : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ) (Y' : Matrix (Fin D) (Fin D) ℂ)
    (Y : ∀ u, Matrix (Fin (r u)) (Fin (r u)) ℂ) (Dstar sg η0 η1 e0 de del C0 Gam : ℝ),
    ChainHyp Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam →
    (∀ u, 0 < gaTw ga c u) ∧
    (∀ u, (VrS Vr U u)ᴴ * VrS Vr U u = 1) ∧
    Dstar / sg ≤ MatrixLatticeEstimates.RsG (fun u => Fin (d u)) ∧
    ∑ u, ((Fintype.card (Fin (d u)) : ℝ) - (Fintype.card (Fin (r u)) : ℝ))
      ≤ de * MatrixLatticeEstimates.RsG (fun u => Fin (d u)) ∧
    MatrixLatticeEstimates.InputSG (BfS Pf c V J J1) (gaTw ga c) Dstar η0 η1 e0 ∧
    (∀ u k j, (BfS Pf c V J J1 u * VrS Vr U u) (Sum.inl k) j = (Y'⁻¹ * A u * Y u) k j) ∧
    (∀ u i j, (BfS Pf c V J J1 u * VrS Vr U u) i j
      = Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U) u (finSumFinEquiv i) j) ∧
    0 < ∑ u, Fintype.card (Fin (r u)) ∧ 0 ≤ del ∧ del < 1 ∧
    (1 - del) * (Fintype.card (Fin D ⊕ Fin D1) : ℝ) ≤ (Fintype.card (Fin D) : ℝ)

end

end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
