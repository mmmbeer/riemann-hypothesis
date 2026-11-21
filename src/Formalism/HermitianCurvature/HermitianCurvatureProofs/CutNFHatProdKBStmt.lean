import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def OmKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ∧
    ∀ a : Fin P.r, Formalism.QuantumDeterminants.Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def FFKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :=
  Q.FFl P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' 0 (OmKB p)

def IsGaugeQQKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    CutMP.Gauge.FamR P p.T.base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e
          (Q.QL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (fun ρ' => MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e Φ ρ')) ρ

end kb

def NFHatProdKBS : Prop :=
  ∃ C₁ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → IsGaugeQQKB p e → MA.IsModelLevel P (MA.DQ P) L → ∀ (N : ℕ) (u : List (MA.A P (MA.DQ P))),
      u.length ≤ N → (∀ a ∈ u, a ∈ MA.hatSet P L) →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
        (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ k, NFOpOK C₁ p N (Th k)) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          B.JF p.T.base F ∈ FFKB p →
          MA.actA P u.prod (trJKB p e (B.JF p.T.base F)) =
            ∑ k, MA.actA P (b k) (trJKB p e (B.JF p.T.base (B.opApply (Th k) F)))

end

end Formalism.FourierDecayAlt.P.CutBP
