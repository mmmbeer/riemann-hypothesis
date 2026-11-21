import Formalism.CoboundaryTransfers.StatementAPI
import Formalism.WachModuleLifts.StatementW
import Formalism.LagrangeIdealLifts.Statement
import Formalism.FrobeniusContraction.Statement

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

section CL

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

def baseOfCL (B : CL.W.Base p A) : Base ℤ_[p] A where
  p := p
  hp := Fact.out
  φ := B.φA
  γ := B.γA
  X := B.π₀
  Q := B.q
  comm := B.comm
  φX := by
    obtain ⟨v, hv⟩ := B.hφ
    exact ⟨B.q ^ (p - 1) * v, by rw [hv]; ring⟩

variable {B : CL.W.Base p A} {η : ℕ}

def ofCL {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : CL.W.WachMod B η D) : WachMod (baseOfCL B) η D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.π₀_inj
  Q_bij := W.q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_QN := W.γ_qN

variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']

def homOfCL {W : CL.W.WachMod B η D} {W' : CL.W.WachMod B η D'} (F : CL.W.Hom W W') :
    Hom (ofCL W) (ofCL W') where
  f := F.f
  φ_comm := F.φ_comm
  γ_comm := F.γ_comm
  N_le := F.N_le

def sesOfCL {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    {W₀ : CL.W.WachMod B η D₀} {W₁ : CL.W.WachMod B η D₁} {W₂ : CL.W.WachMod B η D₂}
    (S : CL.W.SES W₀ W₁ W₂) : SES (ofCL W₀) (ofCL W₁) (ofCL W₂) where
  ι := homOfCL S.ι
  π := homOfCL S.π
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat

end CL

section CLback

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

def toCL (B : Base ℤ_[p] A) (hp : B.p = p) (hq : B.QLin) (hφ : B.PhiX (p - 1)) :
    CL.W.Base p A where
  φA := B.φ
  γA := B.γ
  π₀ := B.X
  q := B.Q
  hq := by rw [hq, hp]; simp
  hφ := hφ
  comm := B.comm

def WachMod.toCL {B : Base ℤ_[p] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] (W : WachMod B M D) (hp : B.p = p)
    (hq : B.QLin) (hφ : B.PhiX (p - 1)) : CL.W.WachMod (toCL B hp hq hφ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  π₀_inj := W.X_inj
  q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_qN := W.γ_QN

end CLback

section LIFT

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]

def baseOfLIFT (B : LIFT.Base ℓ A) : Base ℤ_[ℓ] A where
  p := ℓ
  hp := Fact.out
  φ := B.φA
  γ := B.γA
  X := B.X
  Q := B.Q
  comm := B.comm
  φX := ⟨B.Q, B.φX⟩

variable {B : LIFT.Base ℓ A} {M : ℕ}

def ofLIFT {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : LIFT.WD B M D)
    (hγ : ∀ y : D, B.Q ^ M • y ∈ W.N → ∃ y' : D, B.Q ^ M • y' ∈ W.N ∧ W.γ y - y = B.X • y') :
    WachMod (baseOfLIFT B) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_QN := hγ

def toLIFT (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q)
    (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) : LIFT.Base ℓ A where
  φA := B.φ
  γA := B.γ
  X := B.X
  Q := B.Q
  u := u
  comm := B.comm
  φX := hφ
  γX := hγX
  γQ := by
    obtain ⟨v, hv, ⟨t, rfl⟩, hγ⟩ := hγQ
    exact ⟨t, hv, by rw [hγ, mul_comm]⟩

def WachMod.toLIFT {B : Base ℤ_[ℓ] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : WachMod B M D) (u : ℤ_[ℓ]ˣ)
    (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.WD (toLIFT B u hφ hγX hγQ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N

end LIFT

def baseOfArchimedeanComponents {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : WachCohomologyFacts.Base O A) :
    Base O A where
  p := B.ℓ
  hp := B.hℓ
  φ := B.φ
  γ := B.γ
  X := B.X
  Q := B.q
  comm := B.comm
  φX := ⟨B.u * (B.X + (B.ℓ : A)) ^ (B.ℓ - 1), by rw [B.hφX]; ring⟩

def LIFTGammaQN : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : LIFT.Base ℓ A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : LIFT.WD B M D),
    ∀ y : D, B.Q ^ M • y ∈ W.N → ∃ y' : D, B.Q ^ M • y' ∈ W.N ∧ W.γ y - y = B.X • y'

end Formalism.CoboundaryTransfers
