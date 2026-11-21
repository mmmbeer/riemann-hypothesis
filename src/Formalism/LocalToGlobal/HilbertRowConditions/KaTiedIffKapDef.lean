import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalRingCardinality.DataKap

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.BasicNotions Formalism.L2.Host

structure OTied (D : D7) (T : HostTied D) (C : CharFrame D) where

  pieces : KsPieces D T

  inj : Function.Injective D.what₂.OtoLL

  range : ∀ x : Qb, (∃ y : D.what₂.O, T.jLL (D.what₂.OtoLL y) = x) ↔ x ∈ OsQ (KsQ D T C pieces)

namespace OTied

variable {D : D7} {T : HostTied D} {C : CharFrame D} (X : OTied D T C)

def toQb (D : D7) (T : HostTied D) : D.what₂.O →+* Qb := T.jLL.comp D.what₂.OtoLL

theorem toQb_injective (X : OTied D T C) : Function.Injective (toQb D T) :=
  (RingHom.injective T.jLL).comp X.inj

def eO : D.what₂.O ≃+* (toQb D T).range :=
  RingEquiv.ofBijective (toQb D T).rangeRestrict ⟨fun _ _ h => X.toQb_injective (congrArg Subtype.val h),
    (toQb D T).rangeRestrict_surjective⟩

theorem mem_range_iff (x : Qb) : x ∈ (toQb D T).range ↔ x ∈ OsQ (KsQ D T C X.pieces) := by
  rw [RingHom.mem_range]
  exact X.range x

theorem range_eq : ((toQb D T).range : Set Qb) = OsQ (KsQ D T C X.pieces) :=
  Set.ext fun x => X.mem_range_iff x


end OTied

structure KappaCompatible (D : D7) : Prop where

  big : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1),
    ((D.what₂.kaBig j τ i : ℤ) : ℚ) = aPlus D j τ i

  small : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (c : Fin (D.R.sigW j).2),
    ((D.what₂.kaSmall j τ c : ℤ) : ℚ) = kaSmallOf D j τ c

theorem getQ_int {n : ℕ} (f : Fin n → ℚ) (hf : ∀ i, ∃ z : ℤ, f i = z) (i : ℕ) : ∃ z : ℤ, getQ f i = z := by
  unfold getQ
  split_ifs with h
  · exact hf _
  · exact ⟨0, by simp⟩

theorem vPar_eq_sigPar (D : D7) (τ : D.what₂.Tau) (i : ℕ) : vPar D τ i = DV.sigPar D τ i := by
  unfold vPar DV.sigPar getQ
  split_ifs <;> first | rfl | simp

theorem getQ_e_eq (D : D7) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (τ : D.what₂.Tau) :
    getQ (D.hc τ).e (j - 1) = DV.eQ D j τ := by
  unfold getQ DV.eQ
  split_ifs <;> first | rfl | (exfalso; omega)

theorem aPlus_eq (D : D7) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (τ : D.what₂.Tau) (i : ℕ) :
    aPlus D j τ i = DV.aPlusQ D j τ i := by
  have n2 : (D.R.sigW j).1 + 1 = D.R.k + j := by
    show D.R.k + j - 1 + 1 = D.R.k + j
    omega
  have n3 : (D.R.sigW j).2 + j = D.R.m := by
    show D.R.m - j + j = D.R.m
    omega
  have q2 : (((D.R.sigW j).1 : ℕ) : ℚ) + 1 = D.R.k + j := by exact_mod_cast n2
  have q3 : (((D.R.sigW j).2 : ℕ) : ℚ) + j = D.R.m := by exact_mod_cast n3
  unfold aPlus DV.aPlusQ
  rw [vPar_eq_sigPar, getQ_e_eq D j hj hjm τ]
  linear_combination (-1/2 : ℚ) * q2 + (1/2 : ℚ) * q3



structure GTied (D : D7) {G Pl0 T : Type} [Group G] [Fintype G] {m : ℕ}
    (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T m) where

  eG : G ≃* G0g D.nd

  e0 : ∀ g : G, D.what₂.embLL ((Formalism.L2.DIV.idemOf A.X).coeff g) = D.ntypes.e0.coeff (eG g)

def ZetaCompatible (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (c : ℂ),
    (∀ (φ : D.what₂.Mu u) (F : D.what₂.Amb μ), F ∈ D.what₂.V0 μ →
      D.what₂.perCol u μ φ F = c * D.what₂.Bu u φ (D.what₂.iota μ ((D.what₂.Qsp μ).starProjection F))) →
    (∃ (φ : D.what₂.Mu u) (F : D.what₂.Amb μ), F ∈ D.what₂.V0 μ ∧ D.what₂.perCol u μ φ F ≠ 0) →
    D.what₂.zeC u μ = c

structure RowsCompatible (D : D7) (T : HostTied D) (C : CharFrame D) {nch : NChoice D} (Tp : TupTied D C nch) where

  O : OTied D T C

  ka : DV.KapDef D

  ze : ZetaCompatible D

end Formalism.L2.Rows
