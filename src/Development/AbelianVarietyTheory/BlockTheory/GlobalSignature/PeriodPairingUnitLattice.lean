import Mathlib
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataKerP

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodPairingUnitLattice

open Formalism.BasicNotions NumberField

section Generic

variable {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (emb : LL →+* ℂ) (Pl : Rows.Places LL)
  (Λ Λ' : HLat LL) (per : Λ.V → Λ'.V → ℂ)

def Rational : Prop := ∀ x z, ∃ y : LL, emb y = per x z

def IntegralUpTo (n : ℕ) : Prop :=
  ∀ (w : Pl.Pl), ∀ x ∈ locW Pl w Λ.L, ∀ z ∈ locW Pl w Λ'.L, ∀ y : LL, emb y = per x z →
    (n : LL) * y ∈ intW Pl w

def CauchySchwarz : Prop :=
  ∀ (v : InfinitePlace LL) x z, ∀ y : LL, emb y = per x z →
    v y ≤ Formalism.HermitianLatticesTheory.normAt Λ.b Λ.X v x * Formalism.HermitianLatticesTheory.normAt Λ'.b Λ'.X v z

theorem IntegralUpTo.of_dvd {n n' : ℕ} (h : IntegralUpTo emb Pl Λ Λ' per n) (hn : n ∣ n') :
    IntegralUpTo emb Pl Λ Λ' per n' := by
  obtain ⟨k, rfl⟩ := hn
  intro w x hx z hz y hy
  have h1 := (intW Pl w).mul_mem (natCast_mem (intW Pl w) k) (h w x hx z hz y hy)
  have e : ((n * k : ℕ) : LL) * y = (k : LL) * ((n : LL) * y) := by push_cast; ring
  rwa [e]

def unitLat (LL : Type) [Field LL] [NumberField LL] [StarRing LL] : HLat LL where
  V := LL
  ι := Unit
  b := Module.Basis.singleton Unit LL
  X := fun _ => 1
  L := LinearMap.range (Algebra.linearMap (𝓞 LL) LL)

example : Rational emb (unitLat LL) (unitLat LL) (fun x z : LL => emb (x * z)) ∧
    CauchySchwarz emb (unitLat LL) (unitLat LL) (fun x z : LL => emb (x * z)) := by
  refine ⟨fun x z => ⟨_, rfl⟩, fun v (x : LL) (z : LL) y hy => ?_⟩
  have hy' : y = x * z := emb.injective hy
  have key : ∀ a : LL, Formalism.HermitianLatticesTheory.normAt (unitLat LL).b (unitLat LL).X v a = v a := by
    intro a
    show Real.sqrt (∑ i : Unit, ‖Matrix.mulVec (1 : Matrix Unit Unit ℂ)⁻¹
      (Formalism.HermitianLatticesTheory.vecAt (Module.Basis.singleton Unit LL) v a) i‖ ^ 2) = v a
    rw [inv_one, Matrix.one_mulVec]
    simp [Formalism.HermitianLatticesTheory.vecAt, InfinitePlace.norm_embedding_eq]
  rw [hy', key, key, map_mul]

end Generic

variable (D : D7)

theorem card_stabilizer_dvd₂ (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (c : (Tw.fm u μ).clsP) :
    Nat.card ((Tw.fm u μ).stabilizer₂ c) ∣ (D.chTw u μ).DGam :=
  (Subgroup.card_dvd_of_injective _ ((Tw.fm u μ).stabMap_inj c)).trans
    ((D.chTw u μ).dvd_DGam _ le_rfl _)

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodPairingUnitLattice
