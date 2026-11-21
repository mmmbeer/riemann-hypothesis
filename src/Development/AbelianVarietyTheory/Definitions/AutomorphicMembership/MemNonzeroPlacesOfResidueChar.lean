import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepColWPinned

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem fk_zero (t : RowsT K w Z Wt p0) (v : B.places.Pl) (hv : v ∉ Wt) (j : Fin B.R.m) :
    FK K.s (w.D Z) (j.1 + 1) (B.places.resChar v) = 0 := by
  by_contra h
  apply hv
  rw [t.exact]
  refine ⟨j, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (j.1 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  exact h


section Idx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}



end Idx

theorem fTypeG_ne {D : D7} (h : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FTypeG D j ≠ 0 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact GaloisStage.f_pos D.R
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hf
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  let i : Fin (D.R.sigW j).1 := ⟨D.R.k + j - 1 - 1, by rw [hs]; omega⟩
  have e := (h j h1 h2 τ).1 i
  have l := DV.aPlusQ_last D j h1 h2 τ
  have p : (1 : ℤ) ≤ D.what₂.kaBig j τ i := by
    have : (1 : ℚ) ≤ (D.what₂.kaBig j τ i : ℚ) := e ▸ l
    exact_mod_cast this
  have q : 0 < fockDeg D j := by
    unfold fockDeg
    refine Finset.sum_pos' (fun t _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) ⟨τ, Finset.mem_univ _, ?_⟩
    refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact abs_pos.2 (by omega)
  unfold FTypeG
  have : (0 : ℝ) < (fockDeg D j : ℝ) := by exact_mod_cast q
  linarith

theorem type_mem (t : RowsT K w Z Wt p0) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : v ∈ Wt := by
  by_contra h
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  have z := fk_zero t v h ⟨0, hm⟩
  unfold FK at z
  rw [if_pos ⟨i, hv⟩] at z
  exact fTypeG_ne t.r.Y.kap 1 le_rfl hm z


def trivialDecorations : Slots := ⟨fun _ _ _ _ _ _ _ _ _ => PUnit, fun _ _ _ _ _ _ _ _ _ _ _ _ => PUnit, fun _ _ _ _ _ _ _ _ _ _ => PUnit,
  fun _ _ _ _ _ _ _ _ _ => PUnit⟩






def expTw (B : Base) (pl : Finset ℕ) (n : ℕ) (hc : ∀ v, B.places.resChar (B.places.conj v) = B.places.resChar v) : TwDat B :=
  { TwDat.untw B pl with
    k := fun v => if B.places.resChar v ∈ pl then n else 0
    psi_ord := fun _ => one_pow _
    off := fun v h => ⟨rfl, if_neg h⟩
    conj := fun v => ⟨rfl, by simp only [hc]⟩ }




end GlobalTheory.Mem.Top.Bl.Model3

end
