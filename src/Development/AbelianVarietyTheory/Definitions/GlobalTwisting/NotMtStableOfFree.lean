import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers

noncomputable section

namespace GlobalTheory.EX.DQ.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField


theorem ok_setDiv (D : D7) (N) (h) (I : TwIn D) (i) : TwIn.Ok (D := setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i ↔ I.Ok i := Iff.rfl
set_option maxHeartbeats 2000000 in
theorem one_setDiv (D : D7) (N) (h) (I : TwIn D) (i b Q k ψ) : TwGoodOne (setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i b Q k ψ ↔ TwGoodOne D I i b Q k ψ := Iff.rfl

section Lat

variable {O L V : Type} [CommRing O] [Field L] [NumberField L] [AddCommGroup V] [Module ℂ V] {φ : O →+* ℂ}

theorem mem_carrier_iff (M : Rows.OLat O φ V) (x : V) :
    x ∈ M.carrier ↔ x ∈ AddSubgroup.closure {y | ∃ c : O, ∃ v ∈ M.gen, y = φ c • v} := by
  classical
  constructor
  · rintro ⟨c, rfl⟩
    exact sum_mem fun v hv => AddSubgroup.subset_closure ⟨c v, v, hv, rfl⟩
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, v, hv, rfl⟩ := hy
      refine ⟨Pi.single v c, ?_⟩
      rw [Finset.sum_eq_single v (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => absurd hv h)]
      simp
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨c + d, by simp [add_smul, Finset.sum_add_distrib]⟩
    | neg a _ ha =>
      obtain ⟨c, rfl⟩ := ha
      exact ⟨-c, by simp⟩

open Classical in

def sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : Rows.OLat O φ V where
  gen := (Finset.univ ×ˢ M.gen).image fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2
  span_top := by
    rw [eq_top_iff, ← M.span_top, Submodule.span_le]
    intro v hv
    obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) := (RingOfIntegers.basis L).index_nonempty
    have h0 : σ (RingOfIntegers.basis L i : L) ≠ 0 := by
      rw [map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
      exact (RingOfIntegers.basis L).ne_zero i
    have := Submodule.smul_mem (Submodule.span ℂ (((Finset.univ ×ˢ M.gen).image
      fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2 : Finset V) : Set V)) (σ (RingOfIntegers.basis L i : L))⁻¹
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩)))
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

theorem smul_mem_sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) (a : 𝓞 L) (c : O) {v : V} (hv : v ∈ M.gen) :
    (φ c * σ (a : L)) • v ∈ (sat σ M).carrier := by
  classical
  rw [mem_carrier_iff]
  have e : (φ c * σ (a : L)) • v = ∑ i, φ (((RingOfIntegers.basis L).repr a i : ℤ) * c) •
      σ (RingOfIntegers.basis L i : L) • v := by
    conv_lhs => rw [← (RingOfIntegers.basis L).sum_repr a]
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  rw [e]
  exact sum_mem fun i _ => AddSubgroup.subset_closure
    ⟨_, _, Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩, rfl⟩


theorem sat_stable (σ : L →+* ℂ) (M : Rows.OLat O φ V) (a : 𝓞 L) : ∀ y ∈ (sat σ M).carrier,
    σ (a : L) • y ∈ (sat σ M).carrier := by
  classical
  intro y hy
  rw [mem_carrier_iff] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, w, hw, rfl⟩ := hy
    obtain ⟨⟨i, v⟩, hv, rfl⟩ := Finset.mem_image.1 hw
    have := smul_mem_sat σ M (a * RingOfIntegers.basis L i) c (Finset.mem_product.1 hv).2
    convert this using 1
    simp [smul_smul, mul_left_comm]
  | zero => rw [mem_carrier_iff]; simp
  | add x y _ _ hx hy => rw [mem_carrier_iff] at *; rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mem_carrier_iff] at *; rw [smul_neg]; exact neg_mem hx


end Lat

set_option maxHeartbeats 4000000 in

def setMt (D : D7) (M : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (D.what₂.Amb μ)) : D7 :=
  { D with
    what₂ := { D.what₂ with Mtilde := M }
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

def satRec (D : D7) : D7 := setMt D fun μ => sat D.what₂.embLL (D.what₂.Mtilde μ)






set_option maxHeartbeats 2000000 in
theorem good_setDiv (D : D7) (O : Obj D) (N) (h) (N0 S) :
    GoodAllAt (setDiv D N h) (O.tr N h).nch ⟨twEOf (O.tr N h).xd, N0, S⟩ ↔ GoodAllAt D O.nch ⟨twEOf O.xd, N0, S⟩ :=
  forall_congr' fun w => forall_congr' fun _ => and_congr (ok_setDiv D N h ⟨twEOf O.xd, N0, S⟩ (O.nch.twI w))
    (forall_congr' fun a => forall_congr' fun _ =>
      one_setDiv D N h ⟨twEOf O.xd, N0, S⟩ (O.nch.twI w) (O.nch.sd w) (O.nch.Q w) (O.nch.k' w) (O.nch.psi' w ^ a))

end GlobalTheory.EX.DQ.Model

end
