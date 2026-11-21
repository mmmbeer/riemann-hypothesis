import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

section
noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix Formalism.L2.S.S7.WittLeviSubgroups

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n)

def cols (Fm : Matrix (Fin n) (Fin n) R) (r : ι) : Fin n → R := fun i => Fm i (e r)

variable {e}

theorem coord_zero {Fm Fi : Matrix (Fin n) (Fin n) R} (hF : Fi * Fm = 1) (S : Set ι) {u : Fin n → R}
    (hu : u ∈ Submodule.span R (cols e Fm '' S)) (s : ι) (hs : s ∉ S) : (Fi *ᵥ u) (e s) = 0 := by
  have hle : Submodule.span R (cols e Fm '' S) ≤
      LinearMap.ker ((LinearMap.proj (e s)).comp (Matrix.toLin' Fi)) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    have hrs : e r ≠ e s := fun h' => hs (e.injective h' ▸ hr)
    have h1 : (Fi *ᵥ cols e Fm r) (e s) = (Fi * Fm) (e s) (e r) := by
      simp only [Matrix.mulVec, dotProduct, cols, Matrix.mul_apply]
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.proj_apply, h1,
      hF, Matrix.one_apply_ne (Ne.symm hrs)]
  have := hle hu
  rwa [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.proj_apply] at this

theorem entry_zero {Fm Fi : Matrix (Fin n) (Fin n) R} (hF : Fi * Fm = 1) (S : Set ι) {g : GL (Fin n) R}
    (hg : g ∈ Formalism.UG.stabGL (Submodule.span R (cols e Fm '' S))) (s r : ι) (hr : r ∈ S) (hs : s ∉ S) :
    (Fi * (g : Matrix (Fin n) (Fin n) R) * Fm) (e s) (e r) = 0 := by
  have hu : (g : Matrix (Fin n) (Fin n) R) *ᵥ cols e Fm r ∈ Submodule.span R (cols e Fm '' S) :=
    (hg _).1 (Submodule.subset_span ⟨r, hr, rfl⟩)
  have h1 := coord_zero hF S hu s hs
  rw [Matrix.mulVec_mulVec] at h1
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, cols, Matrix.mul_apply]

variable (lev : ι → ℕ)

def BLo (T : Matrix ι ι R) : Prop := ∀ s r, lev r < lev s → T s r = 0

def bd (T : Matrix ι ι R) : Matrix ι ι R := fun s r => if lev s = lev r then T s r else 0

theorem bd_mul {T Ti : Matrix ι ι R} (hT : BLo lev T) (hTi : BLo lev Ti) (h : T * Ti = 1) :
    bd lev T * bd lev Ti = 1 := by
  ext s r
  rw [Matrix.mul_apply]
  by_cases hl : lev s = lev r
  · rw [← h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [bd]
    by_cases h1 : lev s = lev t
    · rw [if_pos h1, if_pos (show lev t = lev r by omega)]
    · rw [if_neg h1, zero_mul]
      rcases Nat.lt_or_ge (lev t) (lev s) with h2 | h2
      · rw [hT s t h2, zero_mul]
      · rw [hTi t r (by omega), mul_zero]
  · have hsr : s ≠ r := fun h' => hl (by rw [h'])
    rw [Matrix.one_apply_ne hsr]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [bd]
    by_cases h1 : lev s = lev t
    · rw [if_neg (show ¬ lev t = lev r by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

end Gen

section Form

variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (lev : ι → ℕ) (a : ℕ)

def AntiLev (W : Matrix ι ι R) : Prop := ∀ q r, W q r ≠ 0 → lev q + lev r = 2 * a

end Form

end PI.IwaMeasEx.PD

end
end

section
noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Witt

variable {J n₀ : ℕ} (c : Composition J)

theorem antiLev_wittJ {R : Type} [CommRing R] [StarRing R] (J0 : Matrix (Fin n₀) (Fin n₀) R) :
    AntiLev (levW (n₀ := n₀) c) c.length (wittJ (J := J) J0) := by
  intro q r h
  have hs : ∀ s : Fin J, (c.index s : ℕ) < c.length := fun s => (c.index s).isLt
  rcases q with q | q | q <;> rcases r with r | r | r <;>
    simp [wittJ, levW, Matrix.one_apply] at h ⊢
  all_goals first
    | (obtain ⟨rfl, -⟩ := h; have := hs q; omega)
    | omega

end Witt

section Frame

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J)

abbrev eW : WIdx J (nz I J) ≃ Fin I.n := widx I Fr.hJ

abbrev Bm : Matrix (Fin I.n) (Fin I.n) I.E := (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E)

abbrev Bi : Matrix (Fin I.n) (Fin I.n) I.E := ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

theorem Bm_Bi : Bm Fr * Bi Fr = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem Bi_Bm : Bi Fr * Bm Fr = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

def wcE (h : Matrix (Fin I.n) (Fin I.n) I.E) : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E :=
  (Bi Fr * h * Bm Fr).submatrix (eW Fr) (eW Fr)

def unwc (A : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) : Matrix (Fin I.n) (Fin I.n) I.E :=
  Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr

theorem unwc_mul (A B : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) :
    unwc Fr A * unwc Fr B = unwc Fr (A * B) := by
  unfold unwc
  rw [← submatrix_mul_equiv A B (eW Fr).symm (eW Fr).symm (eW Fr).symm]
  calc Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr * (Bm Fr * B.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr)
      = Bm Fr * A.submatrix (eW Fr).symm (eW Fr).symm * (Bi Fr * Bm Fr) * B.submatrix (eW Fr).symm (eW Fr).symm * Bi Fr := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Bi_Bm, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unwc_one : unwc Fr 1 = 1 := by
  unfold unwc
  rw [submatrix_one_equiv, Matrix.mul_one, Bm_Bi]

theorem cT_eq (M : Matrix (Fin I.n) (Fin I.n) I.E) : Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := by
  ext i j; rfl

abbrev Gm : Matrix (Fin I.n) (Fin I.n) I.E := (Bm Fr)ᴴ * I.J * Bm Fr

theorem Gm_sub : (Gm Fr).submatrix (eW Fr) (eW Fr) = wittJ (J := J) Fr.J0 := by
  ext r s
  have := Fr.gram r s
  rw [cT_eq] at this
  exact this

end Frame

section Flag

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

end Flag

end PI.IwaMeasEx.PD

end
end

section
noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {ι : Type} [Fintype ι] [DecidableEq ι]
  (lev : ι → ℕ) {T : Matrix ι ι R}

end Maps

section Pt

variable {I : AutInst}

theorem sigR_inclE (x : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) x) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star x) := by
  show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (x ⊗ₜ[I.F] (1 : Af I.F)) = star x ⊗ₜ[I.F] (1 : Af I.F)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem cT_map (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (M.map (Formalism.UG.inclE (F := I.F) (Af I.F))) =
      Mᴴ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  ext i j
  simp only [Formalism.UG.cT, transpose_apply, map_apply, conjTranspose_apply]
  exact sigR_inclE (M j i)

theorem semiconj_phi (v : InfinitePlace I.F) : Function.Semiconj (I.φ v) star star := fun a => by
  rw [I.cm.cmUnram.2.1 (I.φ v) a]
  rfl

end Pt

section Dec

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

end Dec

end PI.IwaMeasEx.PD

namespace PI.IwaMeasEx.Sk

open Formalism.L2.S.S7.DensDefs PI.IwaMeasEx.PD

end PI.IwaMeasEx.Sk

end
end
