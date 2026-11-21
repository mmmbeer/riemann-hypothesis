import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SysC
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ConditionIffAdditiveMaps
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DelEquiv
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc

section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

abbrev pendG (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Pend X :=
  pendC X E hfin hst (beLT hLT) (thFOf X pos F)

section Ties

variable (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

end Ties

end Formalism.L2.G.Pend
end
end

section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

section Local

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem ordP_mul [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W))
    {x y : Qq} (hx : x ≠ 0) (hy : y ≠ 0) : ordP W p (x * y) = ordP W p x + ordP W p y := by
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hy
  have hu : algebraMap W Qq (u : W) ≠ 0 := (u.isUnit.map (algebraMap W Qq)).ne_zero
  rw [← mul_assoc, ordP_mul_zpow hp (mul_ne_zero hx hu), ordP_mul_unit hp hx, ordP_eq hp]

theorem colSpan_mul {k : ℕ} (A g : Matrix (Fin k) (Fin k) Qq) :
    (colSpan W g).map ((Matrix.mulVecLin A).restrictScalars W) = colSpan W (A * g) := by
  unfold colSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨c, rfl⟩, ?_⟩
    ext i
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]

theorem gl_det_ne {k : ℕ} (A : GL (Fin k) Qq) : (A : Matrix (Fin k) (Fin k) Qq).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero

theorem lenLat_map [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] {p : ℕ} (hp : Irreducible (p : W))
    {k : ℕ} (A : GL (Fin k) Qq) {L : Submodule W (Fin k → Qq)} (hL : IsLattice W L) :
    lenLat W p (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)) =
      lenLat W p L - ordP W p (A : Matrix (Fin k) (Fin k) Qq).det := by
  obtain ⟨g, hg, rfl⟩ := hL
  have hA : IsUnit (A : Matrix (Fin k) (Fin k) Qq).det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  rw [colSpan_mul, lenLat_colSpan hp _ (by rw [Matrix.det_mul]; exact hA.mul hg), lenLat_colSpan hp g hg,
    Matrix.det_mul, ordP_mul hp hA.ne_zero hg.ne_zero]
  ring

end Local

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem gamAt_ord (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (v : X.Pl) :
    ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det =
      ordP ((X.Pj j).W (X.vJ j v)) p ((X.Lv.lev j c).act (X.vJ j v) γ :
        Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq (X.vJ j v))).det := by
  cases j <;> rfl

theorem gamAt_mul (j : ℕ) (c : X.Lv.comp j) (γ γ' : (X.Lv.lev j c).Γ) :
    gamAt X j c (γ * γ') = fun v => gamAt X j c γ v * gamAt X j c γ' v := by
  funext v
  cases j <;> exact map_mul _ _ _

theorem len_smul (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup) (hL : (X.Pj j).IsLatTup L)
    (v : X.Pl) :
    len X v j ((X.Lv.lev j c).smul γ L) = len X v j L -
      ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det := by
  rw [gamAt_ord]
  have hS := (X.Pj j).setting (X.vJ j v)
  have := hS.frac_alt
  exact lenLat_map hS.p_unif _ (hL _)

section Kap

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

theorem cA_mul (j : ℕ) (B B' : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    cA X Kc j (fun v => B v * B' v) = cA X Kc j B * cA X Kc j B' := by
  unfold cA
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Units.val_mul, Matrix.det_mul, map_mul, mul_zpow]

theorem cA_ne_zero (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : cA X Kc j B ≠ 0 := by
  unfold cA
  refine Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun s _ => zpow_ne_zero _ ?_
  exact (map_ne_zero _).2 (gl_det_ne (B v))

def pP (K : Type) [Field K] (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : K :=
  ∏ v : X.Pl, (p : K) ^ (-(X.vm v (j + 1) *
    ordP (X.G.P.W v) p (B v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))

theorem pPart_mul {K : Type} [Field K] (hp0 : (p : K) ≠ 0) (j : ℕ)
    (B B' : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    pP X K j (fun v => B v * B' v) = pP X K j B * pP X K j B' := by
  unfold pP
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hS := X.G.P.setting v
  have := hS.frac_alt
  rw [Units.val_mul, Matrix.det_mul, ordP_mul hS.p_unif (gl_det_ne (B v)) (gl_det_ne (B' v)), ← zpow_add₀ hp0]
  congr 1
  ring

theorem pPart_ne_zero {K : Type} [Field K] (hp0 : (p : K) ≠ 0) (j : ℕ)
    (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : pP X K j B ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ hp0

theorem pPart_map (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    algebraMap X.G.Kf Kc (pP X X.G.Kf j B) = pP X Kc j B := by
  unfold pP
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, map_natCast]

def chiC (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : Kc :=
  algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O))

theorem kapG_eq (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) :
    kapG X Kc j c γ = chiC X Kc j c γ * cA X Kc j (gamAt X j c γ) * pP X Kc j (gamAt X j c γ) := rfl

theorem chiC_mul (j : ℕ) (c : X.Lv.comp j) (γ γ' : (X.Lv.lev j c).Γ) :
    chiC X Kc j c (γ * γ') = chiC X Kc j c γ * chiC X Kc j c γ' := by
  unfold chiC
  rw [map_mul, Units.val_mul, map_mul, map_mul]

theorem chiC_ne_zero (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : chiC X Kc j c γ ≠ 0 :=
  ((((X.Lv.lev j c).χ γ).isUnit.map (algebraMap X.G.O X.G.Kf)).map (algebraMap X.G.Kf Kc)).ne_zero

variable (hp0 : (p : Kc) ≠ 0)

include hp0

theorem kapG_mul (j : ℕ) (c : X.Lv.comp j) (γ γ' : (X.Lv.lev j c).Γ) :
    kapG X Kc j c (γ * γ') = kapG X Kc j c γ * kapG X Kc j c γ' := by
  rw [kapG_eq, kapG_eq, kapG_eq, gamAt_mul, cA_mul, pPart_mul X hp0, chiC_mul]
  ring

theorem kapG_ne_zero (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : kapG X Kc j c γ ≠ 0 := by
  rw [kapG_eq]
  exact mul_ne_zero (mul_ne_zero (chiC_ne_zero X Kc j c γ) (cA_ne_zero X Kc j _)) (pPart_ne_zero X hp0 j _)

theorem kapG_one (j : ℕ) (c : X.Lv.comp j) : kapG X Kc j c 1 = 1 := by
  have h := kapG_mul X Kc hp0 j c 1 1
  rw [mul_one] at h
  exact (mul_eq_left₀ (kapG_ne_zero X Kc hp0 j c 1)).1 h.symm

omit hp0

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

theorem delt_spec (j : ℕ) (c : X.Lv.comp j) (L : (X.Pj j).Tup) (h : (X.Pj j).IsLatTup L) :
    ∃ L0 : (X.Pj j).Tup, (c, L0) ∈ repOf X.Lv hfin j ∧ L = (X.Lv.lev j c).smul (delt X hfin j c L) L0 := by
  classical
  unfold delt
  rw [dif_pos h]
  exact ⟨_, (Classical.choose_spec (repOf_ex X.Lv hfin j c L h).exists).1,
    (Classical.choose_spec (repOf_ex X.Lv hfin j c L h).exists).2.choose_spec⟩


include hp0


theorem chiN_smul (hK : KapStab X Kc) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    chiN X Kc hfin j (c, (X.Lv.lev j c).smul γ L) = (kapG X Kc j c γ)⁻¹ * chiN X Kc hfin j (c, L) := by
  have hL' : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul γ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ L).2 hL
  obtain ⟨L0, h0, e0⟩ := delt_spec X hfin j c L hL
  obtain ⟨L1, h1, e1⟩ := delt_spec X hfin j c _ hL'
  set δ := delt X hfin j c L with hδ
  set δ' := delt X hfin j c ((X.Lv.lev j c).smul γ L) with hδ'
  have e2 : (X.Lv.lev j c).smul γ L = (X.Lv.lev j c).smul (γ * δ) L0 := by
    rw [lsmul_mul, ← e0]
  have h10 : L1 = L0 := (repOf_ex X.Lv hfin j c _ hL').unique ⟨h1, δ', e1⟩ ⟨h0, γ * δ, e2⟩
  subst h10
  have hst : (X.Lv.lev j c).smul ((γ * δ)⁻¹ * δ') L1 = L1 := by
    rw [lsmul_mul, ← e1, e2, lsmul_inv_lsmul]
  have hk := hK j c L1 ((γ * δ)⁻¹ * δ') (repOf_lat X.Lv hfin j (c, L1) h0) hst
  have hd : δ' = (γ * δ) * ((γ * δ)⁻¹ * δ') := by group
  show (kapG X Kc j c δ')⁻¹ = (kapG X Kc j c γ)⁻¹ * (kapG X Kc j c δ)⁻¹
  rw [hd, kapG_mul X Kc hp0, hk, mul_one, kapG_mul X Kc hp0, mul_inv]

end Kap

section Ker

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

theorem derAt_C_mul (j : ℕ) (n : X.ZA j →₀ ℕ) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) :
    derAt X Kc j n (MvPowerSeries.C a * f) = a * derAt X Kc j n f := by
  unfold derAt
  split_ifs
  · rw [MvPowerSeries.coeff_C_mul]
    ring
  · rw [mul_zero]

theorem delF_C_mul (j : ℕ) (G : (X.Pj j).Xsp) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) :
    delF X Kc j G (MvPowerSeries.C a * f) = a • delF X Kc j G f := by
  rw [delF_apply, delF_apply]
  unfold pairD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [derAt_C_mul, mul_smul]

def eSX (j : ℕ) (La : X.Lt j) : X.G.Kf := ∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)

theorem eSX_smul (hpK : (p : X.G.Kf) ≠ 0) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    eSX X j (c, (X.Lv.lev j c).smul γ L) = eSX X j (c, L) * pP X X.G.Kf j (gamAt X j c γ) := by
  unfold eSX pP
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [len_smul X j c γ L hL v, ← zpow_add₀ hpK]
  congr 1
  ring

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
  (Th0 : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc)

def DelEquivOn (Gd : ∀ j, (X.Pj j).Xsp → Prop) : Prop :=
  ∀ (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) (G : (X.Pj j).Xsp)
    (f : MvPowerSeries (X.ZA j) Kc), Gd j G →
    delF X Kc j ((X.Pj j).natAct A G) (SA X Kc j (glAt X j A) f) = cA X Kc j (glAt X j A) • delF X Kc j G f

def VtIn (Gd : ∀ j, (X.Pj j).Xsp → Prop) : Prop := ∀ j, ∀ G ∈ (X.Pj j).Vtup, Gd j G

theorem ker_smul (hp0 : (p : Kc) ≠ 0) {Gd : ∀ j, (X.Pj j).Xsp → Prop} (hD : DelEquivOn X Kc Gd) (hG : GeoLaw X Kc Th0) (hK : KapStab X Kc) (j : ℕ)
    (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ) (G : (X.Pj j).Xsp)
    (hL : (X.Pj j).IsLatTup L) (hGood : Gd j G) (t : X.G.Kf) :
    (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
        delF X Kc j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
          (thFN X Kc hfin Th0 j (c, (X.Lv.lev j c).smul γ L) La') =
      (eSX X j (c, L) * t) • delF X Kc j G (thFN X Kc hfin Th0 j (c, L) La') := by
  have hpK : (p : X.G.Kf) ≠ 0 := fun h => hp0 (by rw [← map_natCast (algebraMap X.G.Kf Kc), h, map_zero])
  have e1 : ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G) =
      (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) •
        (X.Pj j).natAct (fun v => (X.Lv.lev j c).act v γ) G := (algebraMap_smul X.G.Kf _ _).symm
  have e2 := hD j (fun v => (X.Lv.lev j c).act v γ) G (Th0 j (c, L) La') hGood
  have e3 : SA X Kc j (glAt X j fun v => (X.Lv.lev j c).act v γ) (Th0 j (c, L) La') =
      Th0 j (c, (X.Lv.lev j c).smul γ L) La' := (hG j c L La' γ hL).symm
  rw [e3] at e2
  unfold thFN
  rw [delF_C_mul, delF_C_mul, e1, map_smul, LinearMap.smul_apply, e2, chiN_smul X Kc hp0 hfin hK j c γ L hL,
    eSX_smul X hpK j c γ L hL]
  rw [← algebraMap_smul Kc (eSX X j (c, L) * pP X X.G.Kf j (gamAt X j c γ) * t),
    ← algebraMap_smul Kc (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)),
    ← algebraMap_smul Kc (eSX X j (c, L) * t), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  have hk := kapG_ne_zero X Kc hp0 j c γ
  have hk' := kapG_eq X Kc j c γ
  rw [map_mul, map_mul, map_mul, pPart_map]
  show _ * ((kapG X Kc j c γ)⁻¹ * _) * chiC X Kc j c γ * cA X Kc j (gamAt X j c γ) = _
  field_simp
  rw [hk']
  ring

end Ker

section Geo

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

theorem hasSubst_actS (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    MvPowerSeries.HasSubst (actS X Kc j B) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, a, b)⟩ => by simp [actS]

theorem subst_actS (j : ℕ) (B B' : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (z : X.ZA j) :
    MvPowerSeries.subst (actS X Kc j B) (actS X Kc j B' z) = actS X Kc j (fun v => B v * B' v) z := by
  obtain ⟨v, s, a, b⟩ := z
  simp only [actS]
  rw [subst_lin (hasSubst_actS X Kc j B)]
  simp only [MvPowerSeries.subst_X (hasSubst_actS X Kc j B), actS]
  by_cases hs : IsOddPos s
  · simp only [if_pos hs]
    rw [sum_lin (MvPowerSeries.C) (mAt X Kc j v s ((B' v)⁻¹ : GL _ _)) (mAt X Kc j v s ((B v)⁻¹ : GL _ _))
      (fun a' => (MvPowerSeries.X ⟨v, (s, a', b)⟩ : MvPowerSeries (X.ZA j) Kc)) a, mAt_mul, ← Units.val_mul, ← mul_inv_rev]
  · simp only [if_neg hs]
    have h := sum_lin (MvPowerSeries.C) (mAt X Kc j v s (B' v)).transpose (mAt X Kc j v s (B v)).transpose
      (fun a' => (MvPowerSeries.X ⟨v, (s, a', b)⟩ : MvPowerSeries (X.ZA j) Kc)) a
    simp only [Matrix.transpose_apply] at h
    rw [h, ← Matrix.transpose_mul, mAt_mul, ← Units.val_mul]
    rfl

theorem SA_mul (j : ℕ) (B B' : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (f : MvPowerSeries (X.ZA j) Kc) :
    SA X Kc j B (SA X Kc j B' f) = SA X Kc j (fun v => B v * B' v) f := by
  unfold SA
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_actS X Kc j B') (hasSubst_actS X Kc j B)]
  simp only [subst_actS]

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
  (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc)

def thGeo (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : MvPowerSeries (X.ZA j) Kc :=
  SA X Kc j (gamAt X j La.1 (delt X hfin j La.1 La.2))
    (ThR j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')

def StabGeo : Prop :=
  ∀ j (c : X.Lv.comp j) (L0 : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ), (c, L0) ∈ repOf X.Lv hfin j →
    (X.Lv.lev j c).smul ε L0 = L0 → SA X Kc j (gamAt X j c ε) (ThR j (c, L0) La') = ThR j (c, L0) La'



theorem gamAt_one (j : ℕ) (c : X.Lv.comp j) : gamAt X j c 1 = fun _ => 1 := by
  funext v
  cases j <;> exact map_one _

theorem actS_one (j : ℕ) (z : X.ZA j) : actS X Kc j (fun _ => 1) z = MvPowerSeries.X z := by
  obtain ⟨v, s, a, b⟩ := z
  simp only [actS, inv_one, Units.val_one, mAt_one, Matrix.one_apply]
  by_cases hs : IsOddPos s
  · simp only [if_pos hs, apply_ite MvPowerSeries.C, map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  · simp only [if_neg hs, apply_ite MvPowerSeries.C, map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]

theorem SA_one (j : ℕ) (f : MvPowerSeries (X.ZA j) Kc) : SA X Kc j (fun _ => 1) f = f := by
  unfold SA
  have : actS X Kc j (fun _ => 1) = MvPowerSeries.X := funext (actS_one X Kc j)
  rw [this]
  exact congrFun MvPowerSeries.subst_self f


end Geo

section Rec

theorem pC_ne_zero : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

def RationalInvarianceOnValues {X : Sys p} (Y : Pend X) (Gd : ∀ j, (X.Pj j).Xsp → Prop) : Prop :=
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ)
    (G : (X.Pj j).Xsp), Gd j G → (X.Pj j).IsLatTup L → (X.Pj (j + 1)).IsLatTup La'.2 →
      Y.ker j (c, (X.Lv.lev j c).smul γ L) La' ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G) =
        Y.ker j (c, L) La' G

variable [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (Th0 : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p])

abbrev pendN : Pend X :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  pendC X E hfin hst be (thFN X ℂ_[p] hfin Th0)




abbrev pendR (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Pend X :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  pendN X E hfin hst be (thGeo X ℂ_[p] hfin ThR)




theorem sig_pow_int (v : X.Pl) (s : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ s) (algebraMap (X.G.P.W v) (X.G.P.Qq v) x) = algebraMap (X.G.P.W v) (X.G.P.Qq v) y := by
  induction s generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ s ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ, RingAut.mul_apply, hy, hz]

theorem norm_tw_int (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.G.P.W v) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    ‖tw X ℂ_[p] v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := sig_pow_int X v s.val x
  show ‖E.iK (X.G.P.ι v ((X.G.P.σ v ^ s.val) (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ ≤ 1
  rw [hy, (X.G.P.setting v).ι_comp]
  exact E.int _

theorem norm_tw_unit (v : X.Pl) (s : Fin (X.G.P.n' v)) (u : (X.G.P.W v)ˣ) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    ‖tw X ℂ_[p] v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))‖ = 1 := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  refine le_antisymm (norm_tw_int X E v s _) ?_
  have h1 : tw X ℂ_[p] v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)) *
      tw X ℂ_[p] v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  calc (1 : ℝ) = _ := h2.symm
    _ ≤ ‖tw X ℂ_[p] v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_tw_int X E v s _) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_tw (v : X.Pl) (s : Fin (X.G.P.n' v)) {x : X.G.P.Qq v} (hx : x ≠ 0) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    ‖tw X ℂ_[p] v s x‖ = ‖(p : ℂ_[p])‖ ^ ordP (X.G.P.W v) p x := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  have hS := X.G.P.setting v
  have := hS.frac_alt
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hS.p_unif hx
  rw [ordP_eq hS.p_unif, map_mul, map_zpow₀, map_natCast, norm_mul, norm_zpow, norm_tw_unit X E v s u, one_mul]

theorem prod_zpow_eq {ι : Type} (S : Finset ι) {r : ℝ} (hr : r ≠ 0) (e : ι → ℤ) :
    ∏ i ∈ S, r ^ e i = r ^ ∑ i ∈ S, e i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hr, ih]

theorem sum_sign_w (v : X.Pl) (l : ℕ) :
    ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * X.w v l s = X.vm v l := by
  unfold Sys.vm
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : IsOddPos s <;> simp [h]

theorem norm_kapG (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    ‖kapG X ℂ_[p] j c γ‖ = 1 := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  have hr : ‖(p : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 pC_ne_zero
  rw [kapG_eq, norm_mul, norm_mul]
  have h1 : ‖chiC X ℂ_[p] j c γ‖ = 1 := norm_unit E.iK E.int _
  have h2 : ‖cA X ℂ_[p] j (gamAt X j c γ)‖ * ‖pP X ℂ_[p] j (gamAt X j c γ)‖ = 1 := by
    unfold cA pP
    rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [norm_prod, norm_zpow]
    have h3 : ∀ s : Fin (X.G.P.n' v),
        ‖(tw X ℂ_[p] v s (gamAt X j c γ v :
          Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^
            ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s)‖ =
        ‖(p : ℂ_[p])‖ ^ (ordP (X.G.P.W v) p (gamAt X j c γ v :
          Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det *
            ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s)) := by
      intro s
      rw [norm_zpow, norm_tw X E v s (gl_det_ne _), ← zpow_mul]
    rw [Finset.prod_congr rfl fun s _ => h3 s, prod_zpow_eq _ hr, ← Finset.mul_sum, sum_sign_w, ← zpow_add₀ hr]
    have : ∀ a b : ℤ, a * b + -(b * a) = 0 := fun a b => by ring
    rw [this, zpow_zero]
  rw [h1, one_mul, h2]

theorem norm_chiN (j : ℕ) (La : X.Lt j) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    ‖chiN X ℂ_[p] hfin j La‖ = 1 := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  show ‖(kapG X ℂ_[p] j La.1 (delt X hfin j La.1 La.2))⁻¹‖ = 1
  rw [norm_inv, norm_kapG X E, inv_one]

end Rec

end Formalism.L2.G.Pend
end
end

section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

theorem oddDeg_of_vt (X : Sys p) (j : ℕ) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).Vtup) : OddDeg X j G := by
  classical
  intro m hm b hb
  obtain ⟨d, hd, hw⟩ := vtOddDeg X j G hG b.1 b.2 hb
  have h1 : Finsupp.weight (wBk X j b.1 b.2) m = d := hw (MvPolynomial.mem_support_iff.1 hm)
  rw [← hd, ← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wBk blkJ
  by_cases hx : (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = b
  · have hx' : (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨b.1, b.2⟩ := hx
    rw [if_pos hx, if_pos hx']
    simp
  · have hx' : ¬ (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨b.1, b.2⟩ := hx
    rw [if_neg hx, if_neg hx']
    simp

def GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (G : (X.Pj j).Xsp) : Prop :=
  GoodG X Kc j G ∧ OddDeg X j G

theorem vtIn_GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] : VtIn X (GdC X Kc) :=
  fun j G hG => ⟨vtGood X Kc j G hG, oddDeg_of_vt X j G hG⟩

theorem delEquivOn_GdC (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] :
    DelEquivOn X Kc (GdC X Kc) :=
  fun j A G f hG => (delEquivH X Kc j A G f hG.1 hG.2).2

structure CEmbC (G : GAtP p) extends CEmb G where
  rd : ∀ v, G.P.W v →+* WW p
  compat : Compat G toCEmb rd

variable (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

abbrev pendT : Pend X := pendR X E.toCEmb hfin hst (beLT hLT) (thFOf X pos F)




theorem invariance_iff_additive_maps_exist (D : Formalism.BasicNotions.D7) :
    Formalism.MainNotions.FormalGroupSystem.adm5 D X (pendT X E hfin hst hLT pos F) ↔
      ∀ v, ∀ j < X.mm, letI := algKfC E.toCEmb; XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j :=
  condition_iff_additive_maps X E.toCEmb hfin hst (beLT hLT) _ _ _ D

end Formalism.L2.G.Pend
end
end
