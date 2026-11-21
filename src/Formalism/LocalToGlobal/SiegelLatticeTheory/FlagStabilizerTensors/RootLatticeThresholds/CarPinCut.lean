import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbScale
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinAt
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeZhatTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpOrbQuot

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.MainNotions.S.Pv.Frames

variable {k r : ℕ}

private lemma apply_eq_ite_of_mulVec_bvec_eq' {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (hj : h *ᵥ bvec j = bvec j) (i : Fin n) : h i j = if i = j then 1 else 0 := by
  have e := congrFun hj i
  simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using e

private lemma Hpk_apply_sig_ne_zero {n : ℕ} {h H : Matrix (Fin n) (Fin n) ℂ} (hU : hᴴ * H * h = H) {p q : Fin n}
    (hcol : ∀ l, h l p = if l = p then 1 else 0) (hrow : ∀ m, H p m = if m = q then 1 else 0)
    (j : Fin n) : h q j = if q = j then 1 else 0 := by
  have hcolS : ∀ l, star (h l p) = if l = p then 1 else 0 := by
    intro l; rw [hcol]; split_ifs <;> simp
  have e1 : ∀ m, (hᴴ * H) p m = H p m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcolS, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e : (hᴴ * H * h) p j = H p j := by rw [hU]
  rw [Matrix.mul_apply] at e
  simp only [e1, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  rw [e]
  by_cases hq : q = j
  · subst hq; simp
  · simp [hq, Ne.symm hq]

private lemma Hpk_esI_apply_eq_ite_eI (a : Fin r) (m : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) m = if m = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hm := m.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma Hpk_eI_apply_eq_ite_esI (a : Fin r) (m : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) m = if m = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hm := m.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem fix_gen (d : Fin (2 * r + k + 1) → ℂ) (d0 : ℂ) (hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = d0)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : h ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, h *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ h *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : d i = d j := by
  have hUe : hᴴ * Hpk k r * h = Hpk k r := hU
  have colE : ∀ a : Fin r, ∀ l, h l (eI k r a) = if l = eI k r a then 1 else 0 :=
    fun a => apply_eq_ite_of_mulVec_bvec_eq' h _ (hfix a).1
  have colS : ∀ a : Fin r, ∀ l, h l (esI k r a) = if l = esI k r a then 1 else 0 :=
    fun a => apply_eq_ite_of_mulVec_bvec_eq' h _ (hfix a).2
  have rowE : ∀ a : Fin r, ∀ q, h (eI k r a) q = if eI k r a = q then 1 else 0 :=
    fun a => Hpk_apply_sig_ne_zero hUe (colS a) (Hpk_esI_apply_eq_ite_eI a)
  have rowS : ∀ a : Fin r, ∀ q, h (esI k r a) q = if esI k r a = q then 1 else 0 :=
    fun a => Hpk_apply_sig_ne_zero hUe (colE a) (Hpk_eI_apply_eq_ite_esI a)
  have out : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) →
      (∀ q, h p q = if p = q then 1 else 0) ∧ (∀ l, h l p = if l = p then 1 else 0) := by
    intro p hp
    rcases hp with hp | hp
    · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
      rw [← e]
      exact ⟨rowE _, colE _⟩
    · have hp2 := p.isLt
      have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p :=
        Fin.ext (show 2 * r + k - (2 * r + k - p.val) = p.val by omega)
      rw [← e]
      exact ⟨rowS _, colS _⟩
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [(out i hi).1 j] at hne
    by_cases hij : i = j
    · rw [hij]
    · exact absurd (if_neg hij) hne
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [(out j hj).2 i] at hne
      by_cases hij : i = j
      · rw [hij]
      · exact absurd (if_neg hij) hne
    · push_neg at hi hj
      rw [hmid i hi.1 hi.2, hmid j hj.1 hj.2]

def dD (k r : ℕ) (δ : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((δ ^ (r - i.val) : ℝ) : ℂ)
  else if r + k < i.val then (((δ ^ (r - (2 * r + k - i.val)))⁻¹ : ℝ) : ℂ) else 1

variable {δ : ℝ}

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem cj_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) :
    cj k r κ τ h = h := by
  ext i j
  rw [cj_apply]
  by_cases h0 : h i j = 0
  · rw [h0, mul_zero]
  · have e := fix_gen (fun i => ((tV k r κ τ i : ℝ) : ℂ)) 1 (fun i h1 h2 => by simp [tV_wb i h1 h2]) hh.1 hh.2.1 i j h0
    have e' : tV k r κ τ i = tV k r κ τ j := by exact_mod_cast e
    rw [e', inv_mul_cancel₀ (tV_pos hκ hτ j).ne']
    simp

theorem map_cjT_UW {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)}
    (h : IsHaarOn (UWset k r z) μ) : μ.map (cjT k r κ τ) = μ := by
  have hae : cjT k r κ τ =ᵐ[μ] id := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) h.2.2.1
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro hU
    apply hx
    funext i j
    show cj k r κ τ (Matrix.of x) i j = x i j
    rw [cj_UW hκ hτ hU]; rfl
  rw [Measure.map_congr hae, Measure.map_id]

theorem haarProb_unique {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn (UWset k r z) μ) (hμ1 : μ Set.univ = 1) (hν : IsHaarOn (UWset k r z) ν) (hν1 : ν Set.univ = 1) :
    μ = ν := by
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  have hC := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hK := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT
  have fin : ∀ (m : Measure (Mt k r)), m Set.univ = 1 → ∀ K : Set (Mt k r), IsCompact K → m K < ⊤ :=
    fun m hm K _ => (measure_mono (Set.subset_univ K)).trans_lt (by rw [hm]; exact ENNReal.one_lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 μ hC h0 hμ.2.2.1 hμ.2.2.2 (fin μ hμ1)
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ0 ν hC h0 hν.2.2.1 hν.2.2.2 (fin ν hν1)
  have hfin : μ0 Set.univ ≠ ⊤ := by
    have hle := measure_univ_le_add_compl (μ := μ0) (UWset k r z : Set (Mt k r))
    have hc0 : μ0 (UWset k r z : Set (Mt k r))ᶜ < ⊤ := (le_of_eq h0.conc).trans_lt ENNReal.zero_lt_top
    exact (lt_of_le_of_lt hle (ENNReal.add_lt_top.mpr ⟨h0.finite_compact _ hK, hc0⟩)).ne
  have hne : μ0 Set.univ ≠ 0 := by
    intro h; apply h0.ne_zero; rw [← Measure.measure_univ_eq_zero]; exact h
  have e1 : (c : ENNReal) * μ0 Set.univ = 1 := by rw [← hμ1, hc]; rfl
  have e2 : (d : ENNReal) * μ0 Set.univ = 1 := by rw [← hν1, hd]; rfl
  have hcd : (c : ENNReal) = d := by
    have := e1.trans e2.symm
    exact (ENNReal.mul_left_inj hne hfin).mp this
  rw [hc, hd, ENNReal.coe_injective hcd]

section Choice

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem muWc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ))
    (hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1) := by
  rw [map_cjT_UW (inv_pos.mpr (kaB_pos D)) one_pos (C.muW_haar u τ)]
  show (μW_exists X C u (vOf X τ)).choose = _
  obtain ⟨h1, h2⟩ := (μW_exists X C u (vOf X τ)).choose_spec
  generalize (μW_exists X C u (vOf X τ)).choose = m at h1 h2 ⊢
  have hS : UWset D.R.k D.R.rS (zc X C u (vOf X τ)) = UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [zc_vOf_eq_zB_of_inWb C u u τ hz, UWset_smul one_pos]
  rw [hS] at h1
  exact haarProb_unique hz hT h1 h2 (C.muW_haar u τ) (C.muW_one u τ)

end Choice

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {k r : ℕ}

theorem isRelStab_of_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) {g : Mx k r}
    (h : IsRelStab (turnL L ka) (tTi k r * g * tT k r)) : IsRelStab L g := by
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  intro a ha
  have ha' : tTi k r * a * tT k r ∈ RStab k r (tTi k r * g * tT k r) := (conjI_mem_RStab_iff g a).mpr ha
  have e2 : (tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) =
      tTi k r * (g⁻¹ * a * g) * tT k r := by
    rw [← conjI_inv, ← conjI_mul, ← conjI_mul]
  have := h _ ha'
  change psi k r L.z (cOfDpsi (ka : ℂ)) (tTi k r * a * tT k r) =
    psi k r L.z' (cOfDpsi (ka : ℂ)) ((tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r)) at this
  rw [e2, psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc'] at this
  exact this

theorem orbQuot_exists (L : LocBessel k r) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {μR : Measure (Mt k r)}
    (hμ : IsHaarOn (RStab k r g) μR) : ∃ ν : Measure (PairSp k r), IsOrbQuot L g μR ν := by
  have hν := Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top
  have : SigmaFinite (haarLie (Nset k r) 1) := hν.1
  have hs := PI.AmpOrbQuot.muN_smul L
  have : SFinite L.μN := by rw [hs]; infer_instance
  have hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN := by
    intro s hs'
    rw [hs, Measure.map_smul, hν.2.2.2 s hs']
  have hc : L.μN (PI.AmpOrbQuot.NS k r)ᶜ = 0 := by
    rw [hs, Measure.smul_apply, smul_eq_mul]
    have : haarLie (Nset k r) 1 (PI.AmpOrbQuot.NS k r)ᶜ = 0 := hν.2.2.1
    rw [this, mul_zero]
  exact PI.AmpOrbQuot.exists_isOrbQuot_of_isHaarOn L g μR hg hμ hN hc

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(C.isT τ).1, (C.isT τ).2.1, (C.isT τ).2.2.1, fun a => ((C.isT τ).2.2.2 a a rfl).1,
    fun a => ((C.isT τ).2.2.2 a a rfl).2⟩

theorem gB_mem (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gB C τ γ ∈ UH (Hpk D.R.k D.R.rS) :=
  Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_C C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ)

theorem relStab_of_relevant (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)) :
    IsRelStab (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (gB C τ γ) := by
  set L := toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT' with hL
  have hκ : (0 : ℝ) < (kaB D)⁻¹ := inv_pos.mpr (kaB_pos D)
  have hc : L.c = ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  apply isRelStab_of_turn L (kaB D) hc
  rw [← isRelStab_iff hκ one_pos (turnL L (kaB D)) (stdL L (kaB D) (kaB_pos D)) L.hz.1 L.hz'.1 rfl rfl rfl]
  have hz : (baseOf X C u u' (vOf X τ)).z = (stdL L (kaB D) (kaB_pos D)).z := zc_vOf_eq_zB_of_inWb C u u' τ L.hz.1
  have hz' : (baseOf X C u u' (vOf X τ)).z' = (stdL L (kaB D) (kaB_pos D)).z' := zc_vOf_eq_zB_of_inWb C u' u τ L.hz'.1
  have hcs : (stdL L (kaB D) (kaB_pos D)).c = cStd := stdL_c L (kaB D) (kaB_pos D)
  show IsRelStab (stdL L (kaB D) (kaB_pos D)) (gStd (kaB D) (gB C τ γ))
  have hγ : gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := gStd_eq C τ γ
  intro a ha
  rw [hγ] at ha ⊢
  have h2 := h.2 a ha
  rw [hz, hz'] at h2
  show psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z (stdL L (kaB D) (kaB_pos D)).c a =
    psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z' (stdL L (kaB D) (kaB_pos D)).c _
  rw [hcs]
  exact h2

section Scale

theorem det_sub_diag {m n : ℕ} (s l : Fin m → ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (h : n ≤ m) :
    ((Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ i : Fin n, s (Fin.castLE h i) * l (Fin.castLE h i)) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.diagonal (s ∘ Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
        Matrix.diagonal (l ∘ Fin.castLE h) := by
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp only [Function.comp]
  ring

theorem mono_scale {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : Formalism.FourierDecayAlt.C2.IsMonomial Z) {s l : Fin m → ℂ}
    (hs : ∀ i, s i ≠ 0) (hl : ∀ i, l i ≠ 0) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Matrix.diagonal s * Z * Matrix.diagonal l) := by
  obtain ⟨w, d, hd, rfl⟩ := hZ
  refine ⟨w, fun a => s (w a) * d a * l a, fun a => mul_ne_zero (mul_ne_zero (hs _) (hd a)) (hl a), ?_⟩
  ext i a
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs with h
  · rw [h]
  · simp

end Scale

theorem zhat_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1) :=
  Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_C C u τ) (trHyp_C C u' τ) one_ne_zero (uMat γ)

theorem mono_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ)) := by
  rw [zhat_B C u u' τ γ]
  exact mono_scale h (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i)

section GfTr

open Formalism.L2.SG.RealObj.InfCut

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem gf_pos_tr (hT : Formalism.L2.SG.Pf.Bridge.TrHyp F Qm Qim c) (hT' : Formalism.L2.SG.Pf.Bridge.TrHyp F' Qm Qim c)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (h : 0 < Gv F.T F'.T (Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A)) :
    0 < Formalism.QuantumDeterminants.Gf k r (Qim *ᵥ F.z) (Qim *ᵥ F'.z) (Qim * A * Qm) := by
  have hz := Formalism.L2.SG.Pf.Bridge.zhat_cs hT hT' one_ne_zero A
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin
  rw [hz, det_sub_diag, det_sub_diag, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT']
  have hsq : ∀ x : ℂ, star x * x = ((Complex.normSq x : ℝ) : ℂ) := fun x => by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [hsq, ← Complex.ofReal_prod, Complex.normSq_mul, Complex.normSq_ofReal]
  have hp : (∏ x : Fin ((Fin.last (r + 1) : Fin (r + 2)) : ℕ),
      Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) x))) =
        ∏ x : Fin ((⟨r, by omega⟩ : Fin (r + 2)) : ℕ), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1
          (Fin.castLE (Nat.le_of_lt_succ (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) := by
    show (∏ x : Fin (r + 1), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (le_refl (r + 1)) x))) =
      ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_succ r) x))
    rw [Fin.prod_univ_castSucc]
    have e1 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
    rw [e1, Formalism.L2.SG.Pf.Bridge.lam_last, map_one, mul_one]
    rfl
  rw [hp]
  set Λ : ℝ := ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ
    (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) with hΛ
  have hΛpos : 0 < Λ := Finset.prod_pos fun i _ => Complex.normSq_pos.mpr
    (Formalism.L2.SG.Pf.Bridge.lam_ne hT one_ne_zero _)
  unfold Gv Formalism.L2.SG.RealObj.Dl at h
  rw [dif_pos le_rfl, dif_pos (Nat.le_succ r)] at h
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h
  have hΛ2 : 0 < Λ * Λ := mul_pos hΛpos hΛpos
  have key := mul_pos hΛ2 h
  show 0 < Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (le_refl (r + 1))) (Fin.castLE (le_refl (r + 1)))).det -
    F.T * F'.T * (Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det)
  linarith [key]

end GfTr

theorem gf_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : 0 < Gv (Tw (D := D) u) (Tw (D := D) u')
      (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) :=
  gf_pos_tr (trHyp_C C u τ) (trHyp_C C u' τ) (uMat γ) h

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.Carrier.CarPinCut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cut_of_haar (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 F) (hGV : γ ∈ Formalism.FourierDecayAlt.B.GV k r) (hRel : Formalism.FourierDecayAlt.C6.IsRelevant B γ)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (hd : ∀ a, d a ≠ 0)
    (hZ : Formalism.QuantumDeterminants.Zhat k r B.z B.z' γ = Formalism.FourierDecayAlt.C2.monoP w d) (hGf : 0 < Formalism.QuantumDeterminants.Gf k r B.z B.z' γ)
    (hH : μ (Formalism.FourierDecayAlt.C6.Rset γ)ᶜ = 0 ∧ (∀ a ∈ Formalism.FourierDecayAlt.C6.Rset γ, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) ∧
      (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μ K < ⊤) ∧ μ ≠ 0) :
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut B γ μ θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) B.μSS := by
  obtain ⟨θ, hθ, hint⟩ := Formalism.FourierDecayAlt.P.orbital_integral_converges.choose_spec k r Wp Wq B γ w d A₀ F hGV hRel hd hZ hGf hA hCC
  have hMu := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq B γ w d hGV hd hZ
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Formalism.FourierDecayAlt.C6.Rset γ) (Formalism.FourierDecayAlt.D.muR B γ w) μ
    (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hGV)) hMu hH.1 hH.2.1 hH.2.2.1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hH.2.2.2
    rw [hc, h0, zero_smul]
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)
    exact this
  have hμ : μ = ENNReal.ofReal (c : ℝ) • Formalism.FourierDecayAlt.D.muR B γ w := by
    rw [hc, ENNReal.ofReal_coe_nnreal]
    rfl
  refine ⟨fun p => θ p / (c : ℝ), ?_, ?_⟩
  · rw [hμ, Formalism.L2.SG.Pf.Bridge.isNormCut_smul B γ _ hcpos]
    have e : (fun p => (c : ℝ) * (θ p / (c : ℝ))) = θ := by
      funext p; field_simp
    rw [e]
    exact hθ
  · have e : (fun p => (θ p / (c : ℝ)) • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) =
        fun p => ((c : ℝ)⁻¹ : ℝ) • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand B γ F p) := by
      funext p
      rw [smul_smul, div_eq_inv_mul]
    rw [e]
    exact hint.smul ((c : ℝ)⁻¹ : ℝ)

end Formalism.L2.SG.Pf.Carrier.CarPinCut

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.LocWSOf Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarFields {k r : ℕ} (U : Set (Formalism.FourierDecayAlt.B.Mat k r)) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  μ Uᶜ = 0 ∧ (∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) ∧ (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μ K < ⊤) ∧ μ ≠ 0

def FrameAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ ∈ Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
    (∃ (w : Equiv.Perm (Fin (D.R.rS + 1))) (d : Fin (D.R.rS + 1) → ℂ), (∀ a, d a ≠ 0) ∧
      Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
        (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) =
        Formalism.FourierDecayAlt.C2.monoP w d) ∧
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
      (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
      (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
    HaarFields (Formalism.FourierDecayAlt.C6.Rset
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ))
      (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
        (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x)))

theorem cutAt_of (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hF : FrameAt C u u' τ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c := by
  intro γ μRv ν hP
  obtain ⟨hGV, ⟨w, d, hd, hZ⟩, hGf, hH⟩ := hF γ μRv ν hP
  exact Formalism.L2.SG.Pf.Carrier.CarPinCut.cut_of_haar _ _ _ _ A₀ hA hCC hGV hP.2.2.1 w d hd hZ hGf hH

theorem trHyp_Qc (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ))
      (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ))
      (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).1, (Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.1,
    (Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.1,
    fun a => ((Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.2 a a rfl).1,
    fun a => ((Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)).2.2.2 a a rfl).2⟩

def HaarAtC (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    HaarFields (Formalism.FourierDecayAlt.C6.Rset
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ))
      (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
        (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x)))

set_option maxHeartbeats 2000000 in

theorem frameAt_of (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hH : HaarAtC C u u' τ) : FrameAt C u u' τ := by
  intro γ μRv ν hP
  obtain ⟨hG, hM, -, -, -⟩ := id hP
  refine ⟨Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_Qc C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ), ?_,
    gf_pos_tr (trHyp_Qc C u τ) (trHyp_Qc C u' τ) (uMat γ) hG, hH γ μRv ν hP⟩
  have hz : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z
      (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).z'
      (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam
        (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam
          (fun a : Fin D.R.rS => Formalism.L2.SG.LocWSOf.cfS D ^ (D.R.rS - (a : ℕ))) 1) :=
    Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_Qc C u τ) (trHyp_Qc C u' τ) one_ne_zero (uMat γ)
  have hm := mono_scale hM (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_Qc C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_Qc C u τ) one_ne_zero i)
  rw [← hz] at hm
  obtain ⟨w, d, hd, hwd⟩ := hm
  exact ⟨w, d, hd, hwd⟩

theorem cutAt_of_haar (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hH : HaarAtC C u u' τ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c :=
  cutAt_of C u u' τ a b ξ ξ' c (frameAt_of C u u' τ hH) A₀ hA hCC

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end
