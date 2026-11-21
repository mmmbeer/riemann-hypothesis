import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.HermitianCurvature.StatementTBB

section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Loc

variable (D : D7)

def PlaceOKS (Ch Cg : ℝ) (T T' : ℕ) (b dist dinf : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  PlaceOKR D Ch Cg T T' b dist v L f μsec ∧ ∀ s, |L.lam s - lamSH D.R (D.hc v) s| ≤ dinf

def BpLocS (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOKS D Ch Cg T T' b dist dinf v L f μsec →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (T : ℝ) (T' : ℝ) p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / Gpt (T : ℝ) (T' : ℝ) p) ^ A) *
          jNorm2 L f μsec

def BpRealS (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOKS D Ch Cg T T' b dist dinf v L f μsec →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ →
      ENNReal.ofReal (nLoc D T T' v γ) * orbSq L f (turnPt (ptLoc D v γ)) ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) *
          jNorm2 L f μsec

def QExpAtS (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (dist' dinf' : ℝ) (A : ℕ)
    (C : ℝ) (e : ℕ) (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ∃ (n : ℕ) (a : Fin n → ℝ) (L' : Fin n → LocBessel D.R.k D.R.rS)
      (f' : ∀ i, Mx D.R.k D.R.rS → ((L' i).Wq →L[ℂ] (L' i).Wp))
      (μ' : Fin n → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ),
      (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) ∧
      (∀ i, PlaceOKS D Ch Cg T T' b dist' dinf' v (L' i) (f' i) (μ' i)) ∧
      (∀ i, jNorm2 (L' i) (f' i) (μ' i) ≤ jNorm2 (X.L v) (X.f v) (X.μsec v)) ∧
      ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
          orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
        (∑ i, ENNReal.ofReal (a i) *
          (ENNReal.ofReal (nLoc D T T' v γ) * orbSq (L' i) (f' i) (turnPt (ptLoc D v γ))) ^ ((1 : ℝ) / 2)) ^ 2

variable {D}

theorem max_one_div_mul_le (α g : ℝ) (hα : 0 < α) (hg : 0 < g) :
    max 1 (1 / (α * g)) ≤ max 1 α⁻¹ * max 1 (1 / g) := by
  refine max_le ?_ ?_
  · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  · have e1 : 1 / (α * g) = α⁻¹ * (1 / g) := by field_simp
    rw [e1]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (by positivity) (le_trans zero_le_one (le_max_left _ _))

theorem frame_bounds {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) :
    2 ≤ b ∧ 1 ≤ b ^ (3 + Ch) ∧ D.host.rdE ≤ b ^ (3 + Ch) := by
  obtain ⟨⟨hk, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  have hbC : 1 ≤ b ^ Ch := by
    rcases le_total 1 (kaRe D) with h | h
    · exact h.trans hk1
    · exact ((one_le_inv₀ hka).2 h).trans hk2
  have hb0 : 0 < b := by linarith
  have hb3 : 1 ≤ b ^ (3 + Ch) := by
    rw [Real.rpow_add hb0]
    have : 1 ≤ b ^ (3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  exact ⟨hb2, hb3, Formalism.MainNotions.TheoremBConstants.rdE_le D b Ch hb2 hka hk2⟩

theorem ch_nonneg {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) : 0 ≤ Ch := by
  have hb2 := (frame_bounds hCg hok).1
  obtain ⟨⟨-, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have hlt : b ^ Ch < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hc
  rcases le_total 1 (kaRe D) with h | h
  · linarith
  · have := (one_le_inv₀ hka).2 h
    linarith

theorem bound_at {Ch Cg dist C : ℝ} {A e : ℕ} {T T' : ℕ} {b : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec)
    (γ : Point D.host.E (D.R.rS + 1)) (hγ : IsBPt D T T' γ) (p : Point ℂ (D.R.rS + 1))
    (hGp : Gpt (T : ℝ) (T' : ℝ) p = Gpt (T : ℝ) (T' : ℝ) (ptLoc D v γ))
    (hwp : ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) p = nLoc D T T' v γ)
    (hB : Gpt (T : ℝ) (T' : ℝ) p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (T : ℝ) (T' : ℝ) p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) * max 1 (1 / Gpt (T : ℝ) (T' : ℝ) p) ^ A) *
          jNorm2 L f μsec) :
    ENNReal.ofReal (nLoc D T T' v γ) * orbSq L f p ≤
      ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          (((b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2)) ^ A * max 1 (1 / absV D v (Gglob D T T' γ)) ^ A)) *
        jNorm2 L f μsec := by
  by_cases h0 : orbSq L f p = 0
  · simp [h0]
  obtain ⟨hb2, hR1, hRd⟩ := frame_bounds hCg hok
  obtain ⟨g, hg⟩ := exists_rep_of_orbSq L f p h0
  have hG0 := GPoint_nonneg_of_rep L p g hg
  rw [hok.2.2.2.2.1, hok.2.2.2.2.2] at hG0
  set α : ℝ := ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 with hαdef
  set gv : ℝ := Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
    (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) with hgvdef
  have hGeq : Gpt (T : ℝ) (T' : ℝ) p = α * gv := by rw [hGp, GPoint_loc]
  have hα : 0 < α := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
    positivity
  have hgvC : plEmb D v (Gglob D T T' γ) = (gv : ℂ) := plEmb_Gglob D T T' v γ
  have hgv0 : gv ≠ 0 := by
    intro h
    apply (map_ne_zero (plEmb D v)).2 hγ.2.1
    rw [hgvC, h, Complex.ofReal_zero]
  have hGne : Gpt (T : ℝ) (T' : ℝ) p ≠ 0 := by rw [hGeq]; exact mul_ne_zero hα.ne' hgv0
  have hGpos : 0 < Gpt (T : ℝ) (T' : ℝ) p := lt_of_le_of_ne hG0 (Ne.symm hGne)
  have hgpos : 0 < gv := by
    by_contra hc
    push_neg at hc
    nlinarith
  have habs : absV D v (Gglob D T T' γ) = gv := by
    unfold absV
    rw [hgvC, Complex.norm_real, Real.norm_of_nonneg hgpos.le]
  have main := hB hGne
  rw [hwp] at main
  refine main.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  rw [habs, hGeq]
  have hb0 : 0 < b := by linarith
  have hm1 : max 1 α⁻¹ ≤ (b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2) := by
    refine max_le (one_le_pow₀ hR1) ?_
    exact Formalism.MainNotions.TheoremBConstants.alfProd_inv_le D (b ^ (3 + Ch)) hR1 hRd D.R.rS (by omega)
  have hmax := max_one_div_mul_le α gv hα hgpos
  have hpow : max 1 (1 / (α * gv)) ^ A ≤
      ((b ^ (3 + Ch)) ^ ((2 * D.R.rS + 2) ^ 2)) ^ A * max 1 (1 / gv) ^ A := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (hmax.trans ?_) A
    exact mul_le_mul_of_nonneg_right hm1 (le_trans zero_le_one (le_max_left _ _))
  have hbC : 0 ≤ b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) := Real.rpow_nonneg hb0.le _
  exact mul_le_mul_of_nonneg_left hpow hbC





end Loc

def BesselExpansionLocal : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 CA Cinf Cg₀ : ℝ), 2 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        BpLocS D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C2 5


end Formalism.L2.SG.Pf.BesselExpansion
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Fr

variable (D : D7)

def PlaceOK1 (Ch Cg b dist dinf : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b 1 ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    (∀ s, |L.lam s - lamSH D.R (D.hc v) s| ≤ dinf) ∧ IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec

def BpLoc1 (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ^ A) * jNorm2 L f μsec

variable {D}


theorem gap_mono {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h h' : ℝ} (hg : GapAtLeast ε lam h) (hh : h' ≤ h) :
    GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)




end Fr


def BesselExpansionLocalFrame : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 CA Cinf Cgf Cg₀ : ℝ), 2 ≤ Cg₀ ∧ (∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) ∧
    ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        BpLoc1 D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C2 5



end Formalism.L2.SG.Pf.BesselExpansion
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def TopLevelBesselHypothesis : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (ν' : Fin (2 * r + (k0 + 1) + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r),
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
        0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        ThB.orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re)

theorem topLevelBesselHypothesis : TopLevelBesselHypothesis := by
  have hDF := Formalism.FourierDecayAlt.P.exists_isotropic_frame
  have hVI := Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep
  have hPR := Formalism.FourierDecayAlt.P.relevant_points_holds
  have hRM := root_measure_of_mu_R
  have hQE := quotient_exists
  have hCut := K_finite_decay
  have hRI := repIndep_of K_finite_decay orbital_norm_independence
  intro k0 r L Ds ν' m₀ hc hκ0' hκ1 hz hz' hπ hπ' hW hN hW' hBF
  have hκ0 : L.κN ≠ 0 := hκ0'.ne'
  intro F γ hK hdec hpos _
  have hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := isLocPt_swap γ
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz (k0 + 1) r Ds.z * Tz (k0 + 1) r Ds.z') r (γ.1.map Prod.swap) := by
    rw [ptG_eq_GPoint, hz, hz']
    exact hpos
  obtain ⟨g, hgG, hgZ, hgF⟩ := hDF (k0 + 1) r L.Wp L.Wq Ds ν' m₀ _ hBF hp hG
  have hvec := hVI (k0 + 1) r L.Wp L.Wq Ds ν' m₀ F _ hp g hBF hG hgG hgZ hgF
  have hrep : IsPtRep L γ g := ⟨hgG, by rw [← hz, ← hz', hgZ, ptMatN_swap]⟩
  have hrelD := hPR (k0 + 1) r L.Wp L.Wq Ds _ g hp hgG hgZ
  have hrel : IsRelStab L g := fun a ha => by
    have h1 := hrelD.2 a ha
    rw [hz, hz'] at h1
    rw [hc]
    exact h1
  have hroot := hRM k0 r L Ds γ g hp hc hz hz' hgG hgZ
  obtain ⟨ν, hq⟩ := hQE k0 r L γ g _ hc hκ0 hκ1 hrep hrel hroot
  have hcard_pos : (0 : ℝ) < Real.pi⁻¹ ^ (rootPat γ).card := by positivity
  have hl0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hcard_pos
  have hq' := isOrbQuot_rescale L _ ENNReal.ofReal_ne_top hq
  have hconc : Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))
      {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := by
    have h1 := hroot.1
    rw [Measure.smul_apply, smul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hl0
    · exact h
  have hne : Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)) ≠ 0 := by
    intro h0
    apply muR_ne_zero L hc γ g _ hroot
    rw [h0, smul_zero]
  have : SFinite (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) := by
    unfold Formalism.FourierDecayAlt.D.muR
    infer_instance
  have hcut := hCut k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hgG hgZ
  have hJ := orbJ_eq L Ds hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hgG hrel hconc hne hq' F hcut
  have hsm : OrbInt L F g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • ν) =
      (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν := by
    unfold OrbInt
    rw [integral_smul_measure]
  rw [hvec, hJ, hsm,
    orbSq_eq_of L F γ (hsNormSq (OrbInt L F g ν))
      (fun g' μ' ν' h' => hRI k0 r L Ds F γ hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hK hdec hpos g' μ' ν' g _ ν h' ⟨hrep, hrel, hroot, hq⟩)
      ⟨g, _, ν, hrep, hrel, hroot, hq⟩]
  congr 1
  rw [show (Formalism.FourierDecayAlt.B.hsInner ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν)
      ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν)).re =
      hsNormSq ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν) by rw [hsNormSq, hsInner_eq],
    Formalism.MainNotions.BigCellDensity.hsNormSq_smul, ENNReal.toReal_ofReal hcard_pos.le]
  rw [← card_rootPat γ]
  have h1 : Real.pi ^ (2 * (rootPat γ).card) * (Real.pi⁻¹ ^ (rootPat γ).card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (rootPat γ).card 2, ← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  rw [← mul_assoc, h1, one_mul]

end Formalism.L2.SG.Pf.BesselExpansion
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def parOfL {k r : ℕ} (L : LocBessel k r) (u u' : ℕ → ℝ) : Formalism.FourierDecayAlt.M.Par :=
  ⟨k, r, Tz k r L.z, Tz k r L.z', u, u'⟩

def PlTie {k r : ℕ} (L : LocBessel k r) {u u' : ℕ → ℝ} (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq) : Prop :=
  p.T.base.z = L.z ∧ p.T.base.z' = L.z' ∧ p.T.base.π = L.π ∧ p.T.base.π' = L.π' ∧ p.T.base.μW = L.μW ∧
    p.T.base.μN = L.μN ∧ p.T.base.μW' = L.μW'

def WeightTie : Prop :=
  ∀ (k r : ℕ) (T T' : ℝ) (p : Point ℂ (r + 1)), 1 ≤ k →
    ptWeight k r T T' p = Formalism.FourierDecayAlt.TBB.nPt k r (T * T') (p.1.map Prod.swap)

def EnergyTie : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u u' : ℕ → ℝ)
    (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq), 1 ≤ k → L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → PlTie L p →
    IsKFinCoefH L.σ f → Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f → IsSection k r L.z L.z' μsec →
    Formalism.FourierDecayAlt.TBB.jN2 p f ≤ ENNReal.ofReal (Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jNorm2 L f μsec

def CoefCC1 (Cgc : ℝ) : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsKFinCoefH L.σ f →
    GapAtLeast L.ε L.lam (Cgc * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) →
    Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f

def ThmBpTied (D : D7) (Ch Cg dist dinf : ℝ) (A : ℕ) (C₄ : ℝ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS →
    ∃ (u u' : ℕ → ℝ) (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq) (n₀ p₀ : ℕ),
      PlTie L p ∧ 2 * p₀ + n₀ ≤ A ∧ Formalism.FourierDecayAlt.TBB.ThmBpAt p f b C₄ n₀ p₀

theorem tieTopXk (k r : ℕ) (hk : 1 ≤ k) (L : LocBessel k r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat k r) :
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 F →
        0 < Gpt (Tz k r L.z) (Tz k r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact topLevelBesselHypothesis k0 r L Ds ν' m₀

theorem pc_le (r : ℕ) (s : List ℕ) : Formalism.MainNotions.BigCellDensity.pc r s ≤ (r + 1) ^ 2 := by
  unfold Formalism.MainNotions.BigCellDensity.pc
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem exists_relrep {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (h : orbSq L F γ ≠ 0) : ∃ g, IsPtRep L γ g ∧ IsRelStab L g := by
  by_contra hne
  apply h
  unfold orbSq
  refine le_antisymm ?_ bot_le
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  exact (hne ⟨g, hg.1, hg.2.1⟩).elim

theorem ew_top {P : Formalism.FourierDecayAlt.M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (F : Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : Formalism.FourierDecayAlt.C.LPt)
    (hγ : Formalism.FourierDecayAlt.D.IsLocPt γ (P.r + 1)) (hn : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ) :
    Formalism.FourierDecayAlt.TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ =
      Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ) (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
  unfold Formalism.FourierDecayAlt.TBB.Ew Formalism.FourierDecayAlt.TBB.NP Formalism.FourierDecayAlt.KB.Pl.RR Formalism.FourierDecayAlt.D.RRplace
  rw [dif_pos ⟨hγ, hγ⟩, dif_neg (by omega), if_pos rfl, if_pos rfl]
  simp only [Formalism.FourierDecayAlt.TBB.normC, List.map_nil, List.prod_nil, div_one, Real.mul_self_sqrt hn,
    Complex.re_ofReal_mul]

def BpLoc1N (D : D7) (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ^ A) * jNorm2 L f μsec

def NScale1 : Prop :=
  ∀ (D : D7) (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ), BpLoc1N D Ch Cg dist dinf A C e → BpLoc1 D Ch Cg dist dinf A C e


theorem pointWeight_eq_blockWeight (k r : ℕ) (T T' GG : ℝ) (hk : 1 ≤ k) : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (∀ b ∈ bs, 1 ≤ b.2) → a + (bs.map Prod.snd).sum = r + 1 →
    (∀ x, bs.getLast? = some x → GG = Complex.normSq x.1 - T * T') →
    ptWeightFrom k r T T' a bs = Formalism.FourierDecayAlt.C.nAux k r GG (fun _ _ => 1) (a + 1) (bs.map Prod.swap)
  | [], a, _, _, _ => by simp [ptWeightFrom, Formalism.FourierDecayAlt.C.nAux]
  | (t, s) :: bs, a, hs, hsum, hlast => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    have hsum' : a + (s + (bs.map Prod.snd).sum) = r + 1 := by simpa using hsum
    have ih := pointWeight_eq_blockWeight k r T T' GG hk bs (a + s) (fun b hb => hs b (by simp [hb])) (by omega)
      (fun x hx => hlast x (by rw [List.getLast?_cons, hx]; rfl))
    simp only [ptWeightFrom, List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.C.nAux]
    rw [show a + 1 + s = a + s + 1 by omega, ← ih]
    congr 1
    by_cases hc : s = 1 ∧ a + 1 = r + 1
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩]
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons b bs' =>
          have := hs b (by simp)
          simp only [List.map_cons, List.sum_cons] at hsum'
          omega
      subst hbs
      obtain ⟨rfl, -⟩ := hc
      rw [hlast (t, 1) (by simp)]
    · rw [if_neg hc, if_neg (by omega), one_mul, show a + s + 1 - 1 = a + s by omega]
      have hle : a + s ≤ r + 1 := by omega
      have hexp : (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (a + s) + s - 3)) =
          ((2 * s * (Ml k r (a + s) + s - 3) : ℕ) : ℤ) := by
        unfold Formalism.FourierDecayAlt.C.Mlev Ml
        have h3 : 3 ≤ 2 * (r + 1 - (a + s)) + k + 1 + s := by omega
        push_cast [h3, Nat.sub_add_cancel hle]
        have e2 : ((r + 1 - (a + s) : ℕ) : ℤ) = (r : ℤ) + 1 - ((a + s : ℕ) : ℤ) := by omega
        rw [e2]
        push_cast
        ring
      rw [hexp, zpow_natCast]

theorem weightTie : WeightTie := by
  intro k r T T' p hk
  unfold ptWeight Formalism.FourierDecayAlt.TBB.nPt
  refine pointWeight_eq_blockWeight k r T T' _ hk p.1 0 (fun b hb => (p.2.1 b hb).2)
    (by rw [p.2.2, Nat.zero_add]) ?_
  intro x hx
  simp [Formalism.FourierDecayAlt.D.ptGG, Formalism.FourierDecayAlt.D.ptLast, List.getLast?_map, hx]


def TheoremBLocalExpansion : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C₄ CA Cinf Cgf Cgc Cg₀ : ℝ), 2 ≤ Cg₀ ∧ 0 ≤ C₄ ∧
    (∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) ∧ CoefCC1 Cgc ∧
    ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        ThmBpTied D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C₄



end Formalism.L2.SG.Pf.BesselExpansion
end
end
