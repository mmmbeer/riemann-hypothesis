import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Built

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def chiStd (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_chiStd : Formalism.FourierDecayAlt.C6.IsCut0 chiStd := by
  unfold Formalism.FourierDecayAlt.C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · show ContDiff ℝ _ (Real.smoothTransition ∘ fun x : ℝ => 2 * x - 1)
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def towerOf (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.LevTower k r Wp Wq :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose

theorem towerOf_base (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : (towerOf B h1 h2 h3).base = B :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.1

theorem towerOf_norm (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.TowerNormalised (towerOf B h1 h2 h3) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.2

end tower

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

abbrev par (I : CarrierIn X u u') (v : Fin I.nf) : Formalism.FourierDecayAlt.M.Par := Formalism.FourierDecayAlt.D.parOf (sOf I) v

def sgOf {nf : ℕ} (G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (pl : Fin nf ≃ InfinitePlace D.host.E)
    (T T' : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (v : Fin nf) : ℂ :=
  Formalism.FourierDecayAlt.M.sgn ⟨G.k, G.r, T, T', (G.place (pl v)).u de, (G.place (pl v)).u de'⟩ l

theorem sg_of (I : CarrierIn X u u')
    (h : I.sg = sgOf I.G I.pl ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) I.de I.de' (I.l + 1)) :
    ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (par I v) ((sOf I).l + 1) := by
  intro v
  rw [h]
  rfl

def ParNums (I : CarrierIn X u u') : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u i - (par I v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u' i - (par I v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((par I v).k - 1), (par I v).lo i ≤ (par I v).hi i

def Types (I : CarrierIn X u u') : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z (I.T v).base.π (par I v).u ∧
    Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z' (I.T v).base.π' (par I v).u'

def Frames (I : CarrierIn X u u') : Prop := ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v)

def CoefCC (I : CarrierIn X u u') : Prop := ∀ v (m : ℕ), Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)

def CoefCap (I : CarrierIn X u u') : Prop :=
  ∀ v (Y : ℝ), ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r,
    Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g = (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g

theorem isPlace_of (I : CarrierIn X u u') (hN : ParNums I) (hty : Types I) (v : Fin I.nf) :
    Formalism.FourierDecayAlt.Q.IsPlace (par I v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' := by
  unfold Formalism.FourierDecayAlt.Q.IsPlace
  obtain ⟨h1, h2, h3⟩ := hN v
  obtain ⟨t1, t2⟩ := hty v
  obtain ⟨e1, e2⟩ := I.hT v
  have p1 := (I.T v).base.T_pos
  have p2 := (I.T v).base.T'_pos
  rw [e1] at p1
  rw [e2] at p2
  exact ⟨⟨(I.T v).base.k_pos, p1, p2, h1, h2, h3⟩, (I.T v).base.z_mem, (I.T v).base.z'_mem, e1, e2, t1, t2⟩

end Formalism.L2.SG.Pf.Built
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BaseOf

variable {k r : ℕ}

section Place

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

variable {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ)

def Qc (v : InfinitePlace X.B.I.F) : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ := Qcs C (X.pl v)
def Qic (v : InfinitePlace X.B.I.F) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ := Qics C (X.pl v)

theorem transpC (v : InfinitePlace X.B.I.F) : IsTranspC X v (cfS D) D.R.k D.R.rS (Qc X C v) (Qic X C v) := by
  have hrd : D.host.rdE ≠ 0 := by
    unfold Formalism.BasicNotions.Host.rdE
    exact (Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (K := D.host.E))) _).ne'
  have hc : cfS D ≠ 0 := by
    unfold cfS
    simp [Real.pi_ne_zero, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]
  have hf : frS D ≠ 0 := by
    unfold frS
    simp [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v, hrd, Real.pi_ne_zero]
  have hμ : muT D ≠ 0 := by
    unfold muT
    exact div_ne_zero hc hf
  have hμf : muT D * frS D = cfS D := by
    unfold muT
    field_simp
  have hμm : ∀ m : ℕ, muT D ^ m ≠ 0 := fun m => pow_ne_zero m hμ
  have hsm : ∀ m : ℕ, star (muT D) ^ m ≠ 0 := fun m => pow_ne_zero m (star_ne_zero.mpr hμ)
  have hTT : torS (muT D)⁻¹ D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS = 1 := by
    unfold torS
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    beta_reduce
    split_ifs
    · rw [← mul_pow, inv_mul_cancel₀ hμ, one_pow]
    · rw [← mul_inv, ← star_mul', ← mul_pow, inv_mul_cancel₀ hμ, one_pow, star_one, inv_one]
    · rw [mul_one]
  have hTT' : torS (muT D) D.R.k D.R.rS * torS (muT D)⁻¹ D.R.k D.R.rS = 1 := by
    unfold torS
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    beta_reduce
    split_ifs
    · rw [← mul_pow, mul_inv_cancel₀ hμ, one_pow]
    · rw [← mul_inv, ← star_mul', ← mul_pow, mul_inv_cancel₀ hμ, one_pow, star_one, inv_one]
    · rw [mul_one]
  have hH : (torS (muT D) D.R.k D.R.rS)ᴴ * Hpk D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS = Hpk D.R.k D.R.rS := by
    ext i j
    unfold torS
    rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul]
    simp only [Pi.star_apply, Hpk]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> first
      | (simp; done)
      | (exfalso; omega)
      | (have e : 2 * D.R.rS + D.R.k - (j : ℕ) = i := by omega
         rw [e, mul_one, mul_inv_cancel₀ (star_ne_zero.mpr (hμm _))])
      | (have e : 2 * D.R.rS + D.R.k - (i : ℕ) = j := by omega
         rw [e, mul_one]
         first | rw [star_inv₀] | rw [star_inv']
         rw [star_star, inv_mul_cancel₀ (hμm _)])
      | (have e : 2 * D.R.rS + D.R.k - (j : ℕ) = i := by omega
         rw [e]; simp [hμm, hsm]; done)
      | (have e : 2 * D.R.rS + D.R.k - (i : ℕ) = j := by omega
         rw [e]; simp [hμm, hsm]; done)
      | (subst_vars; exfalso; omega)
      | (subst_vars; simp; done)
      | (simp_all; done)
  have hTe : ∀ a : Fin D.R.rS, torS (muT D) D.R.k D.R.rS *ᵥ Pi.single (eI D.R.k D.R.rS a) 1 =
      muT D ^ (D.R.rS - (a : ℕ)) • Pi.single (eI D.R.k D.R.rS a) 1 := by
    intro a
    ext x
    unfold torS
    rw [Matrix.mulVec_diagonal]
    by_cases hx : x = eI D.R.k D.R.rS a
    · subst hx
      simp [eI]
    · simp [hx]
  have hTf : ∀ a : Fin D.R.rS, torS (muT D) D.R.k D.R.rS *ᵥ Pi.single (esI D.R.k D.R.rS a) 1 =
      (star (muT D ^ (D.R.rS - (a : ℕ))))⁻¹ • Pi.single (esI D.R.k D.R.rS a) 1 := by
    intro a
    ext x
    unfold torS
    rw [Matrix.mulVec_diagonal]
    by_cases hx : x = esI D.R.k D.R.rS a
    · subst hx
      have ha := a.isLt
      have e1 : ¬ (2 * D.R.rS + D.R.k - (a : ℕ) < D.R.rS) := by omega
      have e2 : D.R.rS + D.R.k < 2 * D.R.rS + D.R.k - (a : ℕ) := by omega
      have e3 : 2 * D.R.rS + D.R.k - (2 * D.R.rS + D.R.k - (a : ℕ)) = a := by omega
      simp [esI, e1, e2, e3]
    · simp [hx]
  obtain ⟨h1, h2, h3, h4⟩ := C.isT (X.pl v)
  have hvv : vOf X (X.pl v) = v := by simp [vOf]
  simp only [hvv] at h3 h4
  unfold IsTranspC Qc Qic Qcs Qics
  refine ⟨?_, ?_, ?_, fun a b hab => ⟨?_, ?_⟩⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.Qi _), h1, Matrix.one_mul, hTT]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (torS _ _ _), hTT', Matrix.one_mul, h2]
  · have h3' := congrArg (· * torS (muT D) D.R.k D.R.rS) h3
    simp only [Matrix.mul_assoc] at h3'
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [h3', ← Matrix.mul_assoc, hH]
  · rw [← Matrix.mulVec_mulVec, hTe a, Matrix.mulVec_smul, (h4 a b hab).1, smul_smul, ← mul_pow, hμf]
  · rw [← Matrix.mulVec_mulVec, hTf a, Matrix.mulVec_smul, (h4 a b hab).2, smul_smul, ← mul_inv, ← star_mul',
      ← mul_pow, hμf]

def zc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
  Qic X C v *ᵥ rv X.B.I v (X.zR u)

theorem zc_spec (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    inWb D.R.k D.R.rS (zc X C u v) ∧ Tz D.R.k D.R.rS (zc X C u v) = Tr D u :=
  zTr_of X (transpC X C v) u

theorem zc_pos (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : 0 < Tz D.R.k D.R.rS (zc X C u v) := by
  rw [(zc_spec X C u v).2]
  unfold Tr
  exact_mod_cast (D.mem u).A.T_prime.pos

def πc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) : X.Vloc u v →L[ℂ] X.Vloc u v :=
  X.piLoc u v (Formalism.L2.SG.RealObj.matQ (X.B.I.ε v) (X.wfr u v) (Qc X C v * m * Qic X C v))

theorem πc_type (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsHCTypeW D.R.k D.R.rS (zc X C u v) (fun i => ((D.hcW u (X.pl v)).u i : ℝ)) (πc X C u v) :=
  colsTypeTr_of X (Formalism.L2.SG.Pf.cfS_ne D) (transpC X C v) u

theorem πc_rep (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsCRepOn (UWset D.R.k D.R.rS (zc X C u v)) (πc X C u v) ∧
      (∀ h ∈ UWset D.R.k D.R.rS (zc X C u v), ∀ x, ‖πc X C u v h x‖ = ‖x‖) ∧
      ContinuousOn (πc X C u v) (UWset D.R.k D.R.rS (zc X C u v)) :=
  Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS (zc X C u v) _ (X.Vloc u v) (πc X C u v) (zc_spec X C u v).1
    (zc_pos X C u v) (πc_type X C u v)

def μGc (v : InfinitePlace X.B.I.F) : Measure (Mt D.R.k D.R.rS) :=
  (Formalism.REAL.muG (X.B.I.ε v)).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ))

theorem μGc_haar (v : InfinitePlace X.B.I.F) : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (μGc X C v) :=
  haarG_B (n_eq' X) (X.B.I.ε v) (transpC X C v).2.1 (transpC X C v).2.2.1

theorem μW_exists (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ μ : Measure (Mt D.R.k D.R.rS), Formalism.MainNotions.S.IsHaarOn (UWset D.R.k D.R.rS (zc X C u v)) μ ∧ μ Set.univ = 1 :=
  Formalism.MainNotions.S.Inh.haar_probability_compact_subgroup _ (Formalism.MainNotions.S.Inh.one_mem_unitary_stabilizer_set _) (Formalism.MainNotions.S.Inh.unitary_stabilizer_mul_mem _)
    (fun a => Hpk D.R.k D.R.rS * aᴴ * Hpk D.R.k D.R.rS)
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
    (fun a ha => Formalism.MainNotions.S.Inh.unitary_stabilizer_inv_mem _ a ha)
    (PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact _ _ _ (zc_spec X C u v).1 (zc_pos X C u v))

def μWc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Mt D.R.k D.R.rS) := (μW_exists X C u v).choose

theorem sec_c (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ, IsSection D.R.k D.R.rS (zc X C u v) (zc X C u' v) μsec :=
  sec_exists (k_pos D) _ _ (zc_pos X C u v) (zc_pos X C u' v)
    (let ⟨g, hg, _⟩ := πc_type X C u v; ⟨g, hg⟩) (let ⟨g, hg, _⟩ := πc_type X C u' v; ⟨g, hg⟩)

def baseOf (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Formalism.FourierDecayAlt.B.RealPlaceData D.R.k D.R.rS (X.Vloc u v) (X.Vloc u' v) where
  z := zc X C u v
  z' := zc X C u' v
  π := πc X C u v
  π' := πc X C u' v
  μG := μGc X C v
  μW := μWc X C u v
  μN := Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS
  μW' := μWc X C u' v
  μsec := (sec_c X C u u' v).choose
  χ := Formalism.FourierDecayAlt.P.character_exists_alt.choose
  k_pos := k_pos D
  z_mem := (zc_spec X C u v).1
  z'_mem := (zc_spec X C u' v).1
  T_pos := zc_pos X C u v
  T'_pos := zc_pos X C u' v
  π_rep := (πc_rep X C u v).1
  π'_rep := (πc_rep X C u' v).1
  π_unitary := (πc_rep X C u v).2.1
  π'_unitary := (πc_rep X C u' v).2.1
  π_cont := (πc_rep X C u v).2.2
  π'_cont := (πc_rep X C u' v).2.2
  haarG := μGc_haar X C v
  haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zc_spec X C u v).1 (zc_pos X C u v) (μW_exists X C u v).choose_spec.1
  haarN := Formalism.FourierDecayAlt.P.Dx2.MN.haar D.R.rS
  haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zc_spec X C u' v).1 (zc_pos X C u' v)
    (μW_exists X C u' v).choose_spec.1
  sec := (sec_c X C u u' v).choose_spec
  χ_smooth := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.1
  χ_supp := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.1
  χ_int := Formalism.FourierDecayAlt.P.character_exists_alt.choose_spec.2.2

end Place

section Carrier

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem baseOf_μW1 (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) : (baseOf X C u u' v).μW Set.univ = 1 := (μW_exists X C u v).choose_spec.2

theorem baseOf_μW'1 (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) : (baseOf X C u u' v).μW' Set.univ = 1 := (μW_exists X C u' v).choose_spec.2

def towersOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)) :=
  Formalism.L2.SG.Pf.Built.towerOf (baseOf X C u u' (tauE X e j)) (baseOf_μW1 X C u u' _) (baseOf_μW'1 X C u u' _) rfl

theorem towersOf_base (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    (towersOf X C u u' e j).base = baseOf X C u u' (tauE X e j) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower _ _ _ _ (baseOf X C u u' (tauE X e j)) (baseOf_μW1 X C u u' _)
    (baseOf_μW'1 X C u u' _) rfl).choose_spec.1

theorem Tz_towersOf_base_eq_T (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) :
    Tz D.R.k D.R.rS (towersOf X C u u' e j).base.z = ((D.mem u).A.T : ℝ) ∧
      Tz D.R.k D.R.rS (towersOf X C u u' e j).base.z' = ((D.mem u').A.T : ℝ) := by
  rw [towersOf_base]
  exact ⟨(zc_spec X C u _).2, (zc_spec X C u' _).2⟩

theorem cast_conj (u : D.what₂.Word) {w v : InfinitePlace X.B.I.F} (h : w = v)
    (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    (((castLoc X u h).symm.toContinuousLinearEquiv : X.Vloc u v →L[ℂ] X.Vloc u w).comp
      ((πc X C u v m).comp ((castLoc X u h).toContinuousLinearEquiv : X.Vloc u w →L[ℂ] X.Vloc u v))) = πc X C u w m := by
  subst h
  ext x
  rfl

def carrierIn (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierInOf X u u' e he hv C CA de de' l grid grid1 (towersOf X C u u' e) (Tz_towersOf_base_eq_T X C u u' e) fc χ sg ν' m₀
    top A₀

theorem fromX (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierIn X C u u' e he hv CA de de' l grid grid1 fc χ sg ν' m₀ top A₀))) :
    (CarrierOf (carrierIn X C u u' e he hv CA de de' l grid grid1 fc χ sg ν' m₀ top A₀) Mo).FromX := by
  intro v
  have hw : tauE X e ((tauE X e).symm v) = v := Equiv.apply_symm_apply _ v
  have hT := transpC X C v
  refine ⟨?_, ?_, ?_, fun m => ?_, fun m => ?_, ?_, ?_⟩
  · have h := isTransp_cs (Formalism.L2.SG.Pf.torTie X) C (X.pl v)
    rwa [show vOf X (X.pl v) = v from X.pl.symm_apply_apply v] at h
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.z = zc X C u v
    rw [towersOf_base]
    show zc X C u (tauE X e ((tauE X e).symm v)) = zc X C u v
    rw [hw]
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.z' = zc X C u' v
    rw [towersOf_base]
    show zc X C u' (tauE X e ((tauE X e).symm v)) = zc X C u' v
    rw [hw]
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.π m = _
    rw [towersOf_base]
    exact (cast_conj X C u (tauE_symm X e v) m).symm
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.π' m = _
    rw [towersOf_base]
    exact (cast_conj X C u' (tauE_symm X e v) m).symm
  · show (towersOf X C u u' e ((tauE X e).symm v)).base.μG = μGc X C v
    rw [towersOf_base]
    show μGc X C (tauE X e ((tauE X e).symm v)) = μGc X C v
    rw [hw]
  · show ∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ ∈
        Sset D.R.k D.R.rS (towersOf X C u u' e ((tauE X e).symm v)).base.z} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ)) =
        ((towersOf X C u u' e ((tauE X e).symm v)).base.μN.prod
          (towersOf X C u u' e ((tauE X e).symm v)).base.μW).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2))
    rw [towersOf_base]
    show ∃ μS : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ ∈
        Sset D.R.k D.R.rS (zc X C u (tauE X e ((tauE X e).symm v)))} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qc X C v) (Qic X C v) γ)) =
        ((Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS).prod (μWc X C u (tauE X e ((tauE X e).symm v)))).map
          (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2))
    rw [hw]
    exact muS_loc (n_eq' X) (X.B.I.ε v) hT.1 hT.2.1 hT.2.2.1 (zc_spec X C u v).1 (zc_pos X C u v)
      (μW_exists X C u v).choose_spec.1 (μW_exists X C u v).choose_spec.2 (Formalism.FourierDecayAlt.P.Dx2.MN.haar D.R.rS)

end Carrier

end Formalism.L2.SG.Pf.BaseOf
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def cutStd : Formalism.FourierDecayAlt.LE.Cut where
  χ := chiStd
  smooth := isCut0_chiStd.1
  zero x hx := Real.smoothTransition.zero_of_nonpos (by linarith)
  one x hx := Real.smoothTransition.one_of_one_le (by linarith)
  nonneg _ := Real.smoothTransition.nonneg _
  le_one _ := Real.smoothTransition.le_one _

theorem isCut0_cut (c : Formalism.FourierDecayAlt.LE.Cut) : Formalism.FourierDecayAlt.C6.IsCut0 c.χ :=
  ⟨c.smooth, ⟨1 / 2, by norm_num, fun x hx => c.zero x hx.le⟩, c.one⟩

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

abbrev parE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word) (de de' : ℕ → ℝ) (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.M.Par :=
  ⟨D.R.k, D.R.rS, ((D.mem u).A.T : ℝ), ((D.mem u').A.T : ℝ),
    ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).u de, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).u de'⟩

def carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierIn X C u u' e he hv CA de de' l grid grid1 fc c.χ
    (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) ν' m₀
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j) (ν' j) (m₀ j) (Θ j) (TP j)) A₀



end Formalism.L2.SG.Pf.CarrierT
end
end
