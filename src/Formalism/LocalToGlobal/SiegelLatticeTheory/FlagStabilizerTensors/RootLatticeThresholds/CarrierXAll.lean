import Mathlib
import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.StatementTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierDataBuiltOfCompactTest
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTTypes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GridsRichITc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefCCT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVtRZero
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTFr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WeightDeterminantBlockEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJointAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoefCap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsBuiltPlaceOfCompactTest
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EnergyCompactTestBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsBuilt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSClosedP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsClosedCompactSupportOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit

section
noncomputable section

namespace Formalism.L2.SG.Pf.CarrierT

theorem polynomial_le_decay_threshold (r k i : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (hi0 : 0 ≤ i) (hi : i ≤ r) :
    9 * (i + 1) * (127 * (r + 1) ^ 3 * (20 * (r + 1) * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 1) +
      20 * (r + 1) * (1 + 3 * (r + 1)) * i +
      (6 * i + 3 * (r + 1)) * (5 + 3 * (r + 1) * (20 * (r + 1) + 2) * (2 * r + k + 1) + 20 * (r + 1) * r) ≤
    25000 * (2 * r + k + 1) ^ 7 := by
  lift r to NNReal using hr
  lift k to NNReal using hk
  lift i to NNReal using hi0
  calc _ ≤ 9 * ((r : ℝ) + 1) * (127 * ((r : ℝ) + 1) ^ 3 * (20 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 +
          (2 * (r : ℝ) + k + 1) ^ 3) + 1) +
        20 * ((r : ℝ) + 1) * (1 + 3 * ((r : ℝ) + 1)) * r +
        (6 * (r : ℝ) + 3 * ((r : ℝ) + 1)) * (5 + 3 * ((r : ℝ) + 1) * (20 * ((r : ℝ) + 1) + 2) *
          (2 * (r : ℝ) + k + 1) + 20 * ((r : ℝ) + 1) * r) := by gcongr
    _ ≤ 25000 * (2 * (r : ℝ) + k + 1) ^ 7 := by
      rw [← sub_nonneg]
      ring_nf
      positivity

def decayThreshold (Cc : ℝ) (k r : ℕ) : ℝ := (25000 + 21 * |Cc|) * (2 * (r : ℝ) + k + 1) ^ 7

section setting

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sliceBudget_decayThreshold (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (Cc : ℝ) :
    Formalism.FourierDecayAlt.JCT.SliceBudget S (decayThreshold Cc S.G.k S.G.r) := by
  intro v i hi
  have hi' : (i : ℝ) ≤ S.G.r := by exact_mod_cast hi
  have hpoly := polynomial_le_decay_threshold (S.G.r : ℝ) (S.G.k : ℝ) (i : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hi'
  have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.Ntop, Formalism.FourierDecayAlt.C.Kst]
    push_cast
    ring
  have hn7 : (0 : ℝ) ≤ (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 7 := by positivity
  calc _ = 9 * ((i : ℝ) + 1) * (127 * ((S.G.r : ℝ) + 1) ^ 3 * (20 * ((S.G.r : ℝ) + 1) *
          (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) + 1) +
        20 * ((S.G.r : ℝ) + 1) * (1 + 3 * ((S.G.r : ℝ) + 1)) * i +
        (6 * (i : ℝ) + 3 * ((S.G.r : ℝ) + 1)) * (5 + 3 * ((S.G.r : ℝ) + 1) * (20 * ((S.G.r : ℝ) + 1) + 2) *
          (2 * (S.G.r : ℝ) + S.G.k + 1) + 20 * ((S.G.r : ℝ) + 1) * S.G.r) := by
        simp only [Formalism.FourierDecayAlt.P5.Auser, Formalism.FourierDecayAlt.P5.mmUser, Formalism.FourierDecayAlt.P5.nV, hN]
        push_cast
        rw [hN]
    _ ≤ 25000 * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 7 := hpoly
    _ ≤ decayThreshold Cc S.G.k S.G.r := by
        unfold decayThreshold
        nlinarith [abs_nonneg Cc]

theorem poly_le_decayThreshold (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (Cc : ℝ) :
    Cc * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ decayThreshold Cc S.G.k S.G.r := by
  have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.Ntop, Formalism.FourierDecayAlt.C.Kst]
    push_cast
    ring
  rw [hN]
  unfold decayThreshold
  have hs : (1 : ℝ) ≤ (S.G.r : ℝ) + 1 := by linarith [(Nat.cast_nonneg S.G.r : (0 : ℝ) ≤ S.G.r)]
  have hsn : (S.G.r : ℝ) + 1 ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    linarith [(Nat.cast_nonneg S.G.r : (0 : ℝ) ≤ S.G.r), (Nat.cast_nonneg S.G.k : (0 : ℝ) ≤ S.G.k)]
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (S.G.r : ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = 2 * (S.G.r : ℝ) + S.G.k + 1 := ⟨_, rfl⟩
  rw [← hs_def, ← hn_def]
  rw [← hs_def] at hs hsn
  rw [← hn_def] at hsn
  have hs0 : 0 ≤ s := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hX0 : 0 ≤ s ^ 4 * (20 * s * n ^ 2 + n ^ 3) :=
    mul_nonneg (pow_nonneg hs0 4) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (sq_nonneg n))
      (pow_nonneg hn0 3))
  have hX : s ^ 4 * (20 * s * n ^ 2 + n ^ 3) ≤ 21 * n ^ 7 := by
    have h4 : s ^ 4 ≤ n ^ 4 := pow_le_pow_left₀ hs0 hsn 4
    have h1 : 20 * s * n ^ 2 + n ^ 3 ≤ 21 * n ^ 3 := by nlinarith [sq_nonneg n]
    calc s ^ 4 * (20 * s * n ^ 2 + n ^ 3) ≤ n ^ 4 * (21 * n ^ 3) := by
          apply mul_le_mul h4 h1 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (sq_nonneg n))
            (pow_nonneg hn0 3)) (pow_nonneg hn0 4)
      _ = 21 * n ^ 7 := by ring
  have hn7 : 0 ≤ n ^ 7 := pow_nonneg hn0 7
  calc Cc * s ^ 4 * (20 * s * n ^ 2 + n ^ 3) = Cc * (s ^ 4 * (20 * s * n ^ 2 + n ^ 3)) := by ring
    _ ≤ |Cc| * (s ^ 4 * (20 * s * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_right (le_abs_self Cc) hX0
    _ ≤ |Cc| * (21 * n ^ 7) := mul_le_mul_of_nonneg_left hX (abs_nonneg Cc)
    _ ≤ (25000 + 21 * |Cc|) * n ^ 7 := by nlinarith [abs_nonneg Cc]

end setting

end Formalism.L2.SG.Pf.CarrierT
end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Carrier

theorem propGram_of_vtTensor {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hB : Formalism.FourierDecayAlt.D.IsBuilt S T f χ ν' m₀ top A₀)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : Formalism.FourierDecayAlt.TB.Pt E → H)
    (hVt : Formalism.FourierDecayAlt.JCT.VtTensor S T f ν' m₀ Vt) : Formalism.FourierDecayAlt.C.PropGram S Vt := by
  exact Formalism.FourierDecayAlt.Final.jc_propGramOfPlaces E Wp Wq S
    _ (fun v => Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v) H Vt hVt
    (Formalism.FourierDecayAlt.Final.jc_gramPlaceBuilt Formalism.FourierDecayAlt.Final.d_ptPermSpec Formalism.FourierDecayAlt.Final.d_ptGSpec
      Formalism.FourierDecayAlt.Final.d_ptRelevant Formalism.FourierDecayAlt.Final.d_muRHaar Formalism.FourierDecayAlt.Final.jc_orbJCutScalar
      E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hB)

end Formalism.L2.SG.Pf.Carrier
end
end

section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

private theorem list_prod_apply_eq_foldr {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (l : List (Module.End ℂ W)) (v : W) :
    l.prod v = List.foldr (fun (T : W → W) (h : W) => T h) v
      (l.map (fun (T : Module.End ℂ W) => (T : W → W))) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.prod_cons, Module.End.mul_apply, ih]

private theorem qmF_eq_qdet_apply {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℕ}
    (E : Fin m → Fin m → Module.End ℂ W) (w : ℂ) (v : W) :
    Formalism.FourierDecayAlt.Q.qmF (fun a b => (E a b : W → W)) id id w v = (Formalism.REAL.qdet E w) v := by
  simp only [Formalism.FourierDecayAlt.Q.qmF, Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Module.End.mul_apply, Module.End.intCast_apply, list_prod_apply_eq_foldr, List.map_ofFn]
  rw [← Int.cast_smul_eq_zsmul ℂ]
  congr 2
  congr 1
  funext j y
  simp only [Function.comp, Formalism.REAL.Tm, id]
  split_ifs <;> simp [Module.algebraMap_end_apply, sub_smul, Nat.cast_smul_eq_nsmul]

theorem capacity_from_hermitian_char : CapFromHC := by
  intro Wp _ _ k r z u π hz hT hrep hcont hHC
  obtain ⟨g, ⟨hgU, hgfix, hgz⟩, hU⟩ := hHC
  haveI : FiniteDimensional ℂ Wp := hU.2.1
  intro Bs hBs w v
  have hfr := Formalism.FourierDecayAlt.P.QrCap.fr_frame hgU hgfix _ hgz
  have hcore := Formalism.FourierDecayAlt.P.QrCap.core (u := u) hz hT ⟨hrep, hcont⟩ hgU hgfix _ hgz hU.2.2.2 w v
  have hE : (fun a b => Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) Bs a b))
      = fun a b => ((Formalism.FourierDecayAlt.Qr.EB π Bs a b : Module.End ℂ Wp) : Wp → Wp) := by
    funext a b y
    exact Formalism.FourierDecayAlt.P.QrD.ecRep_eq hrep hcont (Formalism.FourierDecayAlt.P.QrD.frame_lie hBs a b).1
      (Formalism.FourierDecayAlt.P.QrD.frame_lie hBs a b).2 y
  have hcap : Formalism.FourierDecayAlt.Q.capRep k r π Bs w v = (Formalism.REAL.qdet (Formalism.FourierDecayAlt.Qr.EB π Bs) w) v := by
    simp only [Formalism.FourierDecayAlt.Q.capRep]
    rw [hE, qmF_eq_qdet_apply]
  rw [hcap, Formalism.FourierDecayAlt.P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hfr w, hcore]
  congr 1
  simp only [Formalism.FourierDecayAlt.Qr.cpol, Formalism.FourierDecayAlt.P.QrCap.lowK_allPos]
  have hI : Finset.Icc 1 k = (Finset.range k).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hI, Finset.prod_map, Finset.prod_range]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp [Nat.succ_sub_one, j.isLt]
  push_cast
  ring

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

variable {D : D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
  [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wq x)]

theorem ptSome_of (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) : PtSome S := by
  intro p hp
  have hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS p) (D.R.rS + 1) := by
    refine ⟨?_, ?_⟩
    · rw [show Formalism.L2.SG.DataInst.signPt D.R.rS p = Formalism.L2.SG.DataInst.signAux D.R.rS 1 p from rfl,
        Formalism.L2.SG.DataInst.sign_list_fst]
      have := hp.1
      unfold Formalism.FourierDecayAlt.TB.level at this
      rw [this, hr]
    · refine (Formalism.L2.SG.DataInst.sign_list_mem_nonzero D.R.rS 1 p).2 fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
      exact hp.2 k hk
  refine ⟨(Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩, ?_⟩
  unfold Formalism.L2.SG.RealObj.ptOfL Formalism.L2.SG.DataInst.ptOfList
  rw [dif_pos hL]

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def GNonNeg (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf), IsPtRep X u u' w γ → ∀ v, 0 ≤ GX X u u' D.host.rdE γ v

theorem lZero_of (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hG : GNonNeg X u u') :
    LZero X u u' sc i0 i0' FdN FdN' νq := by
  intro p w hp hng
  unfold VtPt
  rw [hp]
  simp only
  by_cases hrep : ∃ γ, IsPtRep X u u' w γ
  · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
    push_neg at h1
    obtain ⟨v, hv⟩ := h1
    have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW; rw [dif_pos hrep]; exact hrep.choose_spec
    have h0 : GX X u u' D.host.rdE (gamW X u u' w) v = 0 := le_antisymm hv (hG w _ hrepw v)
    have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
    have hn : nW X u u' w = 0 := by
      unfold nW
      refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      rw [h0, zero_pow (by omega), zero_mul]
    rw [hn, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  · have hV : unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w = 0 := by
      unfold unscaledOperatorAtPointRepresentative; rw [if_neg hrep]
    rw [hV, map_zero, smul_zero]

theorem gX_nonneg {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) : 0 ≤ GX X u u' D.host.rdE γ v := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := Formalism.L2.SG.Pf.CarrierT.isTransp_Qcs X C v
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  set gg : ℕ := D.host.g 0 * D.host.g 1
  have hTr : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hz := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u v
  have hz' := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u' v
  have hgv := Bridge.delta_GV hTr (Formalism.L2.SG.Pf.Carrier.uMat_unitary (γ v))
  have hG := Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz.1 hz'.1 (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u v)
    (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u' v) _ hgv
  have h1 := Bridge.zhat_cs hTr hTr' (sc := D.host.rdE) hrd.ne' (Formalism.MainNotions.S.uMat (γ v))
  set Zr := Formalism.L2.SG.RealObj.Zhat (X.B.I.ε v)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).z)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).z)
    (Formalism.MainNotions.S.uMat (γ v)) with hZr
  have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.zc X C u v) (Formalism.L2.SG.Pf.BaseOf.zc X C u' v)
      (Qim * Formalism.MainNotions.S.uMat (γ v) * Qm) =
      Matrix.diagonal (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a)) * Zr *
        Matrix.diagonal (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) := h1
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin at hG
  rw [hz.2, hz'.2, h1'] at hG
  have hgg0 : (0 : ℝ) < gg := by
    show (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
    exact_mod_cast Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor (gg : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a; unfold cTor; congr 1; rw [hκ]; push_cast; field_simp
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    exact_mod_cast (div_pos hgg0 (by positivity)).ne'
  have hlamne : ∀ a : Fin (D.R.rS + 1), Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a ≠ 0 := by
    intro a h0
    have := (Bridge.cS_lam hc hrd.ne' a).1
    rw [h0, mul_zero] at this
    exact pow_ne_zero _ hκ0 this.symm
  have hlast : Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE (Fin.last D.R.rS) = 1 := by
    have := (Bridge.cS_lam hc hrd.ne' (Fin.last D.R.rS)).1
    have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
      simp [Formalism.L2.SG.Pf.CarrierTop.cS]
    rw [hcl, one_mul] at this
    rw [this]; simp
  have hD1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))).det = RealObj.Dl M (D.R.rS + 1) :=
    fun M => by unfold RealObj.Dl; rw [dif_pos le_rfl]
  have hD2 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))).det = RealObj.Dl M D.R.rS :=
    fun M => by unfold RealObj.Dl; rw [dif_pos (Nat.le_succ _)]
  rw [hD1, hD2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hG
  have hGd := Bridge.G_diag D.R.rS Zr
    (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a))
    (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) (Tr D u * Tr D u') (by rw [hlast]; simp)
  rw [hGd] at hG
  have hne1 : (∏ i : Fin D.R.rS, star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => star_ne_zero.mpr (hlamne _)
  have hne2 : (∏ i : Fin D.R.rS, Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hlamne _
  have hpos := pow_pos (mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)) 2
  have := (mul_nonneg_iff_of_pos_left hpos).mp hG
  unfold GX Gv
  exact this

theorem lZero_of_choice {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : LZero X u u' sc i0 i0' FdN FdN' νq :=
  lZero_of X u u' sc i0 i0' FdN FdN' νq fun _ γ _ v => gX_nonneg X C u u' γ v

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isHCParam_cast {m n : ℕ} (h : m = n) (f : Fin n → ℝ) (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin m => f (Fin.cast h i)) := by
  subst h
  exact hf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem isHCParam_lamX (w : InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam w) := by
  have hf := Formalism.MainNotions.S.Inh.amp_isHCParam_lamSH D.R (D.hc (X.pl w))
  have e : X.B.lam w = fun i => lamSH D.R (D.hc (X.pl w)) (Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) i) := by
    funext i
    rw [X.lam_eq]
    rfl
  rw [e]
  exact isHCParam_cast _ _ hf

theorem gap_X {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (w : InfinitePlace X.B.I.F) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h := by
  refine ⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L, ?_, ?_⟩
  · have hg := Formalism.MainNotions.BridgeLemma.szh_gap hS0 (X.pl w)
    set c : Fin X.B.I.n → Fin (2 * D.R.rS + D.R.k + 1) := Fin.cast (X.n_eq.trans (dimS_eq D.R).symm) with hc
    have ea : ∀ a, X.B.I.ε w a = epsSH D.R (c a) := fun a => by rw [X.eps_eq]; rfl
    have la : ∀ a, X.B.lam w a = lamSH D.R (D.hc (X.pl w)) (c a) := fun a => by rw [X.lam_eq]; rfl
    intro a b hab
    rw [la a, la b]
    exact hg (c a) (c b) (by rwa [ea a, ea b] at hab)
  · have hn : (D.R.r : ℝ) = (X.B.I.n : ℝ) := by rw [X.n_eq]
    have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
    have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
    have hn900 : (900 : ℝ) ≤ (X.B.I.n : ℝ) := by
      rw [← hn, hr]; push_cast
      have : (1801 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
      have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _
      linarith
    have hthr := Formalism.MainNotions.GapDS.thrX_le (X.B.I.ε w) hn900
    rw [← hn] at hthr
    have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) (X.pl w)
    have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
    have hL : (1 / 2 : ℝ) ≤ large₂.sc.L := by
      by_contra hcn
      push Not at hcn
      have h1 : Real.exp (2 * large₂.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      linarith
    have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
      have : 2 ≤ D.R.f := by
        unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
      exact_mod_cast this
    have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
      have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
      norm_num at this; linarith
    have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
      rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
    have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    have h3 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have e3 : 1000 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right hCl hn19
    have hr0 : (0 : ℝ) < (D.R.r : ℝ) ^ 19 := by positivity
    linarith

theorem smooth_tr {n m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (J : Matrix (Fin n) (Fin n) ℂ) (K : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (h3 : Qᴴ * J * Q = K) (b : H) (hs : Formalism.QuantumDeterminants.SmoothOnH K (fun x => σ (Q * x * Qi) b)) :
    Formalism.QuantumDeterminants.SmoothOnH J (fun g => σ g b) := by
  have h2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.QuantumDeterminants.inUH J g → Formalism.QuantumDeterminants.inUH K (Qi * g * Q) := by
    intro g hg
    have hg' : gᴴ * J * g = J := hg
    show (Qi * g * Q)ᴴ * K * (Qi * g * Q) = K
    rw [← h3]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qiᴴ Qᴴ, h2', Matrix.one_mul, ← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
    rw [← Matrix.mul_assoc gᴴ J, ← Matrix.mul_assoc (gᴴ * J) g, hg']
  have hback : ∀ g : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * g * Q) * Qi = g := by
    intro g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let Lφ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Qi * g * Q
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  have hφ : ContDiff ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℂ => Qi * g * Q) :=
    (LinearMap.toContinuousLinearMap Lφ).contDiff
  intro g₀ hg₀
  obtain ⟨U, F, hUo, h0, hF, hE⟩ := hs (Qi * g₀ * Q) (hU g₀ hg₀)
  refine ⟨(fun g => Qi * g * Q) ⁻¹' U, fun g => F (Qi * g * Q), hUo.preimage hφ.continuous, h0,
    hF.comp (hφ.of_le le_top).contDiffOn (fun g hg => hg), ?_⟩
  intro g hgU hgJ
  have := hE _ hgU (hU g hgJ)
  simp only [hback] at this
  exact this

variable {θ : ℝ} (C : Choice X θ)

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in

theorem coefCap_ITc {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 1000 ≤ Cl)
    (hk : 1801 ≤ D.R.k) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) :
    CoefCap (ITc X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c i0' Θ TP A₀) := by
  have hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)) := by
    intro j
    have hsmv : Formalism.MainNotions.S.IsSmoothVec (k := D.R.k) (r := D.R.rS)
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j) :=
      Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D (e (plE D j))) _
        (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
        (Formalism.L2.SG.Pf.dsTr C (e (plE D j))) (b j) (hkb j)
    obtain ⟨h1, h2, h3, -⟩ := C.isT (e (plE D j))
    exact smooth_tr (X.B.σ (vOf X (e (plE D j)))) _ _ (C.Q (e (plE D j))) (C.Qi (e (plE D j))) h1 h2 h3 (b j) hsmv
  exact coefCap_carrierInT X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀
    hb (isHCParam_lamX X) (gap_X X hS0 hCl hk)

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCMT2

theorem carrier_input_exists_repaired (hPA : Formalism.FourierDecayAlt.P5.ThmPActual)
    (hLEM : Formalism.FourierDecayAlt.MA.LemmaEModel) (hMP : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2)
    (hBB : Formalism.FourierDecayAlt.KB.BuiltBounds2) (Cb : ℝ) :
    ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
      (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
      (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (jn CA : ℝ)
      (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ),
      CarrierDataBound X u u' sc i0 i0' FdN FdN' νq jn CA G0 de de' l C₆ Cc Cb →
      CarrierInput X u u' sc i0 i0' FdN FdN' νq δ M C₄ jn CA G0 de de' l := by
  obtain ⟨C₆, Cc, C₄, hC6, hC4, hmain⟩ := Formalism.FourierDecayAlt.P.real_inputs_closed_model_place_two hPA Formalism.FourierDecayAlt.P.radial_module_form
    Formalism.FourierDecayAlt.P.positive_density_moderate_growth Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Formalism.FourierDecayAlt.P.theorem_P_module_moderate_growth
    Formalism.FourierDecayAlt.P.radial_measure_is_haar hLEM Formalism.FourierDecayAlt.P.levels_of_built_setting Formalism.FourierDecayAlt.P.slices_finite_regularity_built hMP Formalism.FourierDecayAlt.P.top_positive_semidefinite
    hBB Cb
  refine ⟨C₆, Cc, C₄, hC6, hC4, fun D X u u' sc i0 i0' FdN FdN' νq δ M jn CA G0 de de' l hD => ?_⟩
  haveI : IsCMField D.host.E := instCMT2 D
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, i6, S, p, f, χ, A₀, c, τ, Q, Qi, eP, eQ, hCA, hG, hde, hde', hl,
    hComp, hB, hSB, hc, hcut, hVt, hBF, hBase, hTop, hVJ, hE⟩ := hD
  letI := i1; letI := i2; letI := i3; letI := i4; letI := i5; letI := i6
  obtain ⟨L, j, lam, Cm, σ, hM, hRI⟩ := hmain D.host.E Wp Wq S p f χ A₀ c _
    (VtPt X u u' sc i0 i0' FdN FdN' νq) hB hSB hc hcut hVt
  refine ⟨Wp, Wq, i1, i2, i3, i4, i6, S, Formalism.FourierDecayAlt.KB.plT S p, f, χ, Formalism.FourierDecayAlt.KB.plν S p, Formalism.FourierDecayAlt.KB.plm S p,
    Formalism.FourierDecayAlt.KB.plTop S p, A₀, τ, Q, Qi, eP, eQ, hCA, hG, hde, hde', hl, hComp, isBuilt_of_builtPlace hB, hBF, hBase, hTop,
    hVJ, ?_⟩
  unfold Formalism.L2.SG.DataInst.dOf
  rw [← hE L j lam Cm σ hM]
  exact hRI _ _ _ _

end Formalism.L2.SG.Pf.CarrierT
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.SpectralTiesReal

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj

def CarrierSideBoundPositive (Cb : ℝ) : Prop :=
  ∀ C₆ Cc : ℝ, 0 < C₆ → ∃ CA₀ : ℝ, ∀ CA : ℝ, CA₀ ≤ CA → 1 ≤ CA →
    ∀ C0 CG CDel cT Cb' : ℝ, 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb' → 1 < cT * Cb' →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
      (τ : D.what₂.Tau) (Cp Th' : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
      {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
      (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
      Formalism.BasicNotions.Ties D → u ≠ u' → k0 ≤ (gOf D e).k → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
        (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.CarrierT.CarrierDataBound T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq
        (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).IntN CA (gOf D e) (deOf D τ u) (deOf D τ u')
        (lOf D (deOf D τ u) (deOf D τ u')) C₆ Cc Cb

theorem carrierP_of_repaired_model (hPA : P5.ThmPActual) (hLEM : MA.LemmaEModel) (hMP : JCT.ModelPlaceBuilt2)
    (hBB : KB.BuiltBounds2) (Cb : ℝ) (hX : CarrierSideBoundPositive Cb) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨C₆, Cc, C₄, hC6, hC4, hmain⟩ :=
    Formalism.L2.SG.Pf.CarrierT.carrier_input_exists_repaired hPA hLEM hMP hBB Cb
  obtain ⟨CA₀, hrest⟩ := hX C₆ Cc hC6
  refine ⟨C₄, CA₀, hC4, fun CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7 => ?_⟩
  obtain ⟨k0, hk0⟩ := hrest CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7
  refine ⟨k0, fun Cg cb Cw cTf CT C0f hcb hcT => ?_⟩
  obtain ⟨C'₀, Cl₀, hcl⟩ := hk0 Cg cb Cw cTf CT C0f hcb hcT
  refine ⟨C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTi hne hk hH0 hPl hSz hi hPt hNu
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, S, T', f, χ, ν', m₀, top, A₀, τ', Qm, Qim, eP, eQ, h1, h2, h3, h4, h5, h6, -, -,
    h9, h10, h11, h12⟩ := hmain D T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq T.Y.δ T.Y.M _ CA _ _ _ _
    (hcl C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hTi hne hk hH0 hPl hSz hi hPt hNu)
  exact ⟨Wp, Wq, i1, i2, i3, i4, i5, S, T', f, ν', m₀, τ', Qm, Qim, eP, eQ, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12⟩

end Formalism.L2.SG.SpectralTiesReal
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCMT2

end Formalism.L2.SG.Pf.CarrierT

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.SpectralTiesReal

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj

theorem carrierP_of_compact_model (hPA : P5.ThmPActualCpt) (hLEM : MA.LemmaEModel) (hMP : JCT.ModelPlaceBuilt2)
    (hBB : KB.BuiltBounds2Cpt) (Cb : ℝ) (hX : CarrierSideBoundPositive Cb) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨C₆, Cc, C₄, hC₆, hC₄, H⟩ :=
    Formalism.FourierDecayAlt.P.RealInputsCompactSupport.real_inputs_closed_compact_support_of hPA Formalism.FourierDecayAlt.P.radial_module_form
      Formalism.FourierDecayAlt.P.positive_density_compact_support Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate
      Formalism.FourierDecayAlt.P.theorem_P_module_compact_support Formalism.FourierDecayAlt.P.radial_measure_is_haar hLEM
      Formalism.FourierDecayAlt.P.levels_of_built_setting Formalism.FourierDecayAlt.P.slices_finite_regularity_built hMP
      Formalism.FourierDecayAlt.P.top_positive_semidefinite hBB Cb
  obtain ⟨CA₀, hX1⟩ := hX C₆ Cc hC₆
  refine ⟨C₄, CA₀, hC₄, ?_⟩
  intro CA hCA h1CA C0 CG CDel cT Cb' h1 h2 h3 h4 h5 h6
  obtain ⟨k0, hk⟩ := hX1 CA hCA h1CA C0 CG CDel cT Cb' h1 h2 h3 h4 h5 h6
  refine ⟨k0, ?_⟩
  intro Cg cb Cw cTf CT C0f hcb hcTf
  obtain ⟨C'₀, Cl₀, hC⟩ := hk Cg cb Cw cTf CT C0f hcb hcTf
  refine ⟨C'₀, Cl₀, ?_⟩
  intro C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTies hu hk0 hHyp hpl hSz
    hi0 hPt hNu
  have hData := hC C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hTies hu hk0 hHyp hpl hSz
    hi0 hPt hNu
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, i6, S, p, f, χ, A₀, c, τ', Qm, Qim, eP, eQ,
    hCA', hG, hde, hde', hl, hComp, hBP, hSB, hc, hcut, hVt, hBX, hBase, hTop, hVJ, hjn⟩ := hData
  unfold CarrierFull
  refine ⟨Wp, Wq, i1, i2, i3, i4, i6, S, Formalism.FourierDecayAlt.KB.plT S p, f, Formalism.FourierDecayAlt.KB.plν S p,
    Formalism.FourierDecayAlt.KB.plm S p, τ', Qm, Qim, eP, eQ, hCA', hG, hde, hde', hl, hComp, hBase, hTop, hVJ, ?_⟩
  obtain ⟨L', j, lam, Cm, σ, hMod, hRI⟩ := H D.host.E Wp Wq S p f χ A₀ c _ _ hBP hSB hc hcut hVt
  rw [← hjn L' j lam Cm σ hMod]
  exact hRI _ _ _ _

end Formalism.L2.SG.SpectralTiesReal
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.FourierDecayAlt

theorem lenI_big (CDel Cb Cq : ℝ) (hCDel : 4 < CDel) (hCb : 0 < Cb) :
    ∃ k0 : ℕ, ∀ {ι : Type} [Fintype ι] (G : Sz.Glob ι) (bb : ℝ), k0 ≤ G.k → G.Hyp bb CDel Cb →
      Cq * ((G.k : ℝ) * ((G.r : ℝ) + 1) ^ 3 + ((G.r : ℝ) + 1) ^ 4) ≤ G.lenI := by
  set M0 : ℝ := 4 * |Cq| + 5 with hM0
  refine ⟨⌈Real.exp (M0 / Cb)⌉₊ + 2, ?_⟩
  intro ι _ G bb hk hH
  have hm : G.m = 2 * G.r + 2 := rfl
  have hfm : G.m ≤ G.f := hH.hmf
  have hf2 : 2 ≤ G.f := by omega
  have hne : Nonempty ι := by
    have : 0 < Fintype.card ι := by
      have : G.f = Fintype.card ι := rfl
      omega
    exact Fintype.card_pos_iff.mp this
  obtain ⟨w⟩ := hne
  have hbb1 : 1 < bb := hH.hbb
  have hk2 : 2 ≤ G.k := by omega
  have hkR : (2 : ℝ) ≤ (G.k : ℝ) := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < (G.k : ℝ) := by linarith

  have hkexp : Real.exp (M0 / Cb) ≤ (G.k : ℝ) := by
    have h1 : Real.exp (M0 / Cb) ≤ (⌈Real.exp (M0 / Cb)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (M0 / Cb)⌉₊ : ℕ) : ℝ) ≤ (G.k : ℝ) := by exact_mod_cast (by omega : ⌈Real.exp (M0 / Cb)⌉₊ ≤ G.k)
    linarith
  have hlogk : M0 / Cb ≤ Real.log (G.k : ℝ) := by
    rw [← Real.exp_le_exp, Real.exp_log hkpos]; exact hkexp
  have hCblog : M0 ≤ Cb * Real.log (G.k : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlogk hCb.le
    rwa [mul_div_cancel₀ _ hCb.ne'] at this

  have hb1 : (G.k : ℝ) ^ Cb ≤ G.b w 1 := hH.hnode w 1 le_rfl (by omega)
  have hb2 : G.b w 1 ≤ bb ^ 2 := (hH.hsmall w).hbj 1 le_rfl (by show 1 ≤ 2 * G.r + 2; omega)
  have hkb : (G.k : ℝ) ^ Cb ≤ bb ^ 2 := hb1.trans hb2
  have hlog : Cb * Real.log (G.k : ℝ) ≤ 2 * Real.log bb := by
    have hp : (0 : ℝ) < (G.k : ℝ) ^ Cb := Real.rpow_pos_of_pos hkpos _
    have := Real.log_le_log hp hkb
    rwa [Real.log_rpow hkpos, Real.log_pow, Nat.cast_ofNat] at this
  have hLb : M0 / 2 ≤ Real.log bb := by linarith

  set X : ℝ := (G.k : ℝ) * ((G.r : ℝ) + 1) with hX
  have hr0 : (0 : ℝ) ≤ (G.r : ℝ) := Nat.cast_nonneg _
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ (G.r : ℝ) + 1 := by linarith
    nlinarith
  have hfR : 2 * (G.r : ℝ) + 2 ≤ (G.f : ℝ) := by
    have : 2 * G.r + 2 ≤ G.f := by omega
    exact_mod_cast this
  have hM05 : 5 ≤ M0 := by rw [hM0]; have := abs_nonneg Cq; linarith
  have hbase : X * M0 ≤ (G.k : ℝ) * G.f * Real.log bb := by
    have e1 : X * M0 = (G.k : ℝ) * (2 * ((G.r : ℝ) + 1)) * (M0 / 2) := by rw [hX]; ring
    rw [e1]
    apply mul_le_mul _ hLb (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hkpos.le
  set base : ℝ := (G.k : ℝ) * G.f * Real.log bb with hbdef
  have hbase1 : 1 ≤ base := by nlinarith
  have hDel : base ^ CDel ≤ G.Del := hH.hDel
  have h4 : base ^ (4 : ℕ) ≤ base ^ CDel := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase1 (by norm_num; linarith)
  have hXM : (X * M0) ^ 4 ≤ base ^ 4 := pow_le_pow_left₀ (by positivity) hbase 4
  have hXM' : X ^ 4 * M0 ≤ (X * M0) ^ 4 := by
    have : M0 ≤ M0 ^ 4 := by
      have : (1 : ℝ) ≤ M0 := by linarith
      calc M0 = M0 ^ 1 := (pow_one _).symm
        _ ≤ M0 ^ 4 := pow_le_pow_right₀ this (by norm_num)
    calc X ^ 4 * M0 ≤ X ^ 4 * M0 ^ 4 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (X * M0) ^ 4 := by ring
  have hDX : X ^ 4 * M0 ≤ G.Del := by linarith

  have hp1 : (G.k : ℝ) * ((G.r : ℝ) + 1) ^ 3 ≤ X ^ 4 := by
    have hr1 : (1 : ℝ) ≤ (G.r : ℝ) + 1 := by linarith
    have a : (G.k : ℝ) ≤ (G.k : ℝ) ^ 4 := by
      calc (G.k : ℝ) = (G.k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (G.k : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have b : ((G.r : ℝ) + 1) ^ 3 ≤ ((G.r : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hr1 (by norm_num)
    rw [hX, mul_pow]; exact mul_le_mul a b (by positivity) (by positivity)
  have hp2 : ((G.r : ℝ) + 1) ^ 4 ≤ X ^ 4 := by
    have : (G.r : ℝ) + 1 ≤ X := by rw [hX]; nlinarith
    exact pow_le_pow_left₀ (by linarith) this 4
  have hP0 : 0 ≤ (G.k : ℝ) * ((G.r : ℝ) + 1) ^ 3 + ((G.r : ℝ) + 1) ^ 4 := by positivity
  have hCq : Cq * ((G.k : ℝ) * ((G.r : ℝ) + 1) ^ 3 + ((G.r : ℝ) + 1) ^ 4) ≤ |Cq| * (2 * X ^ 4) := by
    calc Cq * ((G.k : ℝ) * ((G.r : ℝ) + 1) ^ 3 + ((G.r : ℝ) + 1) ^ 4)
        ≤ |Cq| * ((G.k : ℝ) * ((G.r : ℝ) + 1) ^ 3 + ((G.r : ℝ) + 1) ^ 4) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hP0
      _ ≤ |Cq| * (2 * X ^ 4) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX1
  unfold Sz.Glob.lenI
  have : |Cq| * (2 * X ^ 4) ≤ G.Del / 2 - 5 / 2 := by
    have e : X ^ 4 * M0 = 4 * |Cq| * X ^ 4 + 5 * X ^ 4 := by rw [hM0]; ring
    nlinarith [abs_nonneg Cq]
  linarith

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped Matrix

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frameVec_facts {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hF : D.IsBaseFrame Bs ν' m₀) (hT : 0 < Tz k r Bs.z) (hT' : 0 < Tz k r Bs.z') :
    inWb k r (m₀ *ᵥ ν') ∧ herm (Hpk k r) (m₀ *ᵥ ν') Bs.z = 0 ∧ herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by
  obtain ⟨hw, hz, hn, hm, hmz⟩ := hF
  have hU : m₀ᴴ * Hpk k r * m₀ = Hpk k r := hm.1
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.inWb_mulVec hm hw, ?_, by rw [herm_mulVec hU]; exact hn⟩
  have h0 : herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ Bs.z') = 0 := by rw [herm_mulVec hU]; exact hz
  rw [hmz] at h0
  set c : ℂ := ((√(Tz k r Bs.z' / Tz k r Bs.z) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.mpr (div_pos hT' hT)).ne'
  have e : herm (Hpk k r) (m₀ *ᵥ ν') (c • Bs.z) = star c * herm (Hpk k r) (m₀ *ᵥ ν') Bs.z := by
    unfold herm
    rw [star_smul, smul_dotProduct, smul_eq_mul]
  rw [e] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (star_eq_zero.mp h) hc0
  · exact h

theorem typeProj_nonempty (hTP : Top.TypeProjExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (hP : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hF : D.IsBaseFrame Bs ν' m₀) :
    Nonempty (Top.TypeProj P Bs.π Bs.z (m₀ *ᵥ ν')) := by
  obtain ⟨hOK, hz, hz', hTz, hTz', hty, hty'⟩ := hP
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  obtain ⟨h1, h2, h3⟩ := frameVec_facts Bs ν' m₀ hF hT hT'
  exact hTP Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') ⟨hOK, hz, hz', hTz, hTz', hty, hty'⟩ h1 h2 h3

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

def ParNumsE (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ) : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (parE e u u' de de' v).k, ∃ n : ℤ, (parE e u u' de de' v).u i - (parE e u u' de de' v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (parE e u u' de de' v).k, ∃ n : ℤ, (parE e u u' de de' v).u' i - (parE e u u' de de' v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((parE e u u' de de' v).k - 1), (parE e u u' de de' v).lo i ≤ (parE e u u' de de' v).hi i

theorem parNumsE_of (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ)
    (h5 : ∀ (w : D.what₂.Word) τ, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hde : de = Formalism.MainNotions.BridgeLemma.deOf D u) (hde' : de' = Formalism.MainNotions.BridgeLemma.deOf D u') :
    ParNumsE (D := D) u u' e de de' := by
  intro v
  set τ := e (plE D v) with hτ
  have hu : ∀ (w : D.what₂.Word) (dw : ℕ → ℝ), dw = Formalism.MainNotions.BridgeLemma.deOf D w → ∀ i, 1 ≤ i → i ≤ D.R.k →
      ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D v)).u dw i = uOne D w τ i := by
    intro w dw hdw i h1 h2
    rw [Formalism.L2.SG.Pf.SzHypOf.gOf_place, hdw]
    exact Formalism.MainNotions.BridgeLemma.cfg_u D w τ (h5 w τ) i h1 h2
  have hsucc : ∀ (w : D.what₂.Word) (j : ℕ) (hj : j < D.R.k), uOne D w τ (j + 1) = (((D.hcW w τ).u ⟨j, hj⟩ : ℚ) : ℝ) :=
    fun w j hj => Formalism.MainNotions.BridgeLemma.uOne_succ D w τ j hj
  have hk : (parE e u u' de de' v).k = D.R.k := rfl
  have hpu : ∀ i, 1 ≤ i → i ≤ D.R.k →
      (parE e u u' de de' v).u i = uOne D u τ i :=
    fun i h1 h2 => hu u de hde i h1 h2
  have hpu' : ∀ i, 1 ≤ i → i ≤ D.R.k →
      (parE e u u' de de' v).u' i = uOne D u' τ i :=
    fun i h1 h2 => hu u' de' hde' i h1 h2
  have hint : ∀ (w : D.what₂.Word) (i : ℕ), 1 ≤ i → i ≤ D.R.k → ∃ n : ℤ, uOne D w τ i - uOne D u τ 1 = n := by
    intro w i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hsucc w j (by omega), show (1 : ℕ) = 0 + 1 from rfl, hsucc u 0 (by omega)]
    obtain ⟨z1, hz1⟩ := (D.hcW w τ).u_half ⟨j, by omega⟩
    obtain ⟨z2, hz2⟩ := (D.hcW u τ).u_half ⟨0, by omega⟩
    refine ⟨z1 - z2, ?_⟩
    rw [hz1, hz2]; push_cast; ring
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    rw [hpu i h1 h2, hpu 1 le_rfl (by omega)]
    exact hint u i h1 h2
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    rw [hpu' i h1 h2, hpu 1 le_rfl (by omega)]
    exact hint u' i h1 h2
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    have hk1 : i + 1 ≤ D.R.k := by omega
    unfold Formalism.FourierDecayAlt.M.Par.lo Formalism.FourierDecayAlt.M.Par.hi
    rw [hpu (i + 1) (by omega) hk1, hpu i h1 (by omega), hpu' (i + 1) (by omega) hk1, hpu' i h1 (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hsucc u (j + 1) (by omega), hsucc u j (by omega), hsucc u' (j + 1) (by omega), hsucc u' j (by omega)]
    have hvj : j < D.R.k - 1 := by omega
    set vv := (D.hcW u τ).v ⟨j, hvj⟩ with hvv
    have hvv' : (D.hcW u' τ).v ⟨j, hvj⟩ = vv := by rw [hvv, D.hcW_v, D.hcW_v]
    have hvi : ∃ z : ℤ, vv = z := (D.hcW u τ).v_int ⟨j, hvj⟩
    have a1 : (D.hcW u τ).u ⟨j + 1, by omega⟩ + 1 / 2 ≤ vv :=
      half_lt_int ((D.hcW u τ).u_half _) hvi ((D.hcW u τ).v_gt_u ⟨j, hvj⟩)
    have a2 : vv + 1 / 2 ≤ (D.hcW u τ).u ⟨j, by omega⟩ :=
      int_lt_half ((D.hcW u τ).u_half _) hvi ((D.hcW u τ).u_gt_v ⟨j, hvj⟩)
    have b1 : (D.hcW u' τ).u ⟨j + 1, by omega⟩ + 1 / 2 ≤ vv :=
      half_lt_int ((D.hcW u' τ).u_half _) hvi (hvv' ▸ (D.hcW u' τ).v_gt_u ⟨j, hvj⟩)
    have b2 : vv + 1 / 2 ≤ (D.hcW u' τ).u ⟨j, by omega⟩ :=
      int_lt_half ((D.hcW u' τ).u_half _) hvi (hvv' ▸ (D.hcW u' τ).u_gt_v ⟨j, hvj⟩)
    have c1 : (((D.hcW u τ).u ⟨j + 1, by omega⟩ : ℚ) : ℝ) + 1 / 2 ≤ (vv : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr a1; push_cast at h; linarith
    have c2 : (vv : ℝ) + 1 / 2 ≤ (((D.hcW u τ).u ⟨j, by omega⟩ : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr a2; push_cast at h; linarith
    have c3 : (((D.hcW u' τ).u ⟨j + 1, by omega⟩ : ℚ) : ℝ) + 1 / 2 ≤ (vv : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr b1; push_cast at h; linarith
    have c4 : (vv : ℝ) + 1 / 2 ≤ (((D.hcW u' τ).u ⟨j, by omega⟩ : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr b2; push_cast at h; linarith
    have := max_le (by linarith : (((D.hcW u τ).u ⟨j + 1, by omega⟩ : ℚ) : ℝ) ≤ (vv : ℝ) - 1 / 2)
      (by linarith : (((D.hcW u' τ).u ⟨j + 1, by omega⟩ : ℚ) : ℝ) ≤ (vv : ℝ) - 1 / 2)
    have := le_min (by linarith : (vv : ℝ) + 1 / 2 ≤ (((D.hcW u τ).u ⟨j, by omega⟩ : ℚ) : ℝ))
      (by linarith : (vv : ℝ) + 1 / 2 ≤ (((D.hcW u' τ).u ⟨j, by omega⟩ : ℚ) : ℝ))
    linarith

def TypesE (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ) : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType D.R.k D.R.rS (towersOf X C u u' e v).base.z (towersOf X C u u' e v).base.π
      (parE e u u' de de' v).u ∧
    Formalism.FourierDecayAlt.Q.IsType D.R.k D.R.rS (towersOf X C u u' e v).base.z' (towersOf X C u u' e v).base.π'
      (parE e u u' de de' v).u'

theorem typesE_of (hcap : CapFromHC) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ)
    (h5 : ∀ (w : D.what₂.Word) τ, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hde : de = Formalism.MainNotions.BridgeLemma.deOf D u) (hde' : de' = Formalism.MainNotions.BridgeLemma.deOf D u') :
    TypesE X C u u' e de de' := by
  intro v
  set τ := e (plE D v) with hτ
  have hpl : X.pl (tauE X e v) = τ := by
    show X.pl (X.pl.symm (e (plE D v))) = _
    rw [Equiv.apply_symm_apply]
  have hu : ∀ (w : D.what₂.Word) (dw : ℕ → ℝ), dw = Formalism.MainNotions.BridgeLemma.deOf D w → ∀ i ∈ Finset.Icc 1 D.R.k,
      ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D v)).u dw i =
        if h : i - 1 < D.R.k then (((D.hcW w (X.pl (tauE X e v))).u ⟨i - 1, h⟩ : ℚ) : ℝ) else 0 := by
    intro w dw hdw i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    rw [Formalism.L2.SG.Pf.SzHypOf.gOf_place, hdw, Formalism.MainNotions.BridgeLemma.cfg_u D w τ (h5 w τ) i h1 h2,
      dif_pos (by omega : i - 1 < D.R.k), hpl]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Formalism.MainNotions.BridgeLemma.uOne_succ D w τ j (by omega)]
    rfl
  have hb := towersOf_base X C u u' e v
  constructor
  · show Formalism.FourierDecayAlt.Q.IsType D.R.k D.R.rS (towersOf X C u u' e v).base.z (towersOf X C u u' e v).base.π _
    rw [hb]
    exact isType_of_hc hcap (zc_spec X C u _).1 (zc_pos X C u _) (πc_type X C u _) (πc_rep X C u _) _
      (hu u de hde)
  · show Formalism.FourierDecayAlt.Q.IsType D.R.k D.R.rS (towersOf X C u u' e v).base.z' (towersOf X C u u' e v).base.π' _
    rw [hb]
    exact isType_of_hc hcap (zc_spec X C u' _).1 (zc_pos X C u' _) (πc_type X C u' _) (πc_rep X C u' _) _
      (hu u' de' hde')

theorem isPlaceE (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ)
    (hN : ParNumsE (D := D) u u' e de de') (hty : TypesE X C u u' e de de') (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.Q.IsPlace (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
      (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' := by
  obtain ⟨h1, h2, h3⟩ := hN j
  have hT := Tz_towersOf_base_eq_T X C u u' e j
  refine ⟨⟨(towersOf X C u u' e j).base.k_pos, ?_, ?_, h1, h2, h3⟩, (towersOf X C u u' e j).base.z_mem,
    (towersOf X C u u' e j).base.z'_mem, hT.1, hT.2, (hty j).1, (hty j).2⟩
  · show (0 : ℝ) < (D.mem u).A.T
    rw [← hT.1]; exact (towersOf X C u u' e j).base.T_pos
  · show (0 : ℝ) < (D.mem u').A.T
    rw [← hT.2]; exact (towersOf X C u u' e j).base.T'_pos

theorem framesE (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.D.IsBaseFrame (towersOf X C u u' e j).base (nuE X C u' e i0' j) (m0E X C u u' e j) := by
  rw [towersOf_base]
  exact Formalism.L2.SG.Pf.CarrierBase.isBaseFrame_of X u u' (tauE X e j) rfl (isTransp_Qcs X C (tauE X e j)) _ rfl rfl _

def tpOf (hTP : Formalism.FourierDecayAlt.Top.TypeProjExists) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ)
    (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hN : ParNumsE (D := D) u u' e de de') (hty : TypesE X C u u' e de de')
    (j : Fin (nfE D)) :
    Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.z
      (m0E X C u u' e j *ᵥ nuE X C u' e i0' j) :=
  Classical.choice (typeProj_nonempty hTP (parE e u u' de de' j) (towersOf X C u u' e j).base (nuE X C u' e i0' j)
    (m0E X C u u' e j) (isPlaceE X C u u' e de de' hN hty j) (framesE X C u u' e i0' j))

theorem parNums_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (h : ParNumsE (D := D) u u' e de de') : ParNums (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) := h

theorem types_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (h : TypesE X C u u' e de de') : Types (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀) := h

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.L2.SG.Pf.Carrier.CarPinVt

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem cut_len {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (I : CarrierIn X u u') (v : Fin I.nf) :
    (sOf I).cutHi v - (sOf I).cutLo v = I.G.Del / 2 - 5 / 2 := by
  unfold Formalism.FourierDecayAlt.C.HidaSetting.cutHi Formalism.FourierDecayAlt.C.HidaSetting.cutLo
  have : ((sOf I).G.place ((sOf I).pl v)).Del = I.G.Del := rfl
  rw [this]; ring

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

def Ce : ℝ := (Formalism.FourierDecayAlt.P.energy_of_built_setting Formalism.FourierDecayAlt.P.beta_cutoff_limit).choose

def fourierDecayLevelZeroConst : ℝ := (Formalism.FourierDecayAlt.P.lemma_E_of_model Formalism.FourierDecayAlt.P.lemma_E_of_residue Formalism.FourierDecayAlt.P.level_zero_holds
  Formalism.FourierDecayAlt.P.good_of_admissible Formalism.FourierDecayAlt.P.lemma_model).choose

theorem carrierDataBuilt_of_towers (Cb Cc C₆ : ℝ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hN : ParNumsE (D := D) u u' e de de') (hty : TypesE X C u u' e de de') (hl2 : l + 2 ≤ D.R.k)
    (hΘ : ∀ j : Fin (nfE D),
      ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
        (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
        (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
        (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
        Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
        Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st (Θ j))
    (hDD : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.KB.InDDplus2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base Cb (Θ j))
    (hOk : ∀ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).Ok)
    (hw : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de') (hl1 : 1 ≤ l) (hne : de l ≠ de' l)
    (hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2)
    (hLc : Cc * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 +
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ)) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 +
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ)) ^ 3) ≤ (D.s.Del : ℝ) / 2 - 5 / 2)
    (hC6 : C₆ * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 +
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ)) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ (D.s.Del : ℝ) / 2 - 5 / 2)
    (hCA : Cc ≤ CA)
    (hA : Cc * ((D.R.rS : ℝ) + 1) ^ 4 *
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 +
        (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤ A₀)
    (hSB : Formalism.FourierDecayAlt.JCT.SliceBudget (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) A₀)
    (h : ℝ) (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) (hA0 : 0 ≤ A₀) (hAh : A₀ ≤ h / 2)
    (hka : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (a j))
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j))
    (hsm : ∀ j, Formalism.FourierDecayAlt.B.CkOn ⊤ (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (fcT X C e u u' a b ξ ξ' cc j))
    (hcap : CoefCap (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
    (hJT : Formalism.FourierDecayAlt.D.IsBuilt (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀ →
      JointTensorAt X u u' (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc
      (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).τ (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).eP (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).eQ sc i0 i0' νq) (hsc : 0 < sc)
    (hPt : PtSome (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)))
    (hW : WtTie X (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) u u')
    (hLz : LZero X u u' sc i0 i0' FdN FdN' νq)
    (hRz : RZero X (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) u u' (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (nuE X C u' e i0') (m0E X C u u' e))
    (hE2 : Formalism.FourierDecayAlt.D.IsBuilt (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀ →
      (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
      Formalism.FourierDecayAlt.D.GamLev (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
        (Formalism.FourierDecayAlt.D.deG (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) = jn)
    (hLe : Ce * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2)
    (hC6e : fourierDecayLevelZeroConst * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ (D.s.Del : ℝ) / 2 - 5 / 2)
    (hCAe : Ce ≤ CA)
    (hAe : Ce * ((D.R.rS : ℝ) + 1) ^ 4 *
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤ A₀)
    (hi : ∀ v, i0 v = i0' v) :
    CarrierDataBound X u u' sc i0 i0' FdN FdN' νq jn CA (Formalism.L2.SG.SpectralTiesReal.gOf D e) de de' l C₆ Cc Cb := by
  have hN' := parNums_ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀ hN
  have hty' := types_ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀ hty
  have hcc : CoefCC (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) :=
    Formalism.L2.SG.Pf.CoefCCT.coefCC_carrierInTc C u u' e he hv CA de de' l (gridT e l) (grid1T e l) a b ξ ξ' cc cutStd
      (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ (fun _ => h) (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _) hgap
      (fun _ => hok) hA0 (fun _ => hAh) hka hkb
  have hG := gridsOK_ITc X C u u' e he hv CA de de' l (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀ hlen hOk hl2
  have hR := gridsRich_ITc X C u u' e he hv CA de de' l (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀ hlen
  have hL : Formalism.FourierDecayAlt.JCT.LongCut Cc (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) := fun v => le_of_le_of_eq hLc (cut_len (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) v).symm
  have hB := isBuiltPlace_of_compact_test X C Cb Cc u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc)
    cutStd i0' Θ TP A₀ hN' hty' hcc hcap hΘ hDD hOk hw hw' hl1 hl2 hne hG hR hL hCA hsm hA
  have hcut : ∀ v, C₆ * ((D.R.k : ℝ) * (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).Ntop * ((D.R.rS : ℝ) + 1) ^ 2 +
        ((sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).Ntop : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤
      (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).cutHi v - (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).cutLo v := fun v => le_of_le_of_eq hC6 (cut_len (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) v).symm
  have hVJ := vJoint_of_tensorAt X u u' (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).τ
    (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).eP (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).eQ sc hsc i0 i0' hi νq (hJT (isBuilt_of_builtPlace hB))
  have hVt := vtTensor_of_steps X (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) u u' sc i0 i0' FdN FdN' νq (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (nuE X C u' e i0')
    (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).τ (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).eP (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).eQ hVJ hPt hW hLz hRz
  have hPG := propGram_of_vtTensor (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) _ _ _ _ _ _ A₀ (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1
    (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2 (isBuilt_of_builtPlace hB) _ hVt
  have hLe' : Formalism.FourierDecayAlt.JCT.LongCut Ce (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) := fun v => le_of_le_of_eq hLe (cut_len (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) v).symm
  have hIBP := isBuiltPlace_carrierInT X C Ce u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc)
    cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ hN' hty'
    (frames_carrierInT X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)
    hcc hcap hw hw' hl1 hl2 hne hG hLe' hCAe hsm hAe
  have hC6e' : ∀ v, fourierDecayLevelZeroConst * (((sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k : ℝ) * (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).Ntop * (((sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r : ℝ) + 1) ^ 2 +
      ((sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).Ntop : ℝ) ^ 2 * (((sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r : ℝ) + 1) ^ 2) ≤ (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).cutHi v - (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).cutLo v :=
    fun v => le_of_le_of_eq hC6e (cut_len (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) v).symm
  have hcutsm : ∀ v ε, 0 < ε → Formalism.FourierDecayAlt.B.CkOn ⊤ (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS)
      (Formalism.FourierDecayAlt.D.cutF ((ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ ((ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v) ε) :=
    fun v ε hε => Formalism.FourierDecayAlt.P.cutoff_smooth _ _ _ _ _ _ _ ε (isCut0_cut cutStd) (hsm v) hε
  have hE : ∀ (L : ∀ v : Fin (nfE D), Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (parE e u u' de de' v)
        (Formalism.FourierDecayAlt.MA.DQ (parE e u u' de de' v))) D.R.rS)
      (j : ∀ v : Fin (nfE D), Formalism.FourierDecayAlt.M.Ty (parE e u u' de de' v) →
        Formalism.FourierDecayAlt.MA.SmQ D.R.rS (parE e u u' de de' v).TT)
      (lam : ∀ v : Fin (nfE D), Fin (D.R.k + 2 * D.R.rS + 1) → ℝ) (Cm σ : Fin (nfE D) → ℝ),
      (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ v (L v) (j v) (lam v) cutStd (Cm v) (σ v)) →
      (∏ v, Formalism.FourierDecayAlt.JCT.jvModel (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) j Cm v) = jn := by
    intro L j lam Cm σ hM
    have hLE := (Formalism.FourierDecayAlt.P.lemma_E_of_model Formalism.FourierDecayAlt.P.lemma_E_of_residue Formalism.FourierDecayAlt.P.level_zero_holds
      Formalism.FourierDecayAlt.P.good_of_admissible Formalism.FourierDecayAlt.P.lemma_model).choose_spec.2 D.host.E _ _ (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀ L j lam cutStd Cm σ hIBP.2.2.2.1 hcutsm hC6e' hM
    have hjv := (Formalism.FourierDecayAlt.P.energy_of_built_setting Formalism.FourierDecayAlt.P.beta_cutoff_limit).choose_spec D.host.E _ _ (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
      (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀ _ hIBP hLE
    rw [← hE2 (isBuilt_of_builtPlace hB)]
    exact Finset.prod_congr rfl (fun v _ => hjv v)
  exact carrierDataBuilt_of_compact_test X C Cb Cc C₆ u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc)
    cutStd i0 i0' Θ TP A₀ sc FdN FdN' νq jn hN' hty' hl2 hΘ hB hSB hcut hVt hPG hVJ hE hi

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fcT_smooth {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ) (j : Fin (nfE D))
    (hkb : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) :
    Formalism.FourierDecayAlt.B.CkOn ⊤ (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (fcT X C e u u' a b ξ ξ' cc j) := by
  have hsmv : Formalism.MainNotions.S.IsSmoothVec (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j) :=
    Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D (e (plE D j))) _
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
      (Formalism.L2.SG.Pf.dsTr C (e (plE D j))) (b j) hkb
  have hcf := Formalism.L2.SG.Pf.CoefDecay.ss_cf hsmv (a j) (Formalism.L2.SG.Pf.CoefDecay.rk1 (ξ j) (ξ' j))
  have hμ := Formalism.L2.SG.Pf.muT_ne D
  set t := torS (muT D) D.R.k D.R.rS with ht
  set t' := torS (muT D)⁻¹ D.R.k D.R.rS with ht'
  have hfun : ∀ g, fcT X C e u u' a b ξ ξ' cc j g = cc j • Formalism.L2.SG.Pf.CoefDecay.cf
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (a j) (b j)
      (Formalism.L2.SG.Pf.CoefDecay.rk1 (ξ j) (ξ' j)) (t * g * t') := by
    intro g
    show cc j • Formalism.MainNotions.S.Pv.BetaCut.coefM _ (a j) (b j) (ξ j) (ξ' j) (t * g * t') = _
    congr 1
    ext x
    simp only [Formalism.MainNotions.S.Pv.BetaCut.coefM, Formalism.L2.SG.Pf.CoefDecay.cf, Formalism.L2.SG.Pf.CoefDecay.rk1,
      ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
    exact smul_comm _ _ _
  let Lφ : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS →ₗ[ℝ] Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS :=
    { toFun := fun g => t * g * t'
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  have hφ : ContDiff ℝ ⊤ (fun g : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS => t * g * t') :=
    (LinearMap.toContinuousLinearMap Lφ).contDiff
  intro g₀ hg₀
  have hmem : ∀ g ∈ Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS, t * g * t' ∈ Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS := fun g hg =>
    Formalism.L2.SG.RealObj.EnergyIntTor.UH_mul (Formalism.L2.SG.RealObj.EnergyIntTor.UH_mul
      (Formalism.L2.SG.RealObj.EnergyIntTor.tor_mem_UH hμ) hg) (Formalism.L2.SG.RealObj.EnergyIntTor.tor_mem_UH (inv_ne_zero hμ))
  obtain ⟨U, F, hU, h0, hF, hE⟩ := hcf _ (hmem g₀ hg₀)
  refine ⟨(fun g => t * g * t') ⁻¹' U, fun g => cc j • F (t * g * t'), hU.preimage hφ.continuous, h0, ?_, ?_⟩
  · exact (hF.comp (hφ.of_le le_top).contDiffOn (fun g hg => hg)).const_smul (cc j)
  · intro g hgU hgG
    rw [hfun g, hE _ hgU (hmem g hgG)]

end Formalism.L2.SG.Pf.CarrierXAll

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.L2.SG.Pf.Carrier.CarPinVt

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem host_v (D : D7) : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2 := by
  unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
  rw [Int.cast_abs, one_div]

theorem gapOK_mono {k r : ℕ} {h h' : ℝ} (hg : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hh : h ≤ h') : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h' := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r h ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h' := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    exact div_le_div_of_nonneg_right hh (by positivity)
  exact ⟨h1, by linarith, by linarith, by linarith⟩

def XLeafAt {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ)
    (de de' : ℕ → ℝ) (l : ℕ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ) : Prop :=
  (∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (a j)) ∧
  (∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) ∧
  ∀ (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ),
    Formalism.L2.SG.Pf.Carrier.JointPin.PinCov (CarrierOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)))

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.L2.SG.Pf.Carrier.CarPinVt

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def Cd : ℝ := exists_Cc_data.choose

def LiftAt3 (Cb : ℝ) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : Formalism.FourierDecayAlt.M.Par)
    (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) (X : Formalism.FourierDecayAlt.Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt P.k P.r))
    (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ), 1 ≤ l0 → l0 ≤ P.k →
    Formalism.FourierDecayAlt.P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 →
      ∃ Θ : Formalism.FourierDecayAlt.Top.TopLift P.k P.r Wp Wq, Formalism.FourierDecayAlt.KB.IsTopLift2 P l0 Bs L st Θ ∧ Formalism.FourierDecayAlt.KB.InDDplus2 P l0 Bs Cb Θ

theorem lift_compact_test_towers (Cb : ℝ) (hL : LiftAt3 Cb) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)
    (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (de de' : ℕ → ℝ) (l : ℕ) (hl2 : l + 2 ≤ D.R.k)
    (hdat : ∀ j : Fin (nfE D),
      ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
        (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
        (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
        (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
        Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1)) :
    ∃ Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)),
      (∀ j : Fin (nfE D),
        ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
            (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
          (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
          (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
            (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
          (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
            (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
          Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
            (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
          Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st (Θ j)) ∧
      ∀ j : Fin (nfE D),
        Formalism.FourierDecayAlt.KB.InDDplus2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base Cb (Θ j) := by
  have key : ∀ j : Fin (nfE D), ∃ Θj : Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)),
      (∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
            (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
          (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
          (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
            (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
          (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
            (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
          Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
            (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
          Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st Θj) ∧
        Formalism.FourierDecayAlt.KB.InDDplus2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base Cb Θj := by
    intro j
    obtain ⟨Xo, μ, L, st, hD⟩ := hdat j
    obtain ⟨Θj, h1, h2⟩ := hL _ _ (parE e u u' de de' j) (towersOf X C u u' e j).base Xo μ L st (l + 1) (by omega)
      (show l + 1 ≤ D.R.k by omega) hD
    exact ⟨Θj, ⟨Xo, μ, L, st, hD, h1⟩, h2⟩
  choose Θ hΘ using key
  exact ⟨Θ, fun j => (hΘ j).1, fun j => (hΘ j).2⟩

theorem liftAt3_exists : ∃ Cb : ℝ, LiftAt3 Cb := by
  obtain ⟨Cb, -, h⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  exact ⟨Cb, h⟩

def liftId {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] : Formalism.FourierDecayAlt.Top.TopLift k r Wp Wq where
  Θ _ _ F := F
  nil _ _ := rfl

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in

theorem carrierDataBuilt_of_hyp (Cb : ℝ) (hLift : LiftAt3 Cb) (hCap : CapFromHC) {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ}
    (hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl1000 : 1000 ≤ Cl) (hk18 : 1801 ≤ D.R.k) (Cc C₆ : ℝ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (hleaf : XLeafAt X C u u' e he (host_v D) CA de de' l i0 i0' sc FdN FdN' νq jn a b ξ ξ' cc)
    (h5 : ∀ (w : D.what₂.Word) τ, ¬ IsTop D τ → uOne D w τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (hde : de = Formalism.MainNotions.BridgeLemma.deOf D u) (hde' : de' = Formalism.MainNotions.BridgeLemma.deOf D u')
    (hOk : ∀ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).Ok)
    (hw : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de') (hl1 : 1 ≤ l) (hl2 : l + 2 ≤ D.R.k)
    (hne : de l ≠ de' l)
    (hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤ (D.s.Del : ℝ) / 2 - 5 / 2)
    (hLc : Cc * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2)
    (hLd : Cd * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2)
    (hC6 : C₆ * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ (D.s.Del : ℝ) / 2 - 5 / 2)
    (hCA : Cc ≤ CA) (hCAd : Cd ≤ CA)
    (hLe : Ce * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2)
    (hC6e : fourierDecayLevelZeroConst * ((D.R.k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ (D.s.Del : ℝ) / 2 - 5 / 2)
    (hCAe : Ce ≤ CA)
    (h : ℝ) (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) (hAh : decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS ≤ h / 2)
    (hi : ∀ v, i0 v = i0' v) (hPRE : PtRepExists X u u' sc i0 i0') (hsc : 0 < sc) (hNu : NuQPin X u u' νq)
    (hE2 : ∀ (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
      (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
        (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ),
      Formalism.FourierDecayAlt.D.IsBuilt (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE X C u' e i0') (m0E X C u u' e) (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀ →
      (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
        Formalism.FourierDecayAlt.D.GamLev (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.D.deG (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) = jn) :
    CarrierDataBound X u u' sc i0 i0' FdN FdN' νq jn CA (Formalism.L2.SG.SpectralTiesReal.gOf D e) de de' l C₆ Cc Cb := by
  obtain ⟨hka, hkb, hrest⟩ := hleaf
  have hsm := fun j => fcT_smooth X C e u u' a b ξ ξ' cc j (hkb j)
  have hN := parNumsE_of (D := D) u u' e de de' h5 hde hde'
  have hty := typesE_of X C hCap u u' e de de' h5 hde hde'
  set TP := tpOf X C Formalism.FourierDecayAlt.P.type_projectors_exist u u' e de de' i0' hN hty with hTPdef
  set Θ0 : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)) :=
    fun _ => liftId with hΘ0
  set A₀ := decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS with hA₀
  have hA0 : 0 ≤ A₀ := by
    rw [hA₀]; unfold decayThreshold; positivity
  have hCC : |Cc| ≤ |Cc| + |Cd| + |Ce| := by have := abs_nonneg Cd; have := abs_nonneg Ce; linarith
  have hCD : |Cd| ≤ |Cc| + |Cd| + |Ce| := by have := abs_nonneg Cc; have := abs_nonneg Ce; linarith
  have hCE : |Ce| ≤ |Cc| + |Cd| + |Ce| := by have := abs_nonneg Cc; have := abs_nonneg Cd; linarith
  have thr : ∀ c : ℝ, |c| ≤ |Cc| + |Cd| + |Ce| →
      c * ((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤ A₀ := by
    intro c hc
    have h1 := poly_le_decayThreshold (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP (decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS))) (|Cc| + |Cd| + |Ce|)
    have hP : 0 ≤ ((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) := by
      positivity
    have h2 : c * ((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤
        (|Cc| + |Cd| + |Ce|) * ((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) := by
      calc c * ((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3)
          = c * (((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3)) := by ring
        _ ≤ (|Cc| + |Cd| + |Ce|) * (((D.R.rS : ℝ) + 1) ^ 4 * (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 + (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3)) := mul_le_mul_of_nonneg_right ((le_abs_self c).trans hc) hP
        _ = _ := by ring
    exact h2.trans h1
  have hcc0 : CoefCC (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP (decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS)) :=
    Formalism.L2.SG.Pf.CoefCCT.coefCC_carrierInTc C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) a b ξ ξ' cc cutStd
      (nuE X C u' e i0') (m0E X C u u' e) Θ0 TP A₀ (fun _ => h) (fun _ => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _) hgap
      (fun _ => hok) hA0 (fun _ => hAh) hka hkb
  have hLd' : Formalism.FourierDecayAlt.JCT.LongCut Cd (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP (decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS))) :=
    fun v => le_of_le_of_eq hLd (cut_len (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP (decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS)) v).symm
  have hBold := isBuiltPlace_carrierInT X C Cd u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l)
    (fcT X C e u u' a b ξ ξ' cc) cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ0 TP A₀ hN hty
    (frames_carrierInT X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0'
      Θ0 TP A₀) hcc0 (coefCap_ITc X C hS0 hCl1000 hk18 u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) a b ξ ξ' cc cutStd
      i0' Θ0 TP A₀ hkb) hw hw' hl1 hl2 hne
    (gridsOK_ITc X C u u' e he (host_v D) CA de de' l (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ0 TP A₀ hlen hOk hl2)
    hLd' hCAd hsm (thr Cd hCD)
  have hdata := exists_Cc_data.choose_spec X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l)
    (fcT X C e u u' a b ξ ξ' cc) cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ0 TP A₀ hBold
  obtain ⟨Θ, hΘ, hDD⟩ := lift_compact_test_towers Cb hLift X C u u' e de de' l hl2 hdata
  have hpin := hrest Θ TP A₀
  have hcap := coefCap_ITc X C hS0 hCl1000 hk18 u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) a b ξ ξ' cc cutStd
    i0' Θ TP A₀ hkb
  have hW := wtTie_carrierInT X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc)
    cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀
  have hJT := fun hBuilt => jointTensor_compact_test X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l)
    (fcT X C e u u' a b ξ ξ' cc) cutStd i0 i0' hi Θ TP A₀ sc νq hNu hpin hsc hBuilt
  have hLz := lZero_of_choice X C u u' sc i0 i0' FdN FdN' νq
  have hPt := ptSome_of (sOf (ITc X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP (decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS))) rfl
  have hRz := rZero_carrierInT X C u u' e he (host_v D) CA de de' l (gridT e l) (grid1T e l) (fcT X C e u u' a b ξ ξ' cc) cutStd
    (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ sc i0 i0' hPRE
  exact carrierDataBuilt_of_towers X C Cb Cc C₆ u u' e he (host_v D) CA de de' l i0 i0' sc FdN FdN' νq jn a b ξ ξ' cc Θ TP A₀
    hN hty hl2 hΘ hDD hOk hw hw' hl1 hne hlen hLc hC6 hCA (thr Cc hCC) (sliceBudget_decayThreshold _ _) h hgap hok hA0 hAh hka hkb hsm
    hcap hJT hsc hPt hW hLz hRz (hE2 Θ TP A₀) hLe hC6e hCAe (thr Ce hCE) hi

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem polys (k r : ℕ) :
    (k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) * ((r : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 +
        ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) ^ 3 ≤ 8400 * ((k : ℝ) * ((r : ℝ) + 1) ^ 3 + ((r : ℝ) + 1) ^ 4) ∧
    (k : ℝ) * ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) * ((r : ℝ) + 1) ^ 2 + ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 ≤
        8400 * ((k : ℝ) * ((r : ℝ) + 1) ^ 3 + ((r : ℝ) + 1) ^ 4) ∧
    6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) ≤ 48120 * ((k : ℝ) * ((r : ℝ) + 1) ^ 3 + ((r : ℝ) + 1) ^ 4) := by
  have hN : ((4 * Formalism.FourierDecayAlt.C.Kst * (r + 1) : ℕ) : ℝ) = 20 * ((r : ℝ) + 1) := by
    unfold Formalism.FourierDecayAlt.C.Kst; push_cast; ring
  rw [hN]
  set x : ℝ := (r : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; have := (Nat.cast_nonneg r : (0 : ℝ) ≤ r); linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h34 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have h14 : x ≤ x ^ 4 := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hkx : 0 ≤ (k : ℝ) * x ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have e : (k : ℝ) * (20 * x) * x ^ 2 + (20 * x) ^ 2 * x ^ 2 + (20 * x) ^ 3 = 20 * ((k : ℝ) * x ^ 3) + 400 * x ^ 4 + 8000 * x ^ 3 := by ring
    rw [e]; nlinarith
  · have e : (k : ℝ) * (20 * x) * x ^ 2 + (20 * x) ^ 2 * x ^ 2 = 20 * ((k : ℝ) * x ^ 3) + 400 * x ^ 4 := by ring
    rw [e]; nlinarith
  · have e : 6 * (20 * x) ^ 3 + 6 * (20 * x) = 48000 * x ^ 3 + 120 * x := by ring
    rw [e]; nlinarith

theorem scale_le {c P Q B : ℝ} (hP0 : 0 ≤ P) (hP : P ≤ 8400 * Q) (hB : 8400 * |c| * Q ≤ B) : c * P ≤ B := by
  have h1 : c * P ≤ |c| * P := mul_le_mul_of_nonneg_right (le_abs_self c) hP0
  have h2 : |c| * P ≤ |c| * (8400 * Q) := mul_le_mul_of_nonneg_left hP (abs_nonneg c)
  linarith

end Formalism.L2.SG.Pf.CarrierXAll

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

end Formalism.L2.SG.Pf.CarrierXAll

namespace Formalism.L2.SG.Pf.CarrierXAll

def CSTarget : Prop :=
  Formalism.FourierDecayAlt.P5.ThmPActual ∧ Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 ∧ Formalism.FourierDecayAlt.KB.BuiltBounds2

end Formalism.L2.SG.Pf.CarrierXAll

namespace Formalism.L2.SG.Pf.CarrierXAll

def CSTarget4 : Prop :=
  Formalism.FourierDecayAlt.P5.ThmPActualCpt ∧ Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 ∧ Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt

end Formalism.L2.SG.Pf.CarrierXAll
end
end
end
end
end
end
end
end
end
