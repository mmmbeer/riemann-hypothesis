import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FrameOpFull
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvertibleIdealIndex.SubmodulePiToAddSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsTies

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ThrS

end ThrS

section Point

variable {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (hCT : ConcTie X Y)

def wOf : WittDat X := Classical.choice (Formalism.L2.SG.Pf.WittFlags.WittExists_holds D X)

theorem hOf : TieHyp (wOf X) hI :=
  { lat := Formalism.L2.SG.Pf.WittFlags.LatIso_holds D
    idG := fun u u' => identityCell_vanishes u u'
    atSome := fun u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds _ _ Y u u'
    autFin := fun u => Formalism.L2.SG.Pf.autFin_of (automorphism_lattice_finite D) (D.sp.Y_sig 0)
      (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D ((wOf X).δ u) ((wOf X).isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u))
    dim := fun u => Formalism.L2.SG.Pf.dimTie X u
    pairs := Formalism.L2.SG.Pf.pairTiesAll_holds _ _ Y hF (wOf X) hI }

def aOf : AmpDat X := Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hCT.2.2.2.2.1)

theorem hvOf : PvalForm (wOf X) hI (aOf X Y hF hI hCT) :=
  Classical.choose_spec (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hCT.2.2.2.2.1)

def atOf : TermTie D := termTieOf (wOf X) hI (hOf X Y hF hI) (aOf X Y hF hI hCT) (hvOf X Y hF hI hCT)

def ccOf : ConcAt0 D (atOf X Y hF hI hCT) :=
  ⟨X, Y, hF, hI,
    jtPin_of (wOf X) hI (hOf X Y hF hI) (aOf X Y hF hI hCT) (hvOf X Y hF hI hCT) (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI (wOf X) (hOf X Y hF hI) (aOf X Y hF hI hCT) (hvOf X Y hF hI hCT),
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y⟩

end Point

section PointW

variable {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
  (hWD : Formalism.L2.SG.WuDecay.WuDecay X)

def aOfW : AmpDat X := Classical.choose (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hWD)

theorem hvOfW : PvalForm (wOf X) hI (aOfW X Y hF hI hWD) :=
  Classical.choose_spec (Formalism.L2.SG.Pf.KernelOfEmbedding.pvalForm_holds (wOf X) hI hWD)

def atOfW : TermTie D := termTieOf (wOf X) hI (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD)

def ccOfW : ConcAt0 D (atOfW X Y hF hI hWD) :=
  ⟨X, Y, hF, hI,
    jtPin_of (wOf X) hI (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD)
      (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD),
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y⟩

end PointW

end Formalism.L2.SG.LoopsTies
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SelQ

variable {𝒞 : FamClass} (sel : SSel 𝒞)

def QS {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : Prop :=
  ∃ h0 : (sel Fm hc).1 ≤ x, ∃ _ : FinX ((sel Fm hc).2 x hx h0 i).Y,
    ConcTie ((sel Fm hc).2 x hx h0 i).X ((sel Fm hc).2 x hx h0 i).Y

variable {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm)

end SelQ

section Closed

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)

theorem cOut_take {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := by
  unfold FamP.cOut; simp

theorem constant_list_cylinder {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 6 0 = Fm.CYL := by
  unfold FamP.cOut; simp

theorem constant_list_trace {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 13 0 = Fm.CTu := by
  unfold FamP.cOut; simp

end Closed

section Raised

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞)
  (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YFOK : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x), yF Fm hc ≤ x →
    ∀ i : Fm.Ix x, FinX ((sel Fm hc).2 x hx h0 i).Y ∧ Formalism.L2.SG.WuDecay.WuDecay ((sel Fm hc).2 x hx h0 i).X

def yR {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) : ℝ := max (sel Fm hc).1 (yF Fm hc)

theorem h0R {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    (sel Fm hc).1 ≤ x :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans hx.le

theorem hyR {eps : ℝ} {Fm : FamP eps} {hc : 𝒞 Fm} {x : ℝ} (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) :
    yF Fm hc ≤ x :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans hx.le

def AtR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : TermTie (Fm.D x i) :=
  atOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

def CcR (hyF : YFOK sel yF) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x)
    (i : Fm.Ix x) : ConcAt0 (Fm.D x i) (AtR sel yF hyF Fm hc x hx i) :=
  ccOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1
    (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
    (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loopRowS_of_raised (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (C₀f : (List ℝ → ℝ) → List ℝ → ℝ)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hRowsF : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm, ∀ C : ℝ, C₀f aF (Fm.cOut ++ Fm.cMid CH) ≤ C →
      OwnEv Fm fun C' Cl x i => ∀ (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
          Formalism.MainNotions.BridgeLemma.RowsND (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsDeg (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u') C)
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  intro aF
  choose f g hfg using fun p : ℝ × ℝ × ℝ × ℝ =>
    loop_evaluation_threshold_zero Formalism.FourierDecayAlt.P.loop_kernels Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.HermitianLattices.Ext.L3.siegelMassRatio
      (p.1 + 1) (1 / 4) 3 (1 / 2) p.2.1 C0 p.2.2.1 p.2.2.2
  let par : List ℝ → ℝ × ℝ × ℝ × ℝ := fun l => (l.getD 6 0, l.getD 13 0, aF (l.take 16), C₀f aF l)
  obtain ⟨e1, he1, H1⟩ := hRowsF aF
  obtain ⟨e2, he2, H2⟩ := hForm
  refine ⟨min e1 e2, lt_min he1 he2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := H1 eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := H2 eps he (hle.trans (min_le_right _ _))
  let K4 : TransportedAlt := ⟨0, fun _ => 0, fun _ => 0, fun l => max (f (par l)) (g (par l))⟩
  refine ⟨(K1.sup K2).sup K4, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL12, hL4⟩ := (Fm.large_sup _ _ CH).1 hL
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL12
  intro hc'
  have epar : par (Fm.cOut ++ Fm.cMid CH) = (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) := by
    simp only [par, constant_list_cylinder, constant_list_trace, cOut_take]
  have hthr : ∀ c ∈ Fm.cLast, max (f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)))
      (g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH))) ≤ c := by
    intro c hc0
    have := hL4.2.2.2 c hc0
    simpa only [K4, epar] using this
  have hC' : f (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sC' Fm :=
    (le_max_left _ _).trans (hthr _ (by unfold FamP.cLast sC'; simp))
  have hCl : g (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) ≤ sCl Fm := by
    have h := fun c hc => (le_max_right _ _).trans (hthr c hc)
    unfold sCl
    refine le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
      (le_min (h _ (by unfold FamP.cLast; simp)) (le_min (h _ (by unfold FamP.cLast; simp))
        (le_min (h _ (by unfold FamP.cLast; simp)) (h _ (by unfold FamP.cLast; simp))))))
  have hE := hfg (Fm.CYL, Fm.CTu, aF Fm.cOut, C₀f aF (Fm.cOut ++ Fm.cMid CH)) (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut)
    (AtR sel yF hyF Fm hc') (Yt Fm hc') (CcR sel yF hyF Fm hc') (hK1 Fm CH hc hL1 hc') (hK2 Fm CH hc hL2)
  obtain ⟨x0, H⟩ := hE
  refine ⟨max x0 (yR sel yF Fm hc' + 1), fun x hx0 i => ?_⟩
  intro hx h0 u u' hH hCT hA
  have hx' : (Fm.raise (yR sel yF Fm hc')).x1 < x := by
    show max Fm.x1 (yR sel yF Fm hc') < x
    refine max_lt hx ?_
    have := (le_max_right _ _).trans hx0
    linarith
  exact H x ((le_max_left _ _).trans hx0) i hC' hCl hx' u u' hH hCT hA

theorem constant_list_gamma {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := by
  unfold FamP.cOut FamP.cMid; simp

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loopRowS_of_U (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (Uf : (List ℝ → ℝ) → List ℝ → Formalism.L2.SG.RowsU.UC)
    (Yt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut))
    (hAdmR : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm,
      VanishingOnXAndXPlus.AdmF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (Yt Fm hc))
    (hUR : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm,
      Formalism.L2.SG.RowsU.UAdm (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (Yt Fm hc)
        (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) (Uf aF (Fm.cOut ++ Fm.cMid CH)))
    (hTR : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm,
      Formalism.MainNotions.BridgeLemma₂.rows_TiesF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (Yt Fm hc) ∧
      ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (Yt Fm hc x hx i u u'))
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel := by
  refine loopRowS_of_raised C0 sel yF hyF C1f
    (fun aF l => Formalism.L2.SG.RowsU.c0U (l.getD 13 0) (aF (l.take 16)) C0 (l.getD 17 0) (Uf aF l)) Yt ?_ hForm
  intro aF
  obtain ⟨e, he, H⟩ := hAdmR.and ((hUR aF).and hTR)
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  refine ⟨K, fun Fm CH hc hL hc' C hC => ?_⟩
  obtain ⟨hA, hU, hT⟩ := hK Fm CH hc hL
  rw [constant_list_trace, cOut_take, constant_list_gamma] at hC
  exact Formalism.L2.SG.RowsU.rowsFU (Fm.raise (yR sel yF Fm hc')) (C1f Fm.cOut) (AtR sel yF hyF Fm hc') (Yt Fm hc')
    (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) (hA hc') (hT hc').1 (hT hc').2
    (fun x i => _root_.beta_l_unique (Fm.D x i)) _ (hU hc') C hC

end Raised

end Formalism.L2.SG.LoopsTies
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopsFinal

namespace Formalism.L2.SG.Pf.LoopBFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem rowLat_fl' {u u' : D.what₂.Word} (t : D.s.Term u u') :
    IsRowLat D (fl'Of W hI t).fl (lamOf W hI t) := by
  have hR := rowLat_map (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) (W.δ u) (W.isom u) (X.Fu u) _ (rowLat_tc hI t)
  have hFx := fixedC W hI (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) t
  obtain ⟨hLift, -, hOK⟩ := pdC W hI t
  exact ⟨hR.1, ⟨hFx.1, hFx.2.1, ⟨hLift.1, rfl⟩, hOK.1⟩, hOK.2⟩

theorem frameChangeAt_holds : FrameChangeAt W hI := by
  intro u u' t ξ hl hd
  obtain ⟨n, hn, hnf⟩ := Formalism.L2.S.Pv.ClassCounting.frameOpFull D u' (fl'Of W hI t).fl (lamOf W hI t) (rowLat_fl' W hI t) ξ hl hd
  exact ⟨n, hn, fun b => hnf b⟩

theorem frameChangeC_holds : FrameChangeC := fun _ _ _ _ hI W => frameChangeAt_holds W hI

end Formalism.L2.SG.Pf.LoopBFrame
end
end

section
noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.DetUU

section Gram

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

open Formalism.MainNotions.S

def uCat (F : FlagG S r T) (F' : FlagG S r T') : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim F.fvec F'.fvec

def gramCat (F : FlagG S r T) (F' : FlagG S r T') : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
  Matrix.of fun i j => S.hT (uCat F F' i) (uCat F F' j)

def lastDiag (c : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem fvec_castSucc (F : FlagG S r T) (a : Fin r) : F.fvec (Fin.castSucc a) = F.e a := by
  simp [FlagG.fvec]

theorem gram_self (F : FlagG S r T) :
    (Matrix.of fun a b => S.hT (F.fvec a) (F.fvec b)) = lastDiag (-T) := by
  ext a b
  simp only [Matrix.of_apply, lastDiag]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [fvec_last, F.z_norm]; simp
    | cast b =>
      rw [fvec_last, fvec_castSucc]
      have h1 := S.herm.eq (F.e b) F.z
      rw [F.z_orth b, map_zero] at h1
      rw [← h1]
      simp [Fin.castSucc_ne_last]
  | cast a =>
    induction b using Fin.lastCases with
    | last => rw [fvec_castSucc, fvec_last, F.z_orth]; simp [Fin.castSucc_ne_last]
    | cast b => rw [fvec_castSucc, fvec_castSucc, F.e_iso]; simp [Fin.castSucc_ne_last]

theorem gramCat_eq (F : FlagG S r T) (F' : FlagG S r T') :
    gramCat F F' = Matrix.fromBlocks (lastDiag (-T)) (Zhat F F') (Zhat F F')ᴴ (lastDiag (-T')) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁]
    exact congrFun (congrFun (gram_self F) a) b
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply]
    show S.hT (F'.fvec a) (F.fvec b) = star (S.hT (F.fvec b) (F'.fvec a))
    rw [← S.herm.eq (F.fvec b) (F'.fvec a)]
    rfl
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
    exact congrFun (congrFun (gram_self F') a) b

theorem lastDiag_mul_mul (c c' : E) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    lastDiag c * X * lastDiag c' = lastDiag (c * X (Fin.last r) (Fin.last r) * c') := by
  ext a b
  simp only [lastDiag, Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem det_sub_lastDiag (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c : E) :
    (M - lastDiag c).det = M.det - c * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  have h1 : M - lastDiag c = M.updateRow (Fin.last r) (M (Fin.last r) - c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb
        simp [lastDiag]
      · simp [lastDiag, hb, Pi.single_apply]
    · simp [lastDiag, Matrix.updateRow_ne ha, ha]
  rw [h1, sub_eq_add_neg (M (Fin.last r)), ← neg_smul, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, neg_mul, ← sub_eq_add_neg]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · simp [Matrix.updateRow_self, Fin.succAbove_last]
    congr 1
    ext a b
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]
  · intro j _ hj
    simp [Matrix.updateRow_self, Pi.single_apply, hj]
  · simp

theorem leadMinor_full (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : leadMinorE B (r + 1) = B.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  congr 1

theorem leadMinor_r (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE B r = (B.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  rfl

theorem gram_det_eq (F : FlagG S r T) (F' : FlagG S r T') (hB : (Zhat F F').det ≠ 0) :
    ∃ s : E, s * s = 1 ∧ (gramCat F F').det = s * Gflag F F' := by
  set B := Zhat F F' with hBdef
  letI : Invertible B := invertibleOfIsUnitDet B (isUnit_iff_ne_zero.2 hB)
  set P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E := Matrix.fromBlocks 0 1 1 0 with hP
  have hPP : P * P = 1 := by
    rw [hP, Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have hs : P.det * P.det = 1 := by rw [← det_mul, hPP, det_one]
  have hsw : gramCat F F' * P = Matrix.fromBlocks B (lastDiag (-T)) (lastDiag (-T')) Bᴴ := by
    rw [gramCat_eq, hP, Matrix.fromBlocks_multiply]; simp [hBdef]
  have h1 := congrArg Matrix.det hsw
  rw [det_mul, det_fromBlocks₁₁ B (lastDiag (-T)) (lastDiag (-T')) Bᴴ] at h1
  have hm : lastDiag (-T') * ⅟B * lastDiag (-T) = lastDiag ((-T') * (⅟B) (Fin.last r) (Fin.last r) * (-T)) :=
    lastDiag_mul_mul _ _ _
  rw [hm, det_sub_lastDiag, det_conjTranspose] at h1
  have hsub : (Bᴴ.submatrix Fin.castSucc Fin.castSucc) = (B.submatrix Fin.castSucc Fin.castSucc)ᴴ := by
    ext a b; simp
  rw [hsub, det_conjTranspose] at h1
  have hinv : (⅟B) (Fin.last r) (Fin.last r) = B.det⁻¹ * (B.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [invOf_eq_nonsing_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
      adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.succAbove_last, Fin.val_last, smul_eq_mul]
    rw [← two_mul, pow_mul]
    norm_num
  rw [hinv] at h1
  refine ⟨P.det, hs, ?_⟩
  have key : (gramCat F F').det = P.det * (B.det * (star B.det - (-T') * (B.det⁻¹ *
      (B.submatrix Fin.castSucc Fin.castSucc).det) * (-T) * star (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
    calc (gramCat F F').det = (gramCat F F').det * (P.det * P.det) := by rw [hs, mul_one]
      _ = P.det * ((gramCat F F').det * P.det) := by ring
      _ = _ := by rw [h1]
  rw [key]
  unfold Gflag Dl
  rw [← hBdef, leadMinor_full, leadMinor_r]
  field_simp

end Gram

section Conc

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsTies Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def pseudoLat {ι : Type} (u : ι → (hS D).V) (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) (hS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ j, ∃ x ∈ I j, y = x • u j}

def GenIdxPseudo : Prop :=
  ∀ (D : D7) (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → (hS D).V)
    (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
    LinearIndependent D.host.E u → (∀ j, I j ≠ 0) → (∀ j, ∀ x ∈ I j, star x ∈ I j) →
    (Matrix.of fun i j => (hS D).hT (u i) (u j)).det ≠ 0 →
    genIdx (hS D) (dualIn (hS D) (pseudoLat u I)) (pseudoLat u I) =
      |((Algebra.norm ℚ (Matrix.of fun i j => (hS D).hT (u i) (u j)).det : ℚ) : ℝ)| *
        ∏ j, ((FractionalIdeal.absNorm (I j) : ℚ) : ℝ) ^ 2

def aaF (D : D7) (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  if (a : ℕ) < D.R.rS then ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) else 1

theorem aaF_castSucc (a : Fin D.R.rS) : aaF D (Fin.castSucc a) = ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) := by
  unfold aaF
  rw [if_pos (by simp)]
  simp

theorem aaF_last : aaF D (Fin.last D.R.rS) = 1 := by
  unfold aaF
  rw [if_neg (by simp)]

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
  exact differentIdeal_ne_bot

theorem aaF_ne_zero (a : Fin (D.R.rS + 1)) : aaF D a ≠ 0 := by
  unfold aaF
  split_ifs
  · exact zpow_ne_zero _ ddS_ne_zero
  · exact one_ne_zero

theorem aaF_star (a : Fin (D.R.rS + 1)) : ∀ x ∈ aaF D a, star x ∈ aaF D a := by
  intro x hx
  unfold aaF at hx ⊢
  split_ifs at hx ⊢ with h
  · have ha : (a : ℕ) ≤ D.R.rS := h.le
    have e : ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) =
        (((dI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
      rw [show (-((D.R.rS : ℤ) - (a : ℕ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℤ)) by push_cast [Nat.cast_sub ha]; ring,
        _root_.zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
      rfl
    rw [e] at hx ⊢
    exact star_mem_inv _ hx
  · obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    obtain ⟨o', ho'⟩ := star_int o
    exact (FractionalIdeal.mem_one_iff _).2 ⟨o', by rw [← ho']⟩

theorem uu_eq (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)
    (F' : LFlag (hS D) D.R.rS T') (hX : XLam Λ F = XS D F.fl) (hX' : XLam Λ F' = XS D F'.fl)
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    UU Λ F F' = pseudoLat (DetUU.uCat F.fl F'.fl) (Sum.elim (aaF D) (aaF D)) := by
  unfold UU
  rw [hX, hX', hz, hz']
  apply le_antisymm
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl (Fin.castSucc a), x, ?_, ?_⟩
      · simpa [aaF_castSucc] using hx
      · simp [DetUU.uCat, DetUU.fvec_castSucc]
    · refine Submodule.span_le.2 ?_
      rintro _ rfl
      refine Submodule.subset_span ⟨Sum.inl (Fin.last _), 1, ?_, ?_⟩
      · simp only [Sum.elim_inl, aaF_last]; exact FractionalIdeal.one_mem_one _
      · simp [DetUU.uCat, DetUU.fvec_last]
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      refine Submodule.subset_span ⟨Sum.inr (Fin.castSucc a), x, ?_, ?_⟩
      · simpa [aaF_castSucc] using hx
      · simp [DetUU.uCat, DetUU.fvec_castSucc]
    · refine Submodule.span_le.2 ?_
      rintro _ rfl
      refine Submodule.subset_span ⟨Sum.inr (Fin.last _), 1, ?_, ?_⟩
      · simp only [Sum.elim_inr, aaF_last]; exact FractionalIdeal.one_mem_one _
      · simp [DetUU.uCat, DetUU.fvec_last]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, x, hx, rfl⟩
    rcases j with a | a
    · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
      · simp only [Sum.elim_inl, aaF_castSucc] at hx
        simp only [DetUU.uCat, Sum.elim_inl, DetUU.fvec_castSucc]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.subset_span ⟨a', x, hx, rfl⟩)))
      · simp only [Sum.elim_inl, aaF_last] at hx
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
        simp only [DetUU.uCat, Sum.elim_inl, DetUU.fvec_last]
        rw [algebraMap_smul]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))))
    · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
      · simp only [Sum.elim_inr, aaF_castSucc] at hx
        simp only [DetUU.uCat, Sum.elim_inr, DetUU.fvec_castSucc]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a', x, hx, rfl⟩))
      · simp only [Sum.elim_inr, aaF_last] at hx
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
        simp only [DetUU.uCat, Sum.elim_inr, DetUU.fvec_last]
        rw [algebraMap_smul]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))

theorem uCat_indep {T T' : D.host.E} (F : FlagG (hS D) D.R.rS T) (F' : FlagG (hS D) D.R.rS T')
    (h : (DetUU.gramCat F F').det ≠ 0) : LinearIndependent D.host.E (DetUU.uCat F F') := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hG : (DetUU.gramCat F F').mulVec c = 0 := by
    funext k
    have h1 := congrArg (fun v => (hS D).hT (DetUU.uCat F F' k) v) hc
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h1
    simp only [DetUU.gramCat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero h hG) i

end Conc

section Final

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsTies Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sum_sub_eq_frameExp : ∑ a : Fin D.R.rS, (D.R.rS - (a : ℕ)) = frameExp D.R.rS D.R.rS := by
  rw [Fin.sum_univ_eq_sum_range (fun a => D.R.rS - a), frameExp]
  have key : ∀ n r : ℕ, ∑ a ∈ Finset.range n, (r - a) = ∑ a ∈ Finset.Icc 1 n, (r + 1 - a) := by
    intro n r
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      congr 1
      omega
  exact key _ _

theorem prod_absNorm_aaF :
    ∏ a : Fin (D.R.rS + 1), ((FractionalIdeal.absNorm (aaF D a) : ℚ) : ℝ) =
      (((D.host.rdE ^ D.R.f) ^ 2)⁻¹) ^ frameExp D.R.rS D.R.rS := by
  have hN : ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := by
    show ((FractionalIdeal.absNorm ((dI D : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℚ) : ℝ) = _
    rw [FractionalIdeal.coeIdeal_absNorm, ← absNorm_dI]
    push_cast; rfl
  rw [Fin.prod_univ_castSucc, aaF_last, map_one, Rat.cast_one, mul_one]
  have e : ∀ a : Fin D.R.rS, ((FractionalIdeal.absNorm (aaF D (Fin.castSucc a)) : ℚ) : ℝ) =
      (((D.host.rdE ^ D.R.f) ^ 2)⁻¹) ^ (D.R.rS - (a : ℕ)) := by
    intro a
    have ha : (a : ℕ) ≤ D.R.rS := a.isLt.le
    rw [aaF_castSucc, show (-((D.R.rS : ℤ) - (a : ℕ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℤ)) by
      push_cast [Nat.cast_sub ha]; ring, _root_.zpow_neg, zpow_natCast, map_inv₀, map_pow]
    push_cast
    rw [hN, inv_pow]
  rw [Finset.prod_congr rfl fun a _ => e a, Finset.prod_pow_eq_pow_sum, sum_sub_eq_frameExp]

theorem embS_gval_real (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) :
    embS D τ (Gval (T.fl t) (T.fl' t)) = (((embS D τ (Gval (T.fl t) (T.fl' t))).re : ℝ) : ℂ) := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, Formalism.MainNotions.S.Pv.HH.embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (T.fl t) (T.fl' t)) =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (T.fl t) (T.fl' t)) (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (T.fl t) (T.fl' t)) D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (T.fl t).fl (T.fl' t).fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.ofReal_re]

theorem detUUC_of (hGI : GenIdxPseudo) : DetUUC := by
  intro D X Y hF hI W H A hV u u' t hG
  set T := termTieOf W hI H A hV with hTdef
  have hX : XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl :=
    ((Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D (W.δ u) (W.isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u)).1 _
      (lamOf_mem W hI t)).2.2
  have hX' : XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl := (pdC W hI t).2.2.2
  have hz : (T.fl t).zt = (T.fl t).fl.z := (T.fixed t).2.2.1.2
  have hz' : (T.fl' t).zt = (T.fl' t).fl.z := (T.lift' t).2
  have hD1 : (Zhat (T.fl t).fl (T.fl' t).fl).det ≠ 0 := by
    have h := (Formalism.MainNotions.BridgeLemma.GDr_of_tie T u u' t hG).1
    unfold Dl at h
    rwa [leadMinor_full] at h
  obtain ⟨s, hs, hdet⟩ := gram_det_eq (T.fl t).fl (T.fl' t).fl hD1
  have hGv : Gval (T.fl t) (T.fl' t) ≠ 0 := Formalism.MainNotions.BridgeLemma.tie_Gval_ne T t hG
  have hs0 : s ≠ 0 := left_ne_zero_of_mul_eq_one hs
  have hdet0 : (gramCat (T.fl t).fl (T.fl' t).fl).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hs0 hGv
  have hgi := hGI D (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (uCat (T.fl t).fl (T.fl' t).fl)
    (Sum.elim (aaF D) (aaF D)) (uCat_indep _ _ hdet0) (by rintro (a | a) <;> exact aaF_ne_zero a)
    (by rintro (a | a) <;> exact aaF_star a) hdet0
  have hdet' : (Matrix.of fun i j => (hS D).hT (uCat (T.fl t).fl (T.fl' t).fl i)
      (uCat (T.fl t).fl (T.fl' t).fl j)).det = s * Gval (T.fl t) (T.fl' t) := hdet
  rw [hdet'] at hgi
  have hNs : |(Algebra.norm ℚ s : ℚ)| = 1 := by
    have h1 := congrArg (Algebra.norm ℚ) hs
    rw [map_mul, map_one] at h1
    have h2 : |(Algebra.norm ℚ s : ℚ)| * |(Algebra.norm ℚ s : ℚ)| = 1 := by rw [← abs_mul, h1, abs_one]
    nlinarith [abs_nonneg (Algebra.norm ℚ s : ℚ)]

  have hL : NG (T.abelian₂ t) (T.fl t) (T.fl' t) =
      Real.sqrt (|((Algebra.norm ℚ (Gval (T.fl t) (T.fl' t)) : ℚ) : ℝ)|) *
        ((((D.host.rdE ^ D.R.f) ^ 2)⁻¹) ^ frameExp D.R.rS D.R.rS) ^ 2 := by
    show Real.sqrt (genIdx (hS D) (dualIn (hS D) (UU (T.abelian₂ t) (T.fl t) (T.fl' t))) (UU (T.abelian₂ t) (T.fl t) (T.fl' t))) = _
    rw [uu_eq (T.abelian₂ t) (T.fl t) (T.fl' t) hX hX' hz hz', hgi, map_mul, Rat.cast_mul, abs_mul,
      show |((Algebra.norm ℚ s : ℚ) : ℝ)| = 1 by rw [← Rat.cast_abs, hNs, Rat.cast_one], one_mul,
      Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_pow, prod_absNorm_aaF, ← mul_pow, Real.sqrt_mul (abs_nonneg _),
      Real.sqrt_sq (by positivity)]
    ring

  have hpos : ∀ τ, 0 < (embS D τ (Gval (T.fl t) (T.fl' t))).re := fun τ =>
    Formalism.MainNotions.BridgeLemma.tie_G_pos T t hG (embS D τ)
  have hnorm : ∀ τ, ‖embS D τ (Gval (T.fl t) (T.fl' t))‖ = (embS D τ (Gval (T.fl t) (T.fl' t))).re := by
    intro τ
    rw [embS_gval_real T t τ, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_pos (hpos τ)]
  have hprod : ∏ τ, (embS D τ (Gval (T.fl t) (T.fl' t))).re =
      Real.sqrt (|((Algebra.norm ℚ (Gval (T.fl t) (T.fl' t)) : ℚ) : ℝ)|) := by
    have h := Formalism.L2.SG.WConst.prod_normSq_embS D (Gval (T.fl t) (T.fl' t))
    rw [← Finset.prod_congr rfl fun τ _ => hnorm τ, ← Rat.cast_abs, ← h, Finset.prod_pow,
      Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
  have hrd := rd_pos (D := D)
  have hW : Formalism.MainNotions.S.Pv.HH.wG D ^ 2 = ((D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS)) ^ 2)⁻¹ := by
    unfold Formalism.MainNotions.S.Pv.HH.wG
    have e : (2 * (frameExp D.R.rS D.R.rS : ℝ)) = ((2 * frameExp D.R.rS D.R.rS : ℕ) : ℝ) := by push_cast; ring
    rw [e, rpow_negNat hrd, inv_pow]
  rw [hL, Finset.prod_congr rfl fun τ _ => gz_eq T t τ, Finset.prod_mul_distrib, hprod, Finset.prod_const,
    Finset.card_univ, D.what₂.card_Tau, hW]
  congr 1
  rw [inv_pow, inv_pow]
  congr 1
  simp only [← pow_mul]
  ring_nf

theorem gram_determinant_of_generic_index (hGI : GenIdxPseudo) : GramDeterminantCount := gramDeterminant_of_unipotent_det (detUUC_of hGI)

end Final

end Formalism.L2.SG.DetUU
end
end

section
noncomputable section

open scoped Classical nonZeroDivisors Pointwise
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.Pf.LoopBGenIdx

section Pi

variable {E : Type} [Field E] [NumberField E] {e : ℕ}

def piF (J : Fin e → FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin e → E) :=
  Submodule.pi Set.univ (fun j => (J j : Submodule (𝓞 E) E))

theorem mem_piF {J : Fin e → FractionalIdeal (𝓞 E)⁰ E} {c : Fin e → E} : c ∈ piF J ↔ ∀ j, c j ∈ J j := by
  simp [piF, Submodule.mem_pi]

theorem piF_mono {J K : Fin e → FractionalIdeal (𝓞 E)⁰ E} (h : ∀ j, J j ≤ K j) : piF J ≤ piF K := fun c hc => mem_piF.2 (fun j => h j (mem_piF.1 hc j))

theorem jLat_piF_one : j_Lat (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))) := by
  have hr : piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E)) =
      LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin e)) := by
    ext c
    rw [mem_piF, LinearMap.mem_range]
    constructor
    · intro h
      choose o ho using fun j => (FractionalIdeal.mem_one_iff _).1 (h j)
      exact ⟨o, funext fun j => ho j⟩
    · rintro ⟨o, rfl⟩ j
      exact (FractionalIdeal.mem_one_iff _).2 ⟨o j, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hr, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin e)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    apply Submodule.subset_span
    rw [SetLike.mem_coe, mem_piF]
    intro i
    refine (FractionalIdeal.mem_one_iff _).2 ⟨if i = j then 1 else 0, ?_⟩
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp

def diagC (a : Fin e → E) (ha : ∀ j, a j ≠ 0) : (Fin e → E) ≃ₗ[E] (Fin e → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (Matrix.diagonal a)) (Matrix.toLin' (Matrix.diagonal fun j => (a j)⁻¹))
    (by
      rw [← Matrix.toLin'_mul, Matrix.diagonal_mul_diagonal, ← Matrix.toLin'_one]
      congr 1
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply, mul_inv_cancel₀ (ha _)])
    (by
      rw [← Matrix.toLin'_mul, Matrix.diagonal_mul_diagonal, ← Matrix.toLin'_one]
      congr 1
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply, inv_mul_cancel₀ (ha _)])

theorem diagC_apply (a : Fin e → E) (ha : ∀ j, a j ≠ 0) (c : Fin e → E) (j : Fin e) :
    diagC a ha c j = a j * c j := by
  simp [diagC, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem det_diagC (a : Fin e → E) (ha : ∀ j, a j ≠ 0) :
    LinearMap.det ((diagC a ha : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) = ∏ j, a j := by
  simp [diagC, LinearMap.det_toLin', Matrix.det_diagonal]

theorem den_ne (J : FractionalIdeal (𝓞 E)⁰ E) : algebraMap (𝓞 E) E (J.den : 𝓞 E) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (J.den).2

theorem mem_num_iff (J : FractionalIdeal (𝓞 E)⁰ E) (y : E) :
    y ∈ ((J.num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∃ c ∈ J, algebraMap (𝓞 E) E (J.den : 𝓞 E) * c = y := by
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule,
    ← FractionalIdeal.den_mul_self_eq_num]
  change y ∈ (J.den : 𝓞 E) • (J : Submodule (𝓞 E) E) ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [Algebra.smul_def, FractionalIdeal.mem_coe]

theorem map_diag_piF (J : Fin e → FractionalIdeal (𝓞 E)⁰ E) :
    (piF J).map (((diagC (fun j => algebraMap (𝓞 E) E ((J j).den : 𝓞 E)) fun j => den_ne (J j) :
        (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E)) =
      piF (fun j => (((J j).num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) := by
  ext y
  rw [Submodule.mem_map, mem_piF]
  constructor
  · rintro ⟨c, hc, rfl⟩ j
    exact (mem_num_iff _ _).2 ⟨c j, mem_piF.1 hc j, by
      rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, diagC_apply]⟩
  · intro hy
    choose c hc hcy using fun j => (mem_num_iff _ _).1 (hy j)
    refine ⟨c, mem_piF.2 hc, funext fun j => ?_⟩
    rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, diagC_apply, hcy]

theorem relIndex_piF (K : Fin e → Ideal (𝓞 E)) :
    (piF (fun j => (K j : FractionalIdeal (𝓞 E)⁰ E))).toAddSubgroup.relIndex
      (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))).toAddSubgroup = ∏ j, Ideal.absNorm (K j) := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) = ((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    simp
  unfold piF
  rw [PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup, PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup, h1]
  exact PI.InvIdealIdxPiWork.relIndex_pi_idS K

theorem fg_piF (J : Fin e → FractionalIdeal (𝓞 E)⁰ E) : (piF J).FG := by
  set C := diagC (fun j => algebraMap (𝓞 E) E ((J j).den : 𝓞 E)) fun j => den_ne (J j)
  have hm := map_diag_piF J
  have hfg : (piF (fun j => (((J j).num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))).FG :=
    g_fg_le jLat_piF_one.1 (piF_mono fun _ => FractionalIdeal.coeIdeal_le_one)
  rw [← hm] at hfg
  have h2 := hfg.map (((C.symm : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))
  rwa [← Submodule.map_comp, show ((((C.symm : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars
      (𝓞 E)).comp (((C : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E))) =
      LinearMap.id by ext x; simp, Submodule.map_id] at h2

theorem jdel_piF {J : Fin e → FractionalIdeal (𝓞 E)⁰ E} (hJ : j_Lat (piF J)) :
    j_del (piF J) = (∏ j, FractionalIdeal.absNorm (J j)) *
      j_del (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))) := by
  set a : Fin e → E := fun j => algebraMap (𝓞 E) E ((J j).den : 𝓞 E) with ha
  set C := diagC a fun j => den_ne (J j)
  have hm := map_diag_piF J
  have hK : j_Lat (piF (fun j => (((J j).num : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))) := by
    rw [← hm]; exact j_Lat_map hJ C
  have e1 := j_del_map hJ C
  rw [hm, det_diagC] at e1
  have e2 := j_del_nested jLat_piF_one hK (piF_mono fun _ => FractionalIdeal.coeIdeal_le_one)
  rw [relIndex_piF, e1] at e2
  have hN : ∀ j, FractionalIdeal.absNorm (J j) = (Ideal.absNorm (J j).num : ℚ) / |Algebra.norm ℚ (a j)| := by
    intro j
    rw [FractionalIdeal.absNorm_eq, ha]
    congr 1
    rw [← Algebra.coe_norm_int]
    push_cast
    rfl
  have hpos : ∀ j, 0 < |Algebra.norm ℚ (a j)| := fun j =>
    abs_pos.2 (Algebra.norm_ne_zero_iff.2 (den_ne (J j)))
  rw [map_prod, Finset.abs_prod] at e2
  push_cast at e2
  simp_rw [hN]
  rw [Finset.prod_div_distrib]
  have hP : 0 < ∏ j, |Algebra.norm ℚ (a j)| := Finset.prod_pos fun j _ => hpos j
  rw [div_mul_eq_mul_div, eq_div_iff hP.ne']
  linear_combination e2

end Pi

section Dual

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {e : ℕ}

def psL (u : Fin e → S.V) (I : Fin e → FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) {y | ∃ j, ∃ x ∈ I j, y = x • u j}

def gramU (u : Fin e → S.V) : Matrix (Fin e) (Fin e) E := Matrix.of fun i j => S.hT (u i) (u j)

theorem psL_eq_map (u : Fin e → S.V) (I : Fin e → FractionalIdeal (𝓞 E)⁰ E) :
    psL u I = (piF I).map (j_iotaO u) := by
  apply le_antisymm
  · rw [psL, Submodule.span_le]
    rintro _ ⟨j, x, hx, rfl⟩
    refine ⟨Pi.single j x, mem_piF.2 fun i => ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs with h
      · subst h; exact hx
      · exact FractionalIdeal.mem_coe.1 ((I i : Submodule (𝓞 E) E).zero_mem)
    · show j_iota u (Pi.single j x) = x • u j
      rw [j_iota_apply]
      simp [Pi.single_apply]
  · rintro _ ⟨c, hc, rfl⟩
    show j_iota u c ∈ psL u I
    rw [j_iota_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, c i, mem_piF.1 hc i, rfl⟩

theorem coords_psL {u : Fin e → S.V} (hu : LinearIndependent E u) (I : Fin e → FractionalIdeal (𝓞 E)⁰ E) :
    (psL u I).comap (j_iotaO u) = piF I := by
  rw [psL_eq_map]
  exact Submodule.comap_map_eq_of_injective (f := j_iotaO u) (j_iota_inj hu) _

theorem exists_ne_mem {J : FractionalIdeal (𝓞 E)⁰ E} (hJ : J ≠ 0) : ∃ x ∈ J, x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hJ
  ext x
  constructor
  · intro hx
    rw [h x hx]
    exact (FractionalIdeal.mem_zero_iff _).mpr rfl
  · intro hx
    rw [FractionalIdeal.mem_zero_iff] at hx
    rw [hx]
    exact (J : Submodule (𝓞 E) E).zero_mem

theorem spanE_psL (u : Fin e → S.V) {I : Fin e → FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ j, I j ≠ 0) :
    spanE S (psL u I) = Submodule.span E (Set.range u) := by
  apply le_antisymm
  · have : psL u I ≤ (Submodule.span E (Set.range u)).restrictScalars (𝓞 E) := by
      rw [psL, Submodule.span_le]
      rintro _ ⟨j, x, -, rfl⟩
      exact Submodule.smul_mem _ x (Submodule.subset_span ⟨j, rfl⟩)
    rw [spanE, Submodule.span_le]
    exact fun y hy => this hy
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨x, hx, hx0⟩ := exists_ne_mem (hI j)
    have h1 : x • u j ∈ spanE S (psL u I) := Submodule.subset_span (Submodule.subset_span ⟨j, x, hx, rfl⟩)
    have h2 := Submodule.smul_mem _ x⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx0, one_smul] at h2

theorem hT_iota (u : Fin e → S.V) (v : S.V) (c : Fin e → E) :
    S.hT v (j_iota u c) = ∑ j, c j * S.hT v (u j) := by
  simp [j_iota, Fintype.linearCombination_apply, map_sum, map_smul]

theorem hT_smul_left (x : E) (v w : S.V) : S.hT (x • v) w = star x * S.hT v w := by
  simp [LinearMap.map_smulₛₗ₂]
  left
  rfl

theorem hT_iota_gram (u : Fin e → S.V) (c : Fin e → E) (i : Fin e) :
    S.hT (u i) (j_iota u c) = (gramU u).mulVec c i := by
  rw [hT_iota]
  simp [gramU, Matrix.mulVec, dotProduct, mul_comm]

theorem one_mul_mem {a b : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) (hb : b ∈ (1 : Submodule (𝓞 E) E)) :
    a * b ∈ (1 : Submodule (𝓞 E) E) := by
  simpa using Submodule.mul_mem_mul ha hb

theorem mem_one_frac {a : E} : a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ a ∈ (1 : Submodule (𝓞 E) E) := by
  rw [FractionalIdeal.mem_one_iff, Submodule.mem_one]

theorem mem_dual_psL (u : Fin e → S.V) {I : Fin e → FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ j, I j ≠ 0)
    (hs : ∀ j, ∀ x ∈ I j, star x ∈ I j) (c : Fin e → E) :
    j_iota u c ∈ Formalism.HermitianLatticesTheory.dual S.hT (psL u I) ↔ ∀ i, (gramU u).mulVec c i ∈ (I i)⁻¹ := by
  rw [i_mem_dual]
  constructor
  · intro h i
    rw [FractionalIdeal.mem_inv_iff (hI i)]
    intro y hy
    have h1 := h (star y • u i) (Submodule.subset_span ⟨i, star y, hs i y hy, rfl⟩)
    rw [hT_smul_left, star_star, hT_iota_gram] at h1
    rw [mem_one_frac, mul_comm]
    exact h1
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, x, hx, rfl⟩ := hy
      rw [hT_smul_left, hT_iota_gram, mul_comm]
      have := (FractionalIdeal.mem_inv_iff (hI j)).1 (h j) (star x) (hs j x hx)
      exact mem_one_frac.1 this
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hy hz
    | smul o y _ hy =>
      rw [← IsScalarTower.algebraMap_smul E o y, hT_smul_left]
      obtain ⟨o', ho'⟩ := i_star_int o
      refine one_mul_mem ?_ hy
      rw [← ho']
      exact Submodule.mem_one.2 ⟨o', rfl⟩

def gramO (u : Fin e → S.V) : (Fin e → E) →ₗ[𝓞 E] (Fin e → E) := (Matrix.toLin' (gramU u)).restrictScalars (𝓞 E)

theorem coords_dual {u : Fin e → S.V} {I : Fin e → FractionalIdeal (𝓞 E)⁰ E}
    (hI : ∀ j, I j ≠ 0) (hs : ∀ j, ∀ x ∈ I j, star x ∈ I j) :
    (dualIn S (psL u I)).comap (j_iotaO u) = (piF fun j => (I j)⁻¹).comap (gramO u) := by
  ext c
  rw [Submodule.mem_comap, Submodule.mem_comap]
  show j_iota u c ∈ dualInH S.hT (psL u I) ↔ _
  rw [dualInH, Submodule.mem_inf, mem_piF]
  have hsp : j_iota u c ∈ (Submodule.span E (psL u I : Set S.V)).restrictScalars (𝓞 E) := by
    show j_iota u c ∈ spanE S (psL u I)
    rw [spanE_psL u hI, ← j_iota_range]
    exact ⟨c, rfl⟩
  simp only [hsp, and_true, gramO, LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
  exact mem_dual_psL u hI hs c

theorem nondeg_span {u : Fin e → S.V} (hH : (gramU u).det ≠ 0) :
    Submodule.span E (Set.range u) ⊓ orth S (Submodule.span E (Set.range u)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxo⟩
  rw [← j_iota_range] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : (gramU u).mulVec c = 0 := funext fun i => by
    have h1 := Submodule.mem_iInf _ |>.1 hxo (u i)
    have h2 := Submodule.mem_iInf _ |>.1 h1 (Submodule.subset_span ⟨i, rfl⟩)
    rw [LinearMap.mem_ker, hT_iota_gram] at h2
    simpa using h2
  have : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hH hc
  subst this
  simp

def gramC (u : Fin e → S.V) (hH : (gramU u).det ≠ 0) : (Fin e → E) ≃ₗ[E] (Fin e → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (gramU u)) (Matrix.toLin' (gramU u)⁻¹)
    (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hH), Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hH), Matrix.toLin'_one])

theorem genIdx_psL {u : Fin e → S.V} (hu : LinearIndependent E u) {I : Fin e → FractionalIdeal (𝓞 E)⁰ E}
    (hI : ∀ j, I j ≠ 0) (hs : ∀ j, ∀ x ∈ I j, star x ∈ I j) (hH : (gramU u).det ≠ 0) :
    genIdx S (dualIn S (psL u I)) (psL u I) =
      |((Algebra.norm ℚ (gramU u).det : ℚ) : ℝ)| * ∏ j, ((FractionalIdeal.absNorm (I j) : ℚ) : ℝ) ^ 2 := by
  have hM : (psL u I).FG := by rw [psL_eq_map]; exact (fg_piF I).map _
  have hsp := spanE_psL u hI
  obtain ⟨l1, l2, hg⟩ := j_genIdx_dual hu hM hsp (by rw [hsp]; exact nondeg_span hH)
  rw [hg]
  rw [coords_psL hu] at l1 ⊢
  rw [coords_dual hI hs] at l2 ⊢
  set C := gramC u hH
  have hmap : ((piF fun j => (I j)⁻¹).comap (gramO u)).map
      (((C : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)).restrictScalars (𝓞 E)) =
      piF fun j => (I j)⁻¹ :=
    Submodule.map_comap_eq_of_surjective (f := gramO u) C.surjective _
  have e1 := j_del_map l2 C
  rw [hmap] at e1
  have hdet : LinearMap.det ((C : (Fin e → E) ≃ₗ[E] (Fin e → E)) : (Fin e → E) →ₗ[E] (Fin e → E)) = (gramU u).det := by
    show LinearMap.det (Matrix.toLin' (gramU u)) = _
    rw [LinearMap.det_toLin']
  rw [hdet] at e1
  have l3 : j_Lat (piF fun j => (I j)⁻¹) := by rw [← hmap]; exact j_Lat_map l2 C
  have e2 := jdel_piF l1
  have e3 := jdel_piF l3
  simp_rw [map_inv₀] at e3
  rw [Finset.prod_inv_distrib] at e3
  have hP := j_del_pos (jLat_piF_one (E := E) (e := e))
  have hn : 0 < ∏ j, FractionalIdeal.absNorm (I j) := Finset.prod_pos fun j _ =>
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm ((FractionalIdeal.absNorm_eq_zero_iff).not.2 (hI j)))
  have hd : 0 < |Algebra.norm ℚ (gramU u).det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hH)
  have hB := j_del_pos l2
  have key : (j_del (piF I) : ℚ) / j_del ((piF fun j => (I j)⁻¹).comap (gramO u)) =
      |Algebra.norm ℚ (gramU u).det| * ∏ j, FractionalIdeal.absNorm (I j) ^ 2 := by
    rw [Finset.prod_pow, div_eq_iff hB.ne', e2]
    have : j_del ((piF fun j => (I j)⁻¹).comap (gramO u)) =
        (∏ j, FractionalIdeal.absNorm (I j))⁻¹ * j_del (piF (fun _ : Fin e => (1 : FractionalIdeal (𝓞 E)⁰ E))) /
          |Algebra.norm ℚ (gramU u).det| := by
      rw [eq_div_iff hd.ne', mul_comm, ← e1, e3]
    rw [this]
    field_simp
  have key' := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at key'
  rw [← key']

end Dual

section Inst

open Formalism.MainNotions.S Formalism.L2.SG.DetUU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genIdxPseudo_holds : GenIdxPseudo := by
  intro D ι _ _ u I hu hI hs hH
  let σ := Fintype.equivFin ι
  have hpl : pseudoLat u I = psL (u ∘ σ.symm) (I ∘ σ.symm) := by
    unfold pseudoLat psL
    congr 1
    ext y
    constructor
    · rintro ⟨j, x, hx, rfl⟩
      exact ⟨σ j, x, by simpa using hx, by simp⟩
    · rintro ⟨j, x, hx, rfl⟩
      exact ⟨σ.symm j, x, hx, rfl⟩
  have hG : gramU (S := hS D) (u ∘ σ.symm) =
      (Matrix.of fun i j => (hS D).hT (u i) (u j)).submatrix σ.symm σ.symm := by
    ext i j
    rfl
  have hdet : (gramU (S := hS D) (u ∘ σ.symm)).det = (Matrix.of fun i j => (hS D).hT (u i) (u j)).det := by
    rw [hG, Matrix.det_submatrix_equiv_self]
  rw [hpl, genIdx_psL (I := I ∘ σ.symm) (hu.comp σ.symm σ.symm.injective) (fun j => hI _) (fun j => hs _) (by rwa [hdet]), hdet]
  congr 1
  exact Equiv.prod_comp σ.symm (fun j => ((FractionalIdeal.absNorm (I j) : ℚ) : ℝ) ^ 2)

theorem gram_determinant_relation : Formalism.L2.SG.LoopsFinal.GramDeterminantCount := gram_determinant_of_generic_index genIdxPseudo_holds

end Inst

end Formalism.L2.SG.Pf.LoopBGenIdx
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.FourierDecayAlt
  Formalism.L2.SG.ThmSOwn

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BM

variable (C0 : ℝ) {𝒞 : FamClass} (sel : SSel 𝒞) (yF : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → ℝ)

def YtR (hyF : YFOK sel yF) (C1f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (x : ℝ) (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
    (u u' : (Fm.D x i).what₂.Word) :
    LoopTie (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) :=
  loopTieOfParts
    (loopRowsOf (wOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X)
      (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1)
      (hOf _ _ _ _) (aOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (hvOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds (Fm.D x i)) u u'
      (frameEqvInj_of _ _ (hOf _ _ _ _) (aOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
        (hvOfW _ _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
        (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ _ _ _) u u'))
    (B Fm hc x hx i u u') (M Fm hc x hx i u u')

theorem tiesAt {D : D7} (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF))
    (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (u u' : D.what₂.Word) :
    Formalism.MainNotions.BridgeLemma₂.wordPairNormRelation (atOfW X Y hF hI hWD) u u' ∧ @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (atOfW X Y hF hI hWD) u u' ∧
      Formalism.MainNotions.BridgeLemma₂.wordPairEntriesInLattice (atOfW X Y hF hI hWD) u u' :=
  ⟨normTieC_holds D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u',
    Formalism.L2.SG.Pf.LoopBGenIdx.gram_determinant_relation D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u',
    entryLatC_holds D X Y hF hI (wOf X) (hOf X Y hF hI) (aOfW X Y hF hI hWD) (hvOfW X Y hF hI hWD) u u'⟩

theorem tiesR (hyF : YFOK sel yF) (C1f : List ℝ → ℝ)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) :
    Formalism.MainNotions.BridgeLemma₂.rows_TiesF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc)
              (YtR sel yF hyF C1f B M Fm hc) ∧
      ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (YtR sel yF hyF C1f B M Fm hc x hx i u u') := by
  have hTI : ∀ x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      Formalism.MainNotions.BridgeLemma₂.wordPairTermInjective (AtR sel yF hyF Fm hc x hx i) (YtR sel yF hyF C1f B M Fm hc x hx i u u') :=
    fun x hx i u u' t t' hL hE => frameEqvInj_of (wOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X) (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hOf ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1))
      (aOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (hvOfW ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2)
      (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) _) u u' t t' hL hE
  refine ⟨Formalism.MainNotions.BridgeLemma₂.family_gram_facts_of_hypotheses _ _ _ _ fun x hx i u u' =>
    ⟨(tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').1,
      (tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').2.1,
      (tiesAt ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).X ((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).Y (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1 (((sel Fm hc).2 x (raise_lt hx) (h0R sel yF hx) i).hI (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).1) (hyF Fm hc x (raise_lt hx) (h0R sel yF hx) (hyR sel yF hx) i).2 u u').2.2, hTI x hx i u u'⟩, hTI⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem loopRowS_of_BM (hyF : YFOK sel yF) (C1f : List ℝ → ℝ) (Uf : (List ℝ → ℝ) → List ℝ → Formalism.L2.SG.RowsU.UC)
    (B : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (_ : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' (C1f Fm.cOut))
    (M : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : (Fm.raise (yR sel yF Fm hc)).x1 < x) (i : Fm.Ix x)
      (u u' : (Fm.D x i).what₂.Word),
      LoopTermDat (Fm.D x i) (Fm.L x i) (AtR sel yF hyF Fm hc x hx i) u u' (C1f Fm.cOut) (B Fm hc x hx i u u'))
    (hAdmR : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm,
      VanishingOnXAndXPlus.AdmF (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (YtR sel yF hyF C1f B M Fm hc))
    (hUR : ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm,
      Formalism.L2.SG.RowsU.UAdm (Fm.raise (yR sel yF Fm hc)) (C1f Fm.cOut) (AtR sel yF hyF Fm hc) (YtR sel yF hyF C1f B M Fm hc)
        (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) (Uf aF (Fm.cOut ++ Fm.cMid CH)))
    (hForm : Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      Hyp0 (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :
    LoopRowS C0 𝒞 sel :=
  loopRowS_of_U C0 sel yF hyF C1f Uf (YtR sel yF hyF C1f B M) hAdmR hUR
    ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => tiesR sel yF hyF C1f B M Fm hc⟩⟩
    hForm



end BM

end Formalism.L2.SG.LoopsTies
end
end
