import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstY
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbMSectMul

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem pushLFin_of_proper (h : ProperOrb) : PushLFin := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK hKI
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  obtain ⟨N, hN, C, hC, hNC⟩ := h X u' ψ hT μinf νinf fibInf hH K hK hKI
  rw [Measure.map_apply (measurable_orbM X u') hK.isClosed.measurableSet]
  refine lt_of_le_of_lt (measure_mono fun g hg => hNC 1 (mem_of_mem_nhds hN) g ?_) hC.measure_lt_top
  rw [rmulT_one]; exact hg

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ProperOne : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K →
      ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • Y0 X u' ∈ K → g ∈ C

def InvNbhd : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ N ∈ 𝓝 (1 : MfI X), ∃ Nc : Set (MfI X), IsCompact Nc ∧ ∀ b ∈ N, ∃ c ∈ Nc, c * b = 1

theorem rmulT_rmulT {D : D7} (X : HidaSetting D) (b c : MfI X) (Y : TupI X) :
    rmulT X c (rmulT X b Y) = rmulT X (b * c) Y := by
  funext a i
  simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem smul_rmulT {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (b : MfI X)
    (Y : TupI X) : g • rmulT X b Y = rmulT X b (g • Y) := by
  change (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (rmulT X b Y a)) =
    rmulT X b (fun a => ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (Y a))
  funext a i
  simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem continuous_right_mul_tuple {D : D7} (X : HidaSetting D) :
    Continuous (fun p : MfI X × TupI X => rmulT X p.1 p.2) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply_apply c a).comp continuous_fst).mul ((continuous_apply_apply c i).comp continuous_snd)

theorem properOrb_of_one (h1 : ProperOne) (hI : InvNbhd) : ProperOrb := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK _
  obtain ⟨N, hN, Nc, hNc, hNi⟩ := hI X
  have hK' : IsCompact ((fun p : MfI X × TupI X => rmulT X p.1 p.2) '' (Nc ×ˢ K)) :=
    (hNc.prod hK).image (continuous_right_mul_tuple X)
  obtain ⟨C, hC, hgC⟩ := h1 X u' ψ hT μinf νinf fibInf hH _ hK'
  refine ⟨N, hN, C, hC, fun b hb g hg => hgC g ?_⟩
  obtain ⟨c, hc, hcb⟩ := hNi b hb
  have hbc : b * c = 1 := mul_eq_one_comm.1 hcb
  refine ⟨(c, g • rmulT X b (Y0 X u')), ⟨hc, hg⟩, ?_⟩
  show rmulT X c (g • rmulT X b (Y0 X u')) = g • Y0 X u'
  rw [smul_rmulT, rmulT_rmulT, hbc, rmulT_one]


end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem fbI_closed {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) : IsClosed (FbI X u' hT) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det =
      inclR (F := X.B.I.F) (Ainf X.B.I.F) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det := by
    rw [RingHom.map_det]; rfl
  have hsub : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} ⊆ IndI X := by
    intro y hy
    have hy' : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y = ((TI X u' hT : HmI X) : Matrix _ _ _) := hy
    apply linIndep_of_isUnit_det (R := Ainf X.B.I.F) (σ := X.B.I.cm.sig) (J := X.B.I.J) y
    rw [hy']
    show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (F := X.B.I.F) (Ainf X.B.I.F))).det
    rw [hdet]
    exact (isUnit_iff_ne_zero.2 hd).map _
  have he : FbI X u' hT = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HmI X) : Matrix _ _ _)} :=
    Set.inter_eq_left.2 hsub
  rw [he]
  exact isClosed_singleton.preimage (continuous_gramI X)

theorem properOne_of (hW : WittInf) (hH : MassDataMassesW.HinfCompact) : ProperOne := by
  intro D X u' ψ hT μinf νinf fibInf hP K hK
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : LocallyCompactSpace (GI X) :=
    inferInstanceAs (LocallyCompactSpace (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have horb : MulAction.orbit (GI X) (Y0 X u') = FbI X u' hT := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩; exact orbM_mem X u' hT hd g
    · intro y hy
      obtain ⟨g, hg⟩ := hW X u' ψ hT μinf νinf fibInf hP hy
      exact ⟨g, hg⟩
  have hcl : IsClosed (MulAction.orbit (GI X) (Y0 X u')) := horb ▸ fbI_closed X u' hT hd
  have : LocallyCompactSpace (MulAction.orbit (GI X) (Y0 X u')) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hjoint : Continuous (fun p : GI X × TupI X => p.1 • p.2) := by
    refine continuous_pi fun a => ?_
    change Continuous fun p : GI X × TupI X =>
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J p.1 : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (p.2 a)
    exact ((MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).comp
      continuous_fst).matrix_mulVec ((continuous_apply a).comp continuous_snd)
  have : ContinuousSMul (GI X) (MulAction.orbit (GI X) (Y0 X u')) :=
    ⟨continuous_induced_rng.2 (hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have y0O : Y0 X u' ∈ MulAction.orbit (GI X) (Y0 X u') := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun g : GI X => g • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) :=
    isOpenMap_smul_of_sigmaCompact _
  have hHc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X)) := by
    have : CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := hH X u'
    have h := isCompact_range (continuous_subtype_val :
      Continuous (Subtype.val : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') → GI X))
    rwa [Subtype.range_coe] at h
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GI X)
  let U : GI X → Set (MulAction.orbit (GI X) (Y0 X u')) := fun g =>
    (fun h : GI X => h • (⟨Y0 X u', y0O⟩ : MulAction.orbit (GI X) (Y0 X u'))) '' ((fun h => h * g) '' interior V)
  have hUo : ∀ g, IsOpen (U g) := fun g => hopen _ ((isOpenMap_mul_right g) _ isOpen_interior)
  have hKO : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hcov : (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) ⊆ ⋃ g, U g := by
    intro y _
    obtain ⟨g, hg⟩ := y.2
    refine Set.mem_iUnion.2 ⟨g, 1 * g, ⟨1, mem_interior_iff_mem_nhds.2 hV1, rfl⟩, ?_⟩
    apply Subtype.ext
    show (1 * g) • Y0 X u' = y.1
    rw [one_mul]; exact hg
  obtain ⟨t, ht⟩ := hKO.elim_finite_subcover U hUo hcov
  refine ⟨⋃ g ∈ t, (fun p : GI X × GI X => p.1 * g * p.2) ''
      (V ×ˢ (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') : Set (GI X))),
    t.isCompact_biUnion fun g _ => (hVc.prod hHc).image ((continuous_fst.mul continuous_const).mul continuous_snd),
    fun g hg => ?_⟩
  have hy : (⟨g • Y0 X u', ⟨g, rfl⟩⟩ : MulAction.orbit (GI X) (Y0 X u')) ∈
      (Subtype.val ⁻¹' K : Set (MulAction.orbit (GI X) (Y0 X u'))) := hg
  obtain ⟨g', hg't, hyU⟩ := Set.mem_iUnion₂.1 (ht hy)
  obtain ⟨_, ⟨v, hv, rfl⟩, hvg⟩ := hyU
  have hvg' : (v * g') • Y0 X u' = g • Y0 X u' := congrArg Subtype.val hvg
  refine Set.mem_iUnion₂.2 ⟨g', hg't, (v, (v * g')⁻¹ * g), ⟨interior_subset hv, ?_⟩, ?_⟩
  · show ((v * g')⁻¹ * g) ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')
    rw [mem_H_iff]
    change ((v * g')⁻¹ * g) • Y0 X u' = Y0 X u'
    rw [mul_smul, ← hvg', ← mul_smul, inv_mul_cancel, one_smul]
  · exact mul_inv_cancel_left (v * g') g


end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem isOpen_units_tens {D : D7} (X : HidaSetting D) :
    IsOpen {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) (Module.finBasis X.B.I.F X.B.I.E)
  have key : {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} =
      (fun x => (LinearMap.toMatrix B B (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) x)).det) ⁻¹'
        {a | IsUnit a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det]
    constructor
    · intro h; exact h.map (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
    · intro h
      obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 h).2 1
      exact isUnit_iff_exists_inv.2 ⟨y, hy⟩
  rw [key]
  refine (PI.AprimeInfW.isOpen_units_Ainf X.B.I.F).preimage (Continuous.matrix_det ?_)
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  change Continuous fun x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i (x * B j)
  have hc : Continuous fun v : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i v :=
    IsModuleTopology.continuous_of_linearMap (B.coord i)
  exact hc.comp (continuous_mul_const _)

theorem invNbhd_holds : InvNbhd := by
  intro D X
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : T2Space (MfI X) := inferInstanceAs (T2Space (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
    (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (MfI X) := inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (MfI X) := inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have hU : IsOpen {M : MfI X | IsUnit M} := by
    have e : {M : MfI X | IsUnit M} = (fun M : MfI X => M.det) ⁻¹' {x | IsUnit x} := by
      ext M; exact Matrix.isUnit_iff_isUnit_det M
    rw [e]
    exact (isOpen_units_tens X).preimage (continuous_id.matrix_det)
  have : LocallyCompactSpace (MfI X)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (MfI X)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : MfI X ≃ₜ (MfI X)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (MfI X)ˣ := Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hO : MulAction.orbit (MfI X)ˣ (1 : MfI X) = {M : MfI X | IsUnit M} := by
    ext M; constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
  have hOo : IsOpen (MulAction.orbit (MfI X)ˣ (1 : MfI X)) := hO ▸ hU
  have : LocallyCompactSpace (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    hOo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul (MfI X)ˣ (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    ⟨continuous_induced_rng.2 (by
      change Continuous fun p : (MfI X)ˣ × MulAction.orbit (MfI X)ˣ (1 : MfI X) => ((p.1 : MfI X) * (p.2 : MfI X))
      exact (Units.continuous_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))⟩
  have y1 : (1 : MfI X) ∈ MulAction.orbit (MfI X)ˣ (1 : MfI X) := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) :=
    isOpenMap_smul_of_sigmaCompact _
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : (MfI X)ˣ)
  have hWo : IsOpen (Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V)) :=
    hOo.isOpenMap_subtype_val _ (hopen _ isOpen_interior)
  have h1W : (1 : MfI X) ∈ Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V) :=
    ⟨⟨1, y1⟩, ⟨1, mem_interior_iff_mem_nhds.2 hV1, one_smul _ _⟩, rfl⟩
  refine ⟨_, hWo.mem_nhds h1W, (fun u : (MfI X)ˣ => ((u⁻¹ : (MfI X)ˣ) : MfI X)) '' V,
    hVc.image Units.continuous_coe_inv, ?_⟩
  rintro b ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨((u⁻¹ : (MfI X)ˣ) : MfI X), ⟨u, interior_subset hu, rfl⟩, ?_⟩
  change ((u⁻¹ : (MfI X)ˣ) : MfI X) * ((u : MfI X) * 1) = 1
  simp


end PI.AprimeInfW
end
end
