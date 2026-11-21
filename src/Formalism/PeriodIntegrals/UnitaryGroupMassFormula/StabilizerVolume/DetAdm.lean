import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuInvSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish

section
noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Borel

variable {F : Type} [Field F] [NumberField F]

instance borel_Ainf : BorelSpace (Ainf F) := ⟨rfl⟩
instance borel_Af : BorelSpace (Af F) := ⟨rfl⟩
instance borel_AF : BorelSpace (AF F) := ⟨rfl⟩
instance borel_Fv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
instance borel_tens {E : Type} [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

end Borel

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_intV : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isClopen_intV : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) := by
  exact Valued.isClopen_valuationSubring _

instance lc_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_intV v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isClopen_intV v).isOpen.mem_nhds (zero_mem (v.adicCompletionIntegers F)))

theorem isClopen_translate (t : Fv F v) :
    IsClopen ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) := by
  exact (isClopen_intV v).preimage (Homeomorph.subRight t).continuous

theorem isCompact_translate (t : Fv F v) :
    IsCompact ((Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) := by
  exact (Homeomorph.subRight t).isCompact_preimage.mpr (isCompact_intV v)

theorem mem_translate (t : Fv F v) :
    t ∈ (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  simp

theorem exists_cc {W : Set (Fv F v)} (hW : IsOpen W) {t : Fv F v} (ht : t ∈ W) :
    ∃ C, IsClopen C ∧ IsCompact C ∧ t ∈ C ∧ C ⊆ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (hW.mem_nhds ht)
  have hB : IsClopen ((Homeomorph.subRight t) ⁻¹' {x : Fv F v | Valued.v.restrict x < (γ : _)}) :=
    (Valued.isClopen_ball _ _).preimage (Homeomorph.subRight t).continuous
  refine ⟨(Homeomorph.subRight t) ⁻¹' {x : Fv F v | Valued.v.restrict x < (γ : _)} ∩
      (Homeomorph.subRight t) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)),
    hB.inter (isClopen_translate v t), (isCompact_translate v t).inter_left hB.isClosed,
    ⟨?_, mem_translate v t⟩, fun y hy => hγ hy.1⟩
  show Valued.v.restrict (t - t) < (γ : _)
  rw [sub_self, map_zero]
  exact zero_lt_iff.2 (Units.ne_zero γ)

end Local

section Box1

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_finite_adele_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  classical
  set S' : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))} with hS'
  have hS : Filter.cofinite ≤ Filter.principal S' := Filter.le_principal_iff.2 hf
  have hBY : IsCompact {y : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal S') | ∀ v, y v ∈ D v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : (DFunLike.coe '' {y : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
        (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal S') | ∀ v, y v ∈ D v}) =
        Set.pi Set.univ D := by
      ext f
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hf'
        refine ⟨⟨f, Filter.eventually_principal.2 (fun v hv => ?_)⟩, fun v => hf' v (Set.mem_univ _), rfl⟩
        have h1 := hf' v (Set.mem_univ _)
        rw [show D v = _ from hv] at h1
        exact h1
    rw [e]
    exact isCompact_univ_pi hc
  have himg : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion _ _ hS ''
      {y : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
        (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal S') | ∀ v, y v ∈ D v} := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x.1, Filter.eventually_principal.2 (fun v hv => ?_)⟩, fun v => hx v, rfl⟩
      have h1 := hx v
      rw [show D v = _ from hv] at h1
      exact h1
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [himg]
  exact hBY.image (RestrictedProduct.continuous_inclusion hS)

end Box1

end PI.VolStabS.DeterminantAdmissible
end
end

section
noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Boxes

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

def boxS (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (ι → Af F) :=
  {y | ∀ c v, y c v ∈ D c v}

def IsBoxD (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Prop :=
  (∀ c v, IsClopen (D c v) ∧ IsCompact (D c v)) ∧
    ∀ᶠ v in cofinite, ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))

variable (F ι) in

def boxes : Set (Set (ι → Af F)) := {s | ∃ D, IsBoxD D ∧ s = boxS D}

theorem boxS_eq (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) :
    boxS D = Set.pi univ fun c => {x : Af F | ∀ v, x v ∈ D c v} := by
  ext y
  simp [boxS]

private theorem isOpen_isCompact_restrictedProduct_box {κ : Type*} {R : κ → Type*} [∀ i, TopologicalSpace (R i)]
    {A : ∀ i, Set (R i)} (hA : ∀ i, IsOpen (A i)) (D : ∀ i, Set (R i))
    (hDo : ∀ i, IsOpen (D i)) (hDc : ∀ i, IsCompact (D i))
    (hcof : ∀ᶠ i in cofinite, D i = A i) :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, f i ∈ D i} ∧
      IsCompact {f : Πʳ i, [R i, A i] | ∀ i, f i ∈ D i} := by
  set S : Set κ := {i | D i = A i} with hSdef
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hcof
  have hfin : Sᶜ.Finite := mem_cofinite.1 hcof
  have himg : {f : Πʳ i, [R i, A i] | ∀ i, f i ∈ D i} =
      RestrictedProduct.inclusion R A hS ''
        (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' (univ.pi D)) := by
    ext f
    constructor
    · intro hf
      refine ⟨⟨fun i => f i, ?_⟩, ?_, ?_⟩
      · exact eventually_principal.2 fun i hi => by
          have h : D i = A i := hi
          show f i ∈ A i
          rw [← h]
          exact hf i
      · intro i _
        exact hf i
      · rfl
    · rintro ⟨g, hg, rfl⟩ i
      exact hg i (mem_univ i)
  rw [himg]
  constructor
  · refine (RestrictedProduct.isOpenEmbedding_inclusion_principal hA hS).isOpenMap _ ?_
    have h : (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' (univ.pi D)) =
        ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' (Sᶜ.pi D) := by
      ext g
      simp only [mem_preimage, Set.mem_pi]
      refine ⟨fun h i _ => h i (mem_univ i), fun h i _ => ?_⟩
      by_cases hi : i ∈ S
      · have h' : D i = A i := hi
        rw [h']
        exact g.2 hi
      · exact h i hi
    rw [h]
    exact (isOpen_set_pi hfin fun i _ => hDo i).preimage RestrictedProduct.continuous_coe
  · refine IsCompact.image ?_ (RestrictedProduct.continuous_inclusion hS)
    refine (RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_).2
      (isCompact_univ_pi hDc)
    rw [RestrictedProduct.range_coe_principal]
    intro g hg i hi
    have h : D i = A i := hi
    rw [← h]
    exact hg i (mem_univ i)

theorem isCompact_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsCompact (boxS D) := by
  rw [boxS_eq]
  exact isCompact_univ_pi fun c => (isOpen_isCompact_restrictedProduct_box (fun v => Valued.isOpen_valuationSubring _)
    (D c) (fun v => (hD.1 c v).1.isOpen) (fun v => (hD.1 c v).2) (hD.2.mono fun v h => h c)).2

theorem isOpen_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsOpen (boxS D) := by
  rw [boxS_eq]
  exact isOpen_set_pi finite_univ fun c _ => (isOpen_isCompact_restrictedProduct_box
    (fun v => Valued.isOpen_valuationSubring _) (D c) (fun v => (hD.1 c v).1.isOpen)
    (fun v => (hD.1 c v).2) (hD.2.mono fun v h => h c)).1

theorem boxes_inter {s t : Set (ι → Af F)} (hs : s ∈ boxes F ι) (ht : t ∈ boxes F ι) :
    s ∩ t ∈ boxes F ι := by
  obtain ⟨D, hD, rfl⟩ := hs
  obtain ⟨D', hD', rfl⟩ := ht
  refine ⟨fun c v => D c v ∩ D' c v, ⟨fun c v => ⟨(hD.1 c v).1.inter (hD'.1 c v).1,
    (hD.1 c v).2.inter_right (hD'.1 c v).1.isClosed⟩, ?_⟩, ?_⟩
  · filter_upwards [hD.2, hD'.2] with v h1 h2 c
    rw [h1 c, h2 c, inter_self]
  · ext y
    simp only [boxS, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ c v
      exact ⟨h1 c v, h2 c v⟩
    · intro h
      exact ⟨fun c v => (h c v).1, fun c v => (h c v).2⟩

private theorem preimage_sub_integers_mem_and_eq_of_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    IsClopen ((fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      IsCompact ((fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      a ∈ (fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) ∧
      (a ∈ v.adicCompletionIntegers F →
        (fun z => z - a) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) =
          (v.adicCompletionIntegers F : Set (Fv F v))) := by
  have hOc := AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine ⟨IsClopen.preimage ⟨hOc.isClosed, hOo⟩ (continuous_id.sub continuous_const),
    (Homeomorph.subRight a).isCompact_preimage.2 hOc, ?_, fun ha => ?_⟩
  · simp only [mem_preimage, sub_self, SetLike.mem_coe]
    exact zero_mem _
  · ext z
    simp only [mem_preimage, SetLike.mem_coe]
    constructor
    · intro h
      simpa using add_mem h ha
    · intro h
      exact sub_mem h ha

theorem exists_box_mem (y : ι → Af F) : ∃ D, IsBoxD D ∧ y ∈ boxS D := by
  refine ⟨fun c v => (fun z => z - y c v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)),
    ⟨fun c v => ⟨(preimage_sub_integers_mem_and_eq_of_mem v (y c v)).1, (preimage_sub_integers_mem_and_eq_of_mem v (y c v)).2.1⟩, ?_⟩, ?_⟩
  · filter_upwards [eventually_all.2 fun c => (y c).2] with v hv c
    exact (preimage_sub_integers_mem_and_eq_of_mem v (y c v)).2.2.2 (hv c)
  · show ∀ c v, y c v ∈ (fun z => z - y c v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
    exact fun c v => (preimage_sub_integers_mem_and_eq_of_mem v (y c v)).2.2.1

theorem boxes_seq : ∃ bs : ℕ → Set (ι → Af F), (∀ n, bs n ∈ boxes F ι) ∧ ⋃ n, bs n = univ := by
  have hopen : ∀ s ∈ boxes F ι, IsOpen s := by
    rintro s ⟨D, hD, rfl⟩
    exact isOpen_boxS hD
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable (boxes F ι) hopen
  have hU : ⋃₀ boxes F ι = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨D, hD, hy⟩ := exists_box_mem y
    exact ⟨boxS D, ⟨D, hD, rfl⟩, hy⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sUnion_empty, hU] at hTU
    exact empty_ne_univ hTU
  obtain ⟨bs, rfl⟩ := hTc.exists_eq_range hTne
  refine ⟨bs, fun n => hTS (mem_range_self n), ?_⟩
  rw [← sUnion_range, hTU, hU]


open Classical in

def upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
  fun c' => if c' = c then Function.update (D c) v (D c v ∩ C) else D c'

private theorem exists_restricted_box_subset_of_isOpen {x : Af F} {U : Set (Af F)} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ E : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v),
      (∀ v, IsClopen (E v) ∧ IsCompact (E v)) ∧
      (∀ᶠ v in cofinite, E v = (v.adicCompletionIntegers F : Set (Fv F v))) ∧
      (∀ v, x v ∈ E v) ∧ {z : Af F | ∀ v, z v ∈ E v} ⊆ U := by
  classical
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    fun v => Valued.isOpen_valuationSubring _
  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | x v ∈ v.adicCompletionIntegers F} with hSdef
  have hSc : S ∈ cofinite := x.2
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hSc
  let x' : Πʳ v : HeightOneSpectrum (𝓞 F),
      [Fv F v, (v.adicCompletionIntegers F : Set (Fv F v))]_[𝓟 S] :=
    ⟨fun v => x v, eventually_principal.2 fun v hv => hv⟩
  have hUx : U ∈ 𝓝 (RestrictedProduct.inclusion _ _ hS x') := hU.mem_nhds hx
  rw [RestrictedProduct.nhds_eq_map_inclusion hA hS] at hUx
  have hUx2 : (RestrictedProduct.inclusion _ _ hS) ⁻¹' U ∈ 𝓝 x' := hUx
  rw [RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hUx2
  obtain ⟨N, hN, hNU⟩ := hUx2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hIt⟩ := hN
  have key : ∀ v, ∃ V : Set (Fv F v), IsClopen V ∧ x v ∈ V ∧
      V ⊆ t v ∩ (fun z => z - x v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro v
    obtain ⟨hT1, -, hT3, -⟩ := preimage_sub_integers_mem_and_eq_of_mem v (x v)
    obtain ⟨W, hWt, hWo, hxW⟩ := mem_nhds_iff.1 (ht v)
    obtain ⟨V, hV, hxV, hVW⟩ :=
      (loc_compact_Haus_tot_disc_of_zero_dim (H := Fv F v)).exists_subset_of_mem_open
        (show x v ∈ W ∩ _ from ⟨hxW, hT3⟩) (hWo.inter hT1.isOpen)
    exact ⟨V, hV, hxV, hVW.trans (inter_subset_inter_left _ hWt)⟩
  choose V hVc hxV hVsub using key
  obtain ⟨E, hEv⟩ : ∃ E : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), ∀ v, E v =
      if v ∈ I then V v
      else (fun z => z - x v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) :=
    ⟨_, fun v => rfl⟩
  have hEsub : ∀ v, E v ⊆ (fun z => z - x v) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro v
    by_cases hv : v ∈ I
    · rw [hEv v, if_pos hv]
      exact (hVsub v).trans inter_subset_right
    · rw [hEv v, if_neg hv]
  refine ⟨E, fun v => ?_, ?_, fun v => ?_, ?_⟩
  · obtain ⟨hT1, hT2, -, -⟩ := preimage_sub_integers_mem_and_eq_of_mem v (x v)
    by_cases hv : v ∈ I
    · rw [hEv v, if_pos hv]
      exact ⟨hVc v, hT2.of_isClosed_subset (hVc v).1 ((hVsub v).trans inter_subset_right)⟩
    · rw [hEv v, if_neg hv]
      exact ⟨hT1, hT2⟩
  · filter_upwards [hSc, hI.compl_mem_cofinite] with v hvS hvI
    rw [hEv v, if_neg hvI]
    exact (preimage_sub_integers_mem_and_eq_of_mem v (x v)).2.2.2 hvS
  · by_cases hv : v ∈ I
    · rw [hEv v, if_pos hv]
      exact hxV v
    · rw [hEv v, if_neg hv]
      exact (preimage_sub_integers_mem_and_eq_of_mem v (x v)).2.2.1
  · intro z hz
    have hz1 : ∀ v, z v ∈ E v := hz
    have hzE : ∀ v, z v - x v ∈ v.adicCompletionIntegers F := fun v => hEsub v (hz1 v)
    let z' : Πʳ v : HeightOneSpectrum (𝓞 F),
        [Fv F v, (v.adicCompletionIntegers F : Set (Fv F v))]_[𝓟 S] :=
      ⟨fun v => z v, eventually_principal.2 fun v hv => by
        have h2 : x v ∈ v.adicCompletionIntegers F := hv
        simpa using add_mem (hzE v) h2⟩
    have hz' : z' ∈ ((↑) : _ → Π v, Fv F v) ⁻¹' N := hIt fun v hv => by
      have h := hz1 v
      rw [hEv v, if_pos hv] at h
      exact ((hVsub v) h).1
    exact hNU hz'

theorem generateFrom_boxes : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro s ⟨D, hD, rfl⟩
    exact (isOpen_boxS hD).measurableSet
  · have hb : (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) = borel (ι → Af F) :=
      BorelSpace.measurable_eq
    rw [hb, borel]
    refine generateFrom_le fun O hO => ?_
    have hO' : IsOpen O := hO
    set Bs : Set (Set (ι → Af F)) := {s | s ∈ boxes F ι ∧ s ⊆ O} with hBs
    obtain ⟨T, hTc, hTB, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable Bs (fun s hs => by
      obtain ⟨D, hD, hsD⟩ := hs.1
      rw [hsD]
      exact isOpen_boxS hD)
    have hOU : ⋃₀ Bs = O := by
      refine Subset.antisymm (sUnion_subset fun s hs => hs.2) fun y hy => ?_
      have hN : O ∈ 𝓝 y := hO'.mem_nhds hy
      rw [nhds_pi, Filter.mem_pi] at hN
      obtain ⟨I, -, t, ht, hIt⟩ := hN
      have hE : ∀ c, ∃ E : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v),
          (∀ v, IsClopen (E v) ∧ IsCompact (E v)) ∧
          (∀ᶠ v in cofinite, E v = (v.adicCompletionIntegers F : Set (Fv F v))) ∧
          (∀ v, y c v ∈ E v) ∧ {z : Af F | ∀ v, z v ∈ E v} ⊆ t c := fun c => by
        obtain ⟨U, hUt, hUo, hyU⟩ := mem_nhds_iff.1 (ht c)
        obtain ⟨E, h1, h2, h3, h4⟩ := exists_restricted_box_subset_of_isOpen hUo hyU
        exact ⟨E, h1, h2, h3, h4.trans hUt⟩
      choose E hE1 hE2 hE3 hE4 using hE
      have hyE : y ∈ boxS E := by
        show ∀ c v, y c v ∈ E c v
        exact fun c v => hE3 c v
      refine ⟨boxS E, ⟨⟨E, ⟨hE1, eventually_all.2 hE2⟩, rfl⟩, fun z hz => hIt fun c _ => ?_⟩, hyE⟩
      have hz' : ∀ c v, z c v ∈ E c v := hz
      exact hE4 c (hz' c)
    rw [← hOU, ← hTU]
    exact MeasurableSet.sUnion hTc fun s hs => measurableSet_generateFrom (hTB hs).1

end Boxes

end PI.VolStabS.DeterminantAdmissible
end
end

section
noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabS
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

section Crd

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {a M : ℕ}

def crdH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a × Fin M × Fin d → R) where
  toFun X c := crd b R (X c.1 c.2.1) c.2.2
  invFun Y x i := (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (x, i, k))
  left_inv X := by
    funext x i
    show (Algebra.TensorProduct.basis R b).equivFun.symm (fun k => crd b R (X x i) k) = X x i
    have e : (fun k => crd b R (X x i) k) = (Algebra.TensorProduct.basis R b).equivFun (X x i) := by
      funext k
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.symm_apply_apply]
  right_inv Y := by
    funext c
    show crd b R ((Algebra.TensorProduct.basis R b).equivFun.symm (fun k => Y (c.1, c.2.1, k))) c.2.2
      = Y c
    have e : ∀ y, crd b R y c.2.2 = (Algebra.TensorProduct.basis R b).equivFun y c.2.2 := fun y => by
      simp [crd, Module.Basis.equivFun_apply]
    rw [e, LinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_pi fun c =>
    (continuous_crd b R c.2.2).comp ((continuous_apply c.2.1).comp (continuous_apply c.1))
  continuous_invFun := continuous_pi fun x => continuous_pi fun i =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply _)

end Crd

section Split

variable (F : Type) [Field F] [NumberField F]

def splitH (ι : Type) : (ι → AF F) ≃ₜ (ι → Ainf F) × (ι → Af F) where
  toFun Y := (fun c => fstA F (Y c), fun c => sndA F (Y c))
  invFun p c := pairA F (p.1 c) (p.2 c)
  left_inv Y := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine (continuous_pi fun c => ?_).prodMk (continuous_pi fun c => ?_)
    · exact continuous_fst.comp (continuous_apply c)
    · exact continuous_snd.comp (continuous_apply c)
  continuous_invFun := continuous_pi fun c =>
    ((continuous_apply c).comp continuous_fst).prodMk ((continuous_apply c).comp continuous_snd)

end Split

section admitted

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}

def locBox (D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
  (crdH b (Fv F v)) ⁻¹' (Set.pi univ fun c => D c v)

variable {b}

theorem isClopen_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsClopen (locBox b D v) :=
  (show IsClopen (Set.pi univ fun c => D c v) from ⟨isClosed_set_pi (fun c _ => (hD.1 c v).1.isClosed),
    isOpen_set_pi finite_univ (fun c _ => (hD.1 c v).1.isOpen)⟩).preimage (crdH b (Fv F v)).continuous

theorem isCompact_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsCompact (locBox b D v) :=
  (crdH b (Fv F v)).isCompact_preimage.2 (isCompact_univ_pi fun c => (hD.1 c v).2)

theorem isSB_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) :
    IsSB ((locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (isClopen_locBox hD v)).isLocallyConstant,
    HasCompactSupport.intro' (isCompact_locBox hD v) (isClopen_locBox hD v).isClosed
      fun Y hY => Set.indicator_of_notMem hY _⟩

theorem locBox_eq_latV {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    locBox b D v = latV b v := by
  ext Y
  simp only [locBox, latV, mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  constructor
  · intro h x i k
    have h1 := h (x, i, k)
    rw [hv] at h1
    exact h1
  · intro h c
    rw [hv]
    exact h c.1 c.2.1 c.2.2

theorem finprod_ite {α : Type} (P : α → Prop) [DecidablePred P] [Decidable (∀ v, P v)] (h : ∀ᶠ v in cofinite, P v) :
    ∏ᶠ v, (if P v then (1 : ℂ) else 0) = if ∀ v, P v then 1 else 0 := by
  by_cases hall : ∀ v, P v
  · rw [if_pos hall]
    exact finprod_eq_one_of_forall_eq_one fun v => if_pos (hall v)
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨v0, hv0⟩ := hall
    refine finprod_eq_zero _ v0 (if_neg hv0) ?_
    refine (eventually_cofinite.1 h).subset fun v hv => ?_
    intro hP
    exact hv (if_pos hP)

theorem finprod_locBox {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (W : Fin a → Fin M → Af F ⊗[F] E) :
    ∏ᶠ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      (boxS D).indicator 1 (crdH b (Af F) W) := by
  classical
  set q := crdH b (Af F) W
  have hv : ∀ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      if (∀ c, q c v ∈ D c v) then 1 else 0 := by
    intro v
    have e : ∀ c, crdH b (Fv F v) (projV v W) c = q c v := fun c =>
      crd_map b (evalV F v) (W c.1 c.2.1) c.2.2
    rw [Set.indicator_apply]
    simp only [locBox, mem_preimage, Set.mem_univ_pi, e, Pi.one_apply]
  rw [finprod_congr hv, finprod_ite _ ?_]
  · rw [Set.indicator_apply]
    by_cases hq : q ∈ boxS D
    · rw [if_pos hq, if_pos (fun v c => hq c v)]
      rfl
    · rw [if_neg hq, if_neg (fun h' => hq (fun c v => h' v c))]
  · filter_upwards [hD.2, eventually_all.2 fun c => (q c).eventually] with v h1 h2 c
    rw [h1 c]
    exact h2 c

end admitted

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {a M : ℕ}

variable (F E a M) in

def psiH : (Fin a → Fin M → AF F ⊗[F] E) ≃ₜ
    (Fin a × Fin M × Fin (Module.finrank F E) → Ainf F) ×
      (Fin a × Fin M × Fin (Module.finrank F E) → Af F) :=
  (crdH (Module.finBasis F E) (AF F)).trans (splitH F _)

theorem psiH_fst (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).1 = crdH (Module.finBasis F E) (Ainf F) (projInf X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (fstA F) (X c.1 c.2.1) c.2.2).symm

theorem psiH_snd (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).2 = crdH (Module.finBasis F E) (Af F) (projFin X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (sndA F) (X c.1 c.2.1) c.2.2).symm

theorem key_int (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2)
    {D : Fin a × Fin M × Fin (Module.finrank F E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (f : C_c(Fin a × Fin M × Fin (Module.finrank F E) → Ainf F, ℝ)) :
    ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν1 =
      ∫ X, f (psiH F E a M X).1 * (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 ∂ν2 := by
  classical
  let b := Module.finBasis F E
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f (crdH b (Ainf F) Y) : ℝ) : ℂ)
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (locBox b D v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun W => ∏ᶠ v, Φv v (projV v W)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hadm : IsAdm F E Φ := by
    refine ⟨_, b, Φinf, Φf, Φv, ?_, ?_, ⟨fun v => isSB_locBox hD v, ?_, fun _ => rfl⟩, fun _ => rfl⟩
    · exact Complex.continuous_ofReal.comp (f.continuous.comp (crdH b (Ainf F)).continuous)
    · exact (f.hasCompactSupport.comp_homeomorph (crdH b (Ainf F))).comp_left Complex.ofReal_zero
    · filter_upwards [hD.2] with v hv
      exact congrArg (fun s => s.indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) (locBox_eq_latV v hv)
  have hΦ : ∀ X, Φ X = ((f (psiH F E a M X).1 *
      (boxS D).indicator (fun _ => (1 : ℝ)) (psiH F E a M X).2 : ℝ) : ℂ) := by
    intro X
    have e2 : Φf (projFin X) = (boxS D).indicator 1 ((psiH F E a M X).2) := by
      rw [psiH_snd]
      exact finprod_locBox hD (projFin X)
    simp only [Φ, e2, psiH_fst, Φinf, b]
    rw [Complex.ofReal_mul]
    congr 1
    by_cases hq : (psiH F E a M X).2 ∈ boxS D
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      simp
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
      simp
  have := h Φ hadm
  simp only [hΦ] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this

end Main

end PI.VolStabS.DeterminantAdmissible
end
end

section
noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabS
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

theorem detAdm_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH F E a M
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU

end PI.VolStabS.DeterminantAdmissible

namespace PI.VolStabS

theorem detAdm_holds : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h

end PI.VolStabS
end
end
