import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by
  intro G X _ _ _ _ r h1 hmul hc Φ
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  obtain ⟨hlc, hcs⟩ := hΦ
  have hA : IsLocallyConstant (fun z : G × X => Φ.1 (r z.2 z.1)) :=
    hlc.comp_continuous (hc.comp continuous_swap)
  have hB : IsLocallyConstant (fun z : G × X => Φ.1 z.2) :=
    hlc.comp_continuous continuous_snd
  have key : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun u x => Φ.1 (r x u) = Φ.1 x) hcs ?_
    intro y _
    filter_upwards [hA.eventually_eq ((1 : G), y), hB.eventually_eq ((1 : G), y)] with z hz hz'
    rw [hz, hz']
    simp only [h1]
  have key' : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u⁻¹) = Φ.1 x := by
    have ht : Filter.Tendsto (fun u : G => u⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact ht.eventually key
  filter_upwards [key, key'] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ.1
  · exact hu x hx
  · by_cases hy : r x u ∈ tsupport Φ.1
    · have := hu' _ hy
      rw [← hmul, mul_inv_cancel, h1] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter

namespace GlobalTheory.SBInduced

variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]

omit [IsTopologicalGroup G] in

theorem isClosedEmbedding_translate (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) (g : G) : IsClosedEmbedding fun y => r (j y) g := by
  have hc' : ∀ g, Continuous fun x => r x g := fun g => hc.comp (Continuous.prodMk_left g)
  let e : X ≃ₜ X :=
    { toFun := fun x => r x g
      invFun := fun x => r x g⁻¹
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := hc' g
      continuous_invFun := hc' g⁻¹ }
  exact e.isClosedEmbedding.comp hj

theorem isQuotientMap_sweep (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : X × K ≃ₜ X × K :=
    { toFun := fun p => (r p.1 p.2, p.2)
      invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2)
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
        continuous_snd
      continuous_invFun := (hc.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd }
  have hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2 :=
    (isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp
      (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)
  refine hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))) fun x => ?_
  obtain ⟨y, c, hc, rfl⟩ := hs x
  exact ⟨(y, ⟨c, hc⟩), rfl⟩

theorem descend [T2Space X] (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) (H : G → SB Y)
    (hU : ∀ᶠ u in 𝓝 (1 : G), ∀ g, H (g * u) = H g)
    (hfib : ∀ y g y' g', r (j y) g = r (j y') g' → (H g).1 y = (H g').1 y') :
    ∃ Φ : SB X, ∀ g y, Φ.1 (r (j y) g) = (H g).1 y := by
  have hq := isQuotientMap_sweep r h1 hm hc hj hK hs
  choose y c hcK hx using hs
  let φ : X → ℂ := fun x => (H (c x)).1 (y x)
  have hφ : ∀ g z, φ (r (j z) g) = (H g).1 z := fun g z => hfib _ _ _ _ (hx _).symm
  have hnear : ∀ g : G, ∀ᶠ z in 𝓝 g, H z = H g := fun g => by
    have hc : Tendsto (fun z : G => g⁻¹ * z) (𝓝 g) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually hU).mono fun z hz => by simpa using hz g
  have hlc : IsLocallyConstant fun p : Y × G => (H p.2).1 p.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    filter_upwards [(continuous_snd.tendsto p).eventually (hnear p.2),
      (continuous_fst.tendsto p).eventually ((H p.2).2.1.eventually_eq p.1)] with z h₁ h₂
    rw [h₁, h₂]
  refine ⟨⟨φ, fun s => ?_, ?_⟩, hφ⟩
  · rw [← hq.isOpen_preimage]
    have := (hlc.comp_continuous (f := fun p : Y × K => (p.1, (p.2 : G)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) s
    convert this using 1
    ext p
    simp only [Set.mem_preimage, hφ, Function.comp_apply]
  · obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | H z = H x}) fun x _ => hnear x
    have hC : IsCompact (⋃ g ∈ t, tsupport (H g).1) :=
      t.isCompact_biUnion fun g _ => (H g).2.2
    refine HasCompactSupport.intro (((hC.image hj.continuous).prod hK).image hc) fun x hxn => ?_
    by_contra h0
    apply hxn
    obtain ⟨g, hg, hcg⟩ := Set.mem_iUnion₂.1 (ht (hcK x))
    refine ⟨(j (y x), c x), ⟨⟨y x, Set.mem_iUnion₂.2 ⟨g, hg, subset_tsupport _ ?_⟩, rfl⟩, hcK x⟩,
      (hx x).symm⟩
    rw [← show H (c x) = H g from hcg]
    exact h0

theorem sb_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  intro G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev
  have hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1 := IsOpen.mem_nhds hχ (one_mem χ.ker)
  have hce := isClosedEmbedding_translate r h1 hm hc hj
  let A : SB X → G → SB Y := fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g),
    Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩
  have hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun _ _ _ => rfl
  have hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w' := fun w w' h =>
    ev.injective (Subtype.ext (funext h))
  let T : SB X →ₗ[ℂ] smoothPart (ind P σ) :=
    { toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by
          rw [hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul,
            mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'
          refine Subtype.ext (funext fun g => ?_)
          show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)
          congr 1
          refine Subtype.ext (funext fun y => ?_)
          rw [hA, hA, map_mul, hu, mul_one, hm, hu'])⟩
      map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)
        rw [← map_add]
        congr 1
        exact Subtype.ext (funext fun y => mul_add _ _ _)))
      map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)
        rw [← map_smul]
        congr 1
        exact Subtype.ext (funext fun y => mul_left_comm _ _ _))) }
  have hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun Φ g y => by
    show (ev (ev.symm (A Φ g))).1 y = _
    rw [ev.apply_symm_apply, hA]
  have hinj : Function.Injective T := fun Φ Ψ h => Subtype.ext (funext fun x => by
    obtain ⟨y, c, -, rfl⟩ := hs x
    have := hT Φ c y
    rw [h, hT] at this
    exact (mul_left_cancel₀ (χ c).ne_zero this).symm)
  have hsurj : Function.Surjective T := fun F => by
    have hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x =>
        congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x
    obtain ⟨Φ, hΦ⟩ := descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g))
      (by
        filter_upwards [hχ', hF] with u hu hu' g
        rw [hu', map_mul, hu, mul_one])
      (fun y g y' g' h => by
        have h2 : r (j y) (g * g'⁻¹) = j y' := by rw [hm, h, ← hm, mul_inv_cancel, h1]
        have hp := hP _ _ _ h2
        have h3 : s y ⟨_, hp⟩ = y' := hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)
        have h4 := F.1.2 ⟨_, hp⟩ g'
        rw [show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g'] at h4
        show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'
        rw [h4, hev, h3]
        simp [← mul_assoc])
    refine ⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩
    rw [hT, hΦ]
    exact mul_inv_cancel_left₀ (χ g).ne_zero _
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

end GlobalTheory.SBInduced
end
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
end

section
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl

end GlobalTheory
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  atlas_forward_decl GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank
end

section
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

open Matrix Topology Module in

theorem _root_.GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  intro k m a b n _ _ _ _ _ e x hx hz v hv
  classical
  set x' := x.submatrix id (fun i => e (Sum.inl i))
  let Q : Matrix n a k := Matrix.of fun l i => if l = e (Sum.inl i) then 1 else 0
  let P : Matrix a n k := Matrix.of fun i l => if l = e (Sum.inl i) then 1 else 0
  have hQ : x' = x * Q := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [x', Q, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hP : x = x' * P := by
    ext i l
    obtain ⟨t, rfl⟩ := e.surjective l
    rcases t with t | t
    · rw [Matrix.mul_apply]
      simp only [x', P, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · rw [Matrix.mul_apply]
      simp [x', P, hz]
  have hr : x'.rank = Fintype.card a := by
    apply le_antisymm
    · rw [← hx, hQ]; exact Matrix.rank_mul_le_left _ _
    · rw [← hx, hP]; exact Matrix.rank_mul_le_left _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker x'.mulVecLin
  have hxr : finrank k (LinearMap.range x'.mulVecLin) = Fintype.card a := hr
  rw [hxr, finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker x'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hvk : v ∈ LinearMap.ker x'.mulVecLin := hv
  rw [hker] at hvk
  exact (Submodule.mem_bot k).1 hvk

end GlobalTheory
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  atlas_forward_decl GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] [DecidableEq b] in

theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ

omit [DecidableEq a] [DecidableEq b] in

theorem isClosed_rank_lt (κ : ℕ) : IsClosed {x : Matrix b a k | x.rank < κ} := by
  have := (isOpen_le_rank (k := k) (a := a) (b := b) κ).isClosed_compl
  simpa only [Set.compl_ofPred, not_le] using this

omit [DecidableEq a] [DecidableEq b] in

theorem exists_extend_rankIn {s : Set ℕ} {κ n : ℕ} (hs : ∀ r ∈ s, κ ≤ r ∧ r < n) (f : SB (RankIn k a b s)) :
    ∃ F : SB (RankIn k a b (Set.Iio n)), (∀ x : RankIn k a b (Set.Iio n), x.1.rank < κ → F.1 x = 0) ∧
      ∀ x : RankIn k a b s, F.1 ⟨x.1, (hs _ x.2).2⟩ = f.1 x := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix b a k) :=
    inferInstanceAs (TotallyDisconnectedSpace (b → a → k))
  have : LocallyCompactSpace (Matrix b a k) := inferInstanceAs (LocallyCompactSpace (b → a → k))
  obtain ⟨G, hG, hG0⟩ := GlobalTheory.SBExtend.exists_extension (Matrix b a k) {x | κ ≤ x.rank} {x | x.rank ∈ s} (isOpen_le_rank κ)
    (fun x hx => (hs _ hx).1) f
  refine ⟨⟨fun y => G.1 y.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal G (isClosed_rank_lt n)
    (fun y => y.2) fun x hx _ => ⟨⟨x, hx⟩, rfl⟩⟩, fun x hx => hG0 _ (not_le.2 hx), fun x => hG x⟩

def resFilt (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) :
    (filt a b μ (Set.Iio n) κ).toRepresentation.IntertwiningMap (omegaOn a b μ s) where
  toFun Φ := ⟨fun x => Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩,
    comp_mem_SB_of_isInducing
      (i := fun x : RankIn k a b s => (⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ : RankIn k a b (Set.Iio n)))
      (IsInducing.subtypeVal.of_comp_iff.1 IsInducing.subtypeVal) Φ.1
      ((isClosed_rank_lt m).preimage continuous_subtype_val) (fun y => ((hs _).1 y.2).2)
      fun x hx h0 => ⟨⟨x.1, (hs _).2 ⟨not_lt.1 fun h => h0 (Φ.2 x h), hx⟩⟩, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl


theorem resFilt_surjective (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) : Function.Surjective (resFilt (a := a) (b := b) μ hmn hs) := by
  intro f
  obtain ⟨F, h0, hF⟩ := exists_extend_rankIn (κ := κ) (n := n)
    (fun r hr => ⟨((hs r).1 hr).1, ((hs r).1 hr).2.trans_le hmn⟩) f
  exact ⟨⟨F, h0⟩, Subtype.ext (funext hF)⟩

theorem ker_resFilt (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) :
    resFilt μ hmn hs Φ = 0 ↔ Φ.1 ∈ (filt a b μ (Set.Iio n) m).toSubmodule := by
  constructor
  · intro h x hx
    by_cases hκ : x.1.rank < κ
    · exact Φ.2 x hκ
    · exact congrFun (congrArg Subtype.val h) ⟨x.1, (hs _).2 ⟨not_lt.1 hκ, hx⟩⟩
  · intro h
    exact Subtype.ext (funext fun x => h _ ((hs _).1 x.2).2)

end


end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct

namespace GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lower

variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype b] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [DecidableEq d] in

theorem _root_.GlobalTheory.RankStrataProof.mul_apply_of_cols {n : Type} (e : c ⊕ d ≃ a) {x : Matrix b a k} (hx : ∀ i j, x i (e (.inr j)) = 0)
    (g : Matrix a n k) (i : b) (l : n) : (x * g) i l = ∑ m, x i (e (.inl m)) * g (e (.inl m)) l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [hx]

def rAct (s : Set ℕ) (x : RankIn k a b s) (g : GL a k) : RankIn k a b s :=
  ⟨act x.1 (g, 1), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL a k) : (_root_.GlobalTheory.RankStrataProof.rAct s x g).1 = x.1 * g.val := by
  unfold _root_.GlobalTheory.RankStrataProof.rAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.rAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL a k) :
    _root_.GlobalTheory.RankStrataProof.rAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.rAct s (_root_.GlobalTheory.RankStrataProof.rAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, Units.val_mul, Matrix.mul_assoc]

theorem continuous_rAct (s : Set ℕ) : Continuous fun p : RankIn k a b s × GL a k => rAct s p.1 p.2 := by
  refine Continuous.subtype_mk (f := fun p : RankIn k a b s × GL a k => act p.1.1 (p.2, 1)) ?_ _
  exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_fst)).matrix_mul
    (Units.continuous_val.comp continuous_snd)

variable (k b) in

abbrev ColZero (e : c ⊕ d ≃ a) (s : Set ℕ) : Type :=
  {x : RankIn k a b s // ∀ i j, x.1 i (e (.inr j)) = 0}

def pAct (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) : ColZero k b e s :=
  ⟨rAct s y.1 p, fun i j => by
    rw [rAct_val, mul_apply_of_cols e y.2]
    simp [(mem_parabLower_two k).1 p.2]⟩

def fstBlock (e : c ⊕ d ≃ a) : GL c k →* parabLower k (two e) :=
  ((emb₂ k e).codRestrict _ fun _ => leviEmb_mem_parabLower k _ _).comp (MonoidHom.inl _ _)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pAct_eq (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) :
    pAct e s y (fstBlock e (leviProjLower k (two e) p false)) = pAct e s y p := by
  refine Subtype.ext (Subtype.ext ?_)
  ext i l
  obtain ⟨l | l, rfl⟩ := e.surjective l
  · show (rAct s y.1 _).1 _ _ = (rAct s y.1 _).1 _ _
    rw [rAct_val, rAct_val, mul_apply_of_cols e y.2, mul_apply_of_cols e y.2]
    refine Finset.sum_congr rfl fun m _ => congrArg _ ?_
    exact leviEmb_apply_same k (two e) _ false m l
  · exact ((pAct e s y _).2 i l).trans ((pAct e s y _).2 i l).symm

variable (b) in

def colRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ν : kˣ →* ℂˣ) :
    Representation ℂ (GL c k) (SB (ColZero k b e s)) :=
  twist (sbRep (fun y g => pAct e s y (fstBlock e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (fun g => ((continuous_rAct s).comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _))
    (detChar c ν)

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.isSmoothChar_omChar {μ : kˣ →* ℂˣ} (hμ : _root_.GlobalTheory.SmGL.IsSmoothChar μ) : _root_.GlobalTheory.SmGL.IsSmoothChar (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar a b μ) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar
  apply _root_.GlobalTheory.SmGL.IsSmoothChar.mul
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_fst
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul
      (_root_.GlobalTheory.SmGL.IsSmoothChar.inv hμ)
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_snd
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul hμ
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))

theorem lower (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (z : ℂ) (hz : z + (Fintype.card c : ℂ) / 2 = (Fintype.card b : ℂ) / 2) :
    Nonempty (Representation.Equiv ((omegaOn a b μ {κ}).comp (MonoidHom.inl _ _))
      (ind₂Lower e (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))))) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hcl : IsClosed {x : RankIn k a b {κ} | ∀ i j, x.1 i (e (.inr j)) = 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL a k) (RankIn k a b {κ}) (ColZero k b e {κ})
    (SB (ColZero k b e {κ}) ⊗[ℂ] ℂ) (rAct {κ}) (rAct_one _) (rAct_mul _) (continuous_rAct _)
    Subtype.val hcl.isClosedEmbedding_subtypeVal (parabLower k (two e)) (KO k a) SplitFlip.isCompact_KO
    (fun x => by
      obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k b c d a e x.1 (x.2.trans hκ)
      obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k a (fun i => (!blk (two e) i).toNat) g⁻¹
      have hp' : p ∈ parabLower k (two e) := (mem_parabLower_two k).2 fun i j => hp (by
        rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
      refine ⟨pAct e _ ⟨rAct _ x g, by rwa [rAct_val]⟩ ⟨p, hp'⟩, w, hw, ?_⟩
      show x = rAct _ (rAct _ (rAct _ x g) p) w
      rw [← rAct_mul, ← rAct_mul, ← h, mul_inv_cancel, rAct_one])
    (pAct e _) (fun _ _ => rfl)
    (fun y y' g h => (mem_parabLower_two k).2 fun i j => by
      refine congrFun (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e y.1.1 (y.1.2.trans hκ) y.2
        (fun m => g.val (e (.inl m)) (e (.inr j))) (funext fun l => ?_)) i
      have := y'.2 l j
      rw [← h, rAct_val, mul_apply_of_cols e y.2] at this
      exact this)
    ((omChar a b μ).comp (MonoidHom.inl _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_id.prodMk continuous_const))
    ((twist (MonoidHom.comp (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))) (leviTwo k c d).symm.toMonoidHom) (deltaHalf k (Two c d))⁻¹).comp
        (leviProjLower k (two e)))
    (TensorProduct.rid ℂ _)
    (fun p w y => by
      obtain ⟨φ, rfl⟩ := (TensorProduct.rid ℂ _).symm.surjective w
      set m := leviProjLower k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL a k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) := by
        have := det_parab k (opp (two e)) p
        rw [this]
        exact (Fintype.prod_bool _).trans (mul_comm _ _)
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      rw [LinearEquiv.apply_symm_apply, TensorProduct.rid_symm_apply]
      show (TensorProduct.rid ℂ _ ((((deltaHalf k (Two c d) m)⁻¹ : ℂˣ) : ℂ) •
        extTensor _ _ (m false, m true) (φ ⊗ₜ 1))).1 y = _
      rw [extTensor_tmul, map_smul, TensorProduct.rid_tmul]
      show (((deltaHalf k (Two c d) m)⁻¹ : ℂˣ) : ℂ) * (detRep d _ (m true) 1 *
        ((detChar c _ (m false) : ℂ) * φ.1 (pAct e _ y (fstBlock e (m false))))) = _
      rw [pAct_eq, ← mul_assoc, ← mul_assoc, detRep, ofChar_apply, mul_one, ← Units.val_mul, ← Units.val_mul]
      congr 2
      rw [hδ]
      simp only [omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply, MonoidHom.inl_apply,
        MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, mul_one, hd, map_mul, neg_div, absPow_neg,
        MonoidHom.inv_apply]
      have h1 := DFunLike.congr_fun (absPow_add k z ((Fintype.card c : ℂ) / 2))
        (GeneralLinearGroup.det (m true))
      rw [hz] at h1
      rw [h1, absPow_add]
      simp only [MonoidHom.mul_apply, mul_inv, inv_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
  refine (TensorProduct.rid ℂ _).injective (Subtype.ext (funext fun y => ?_))
  refine (hE _ x y).trans (Eq.trans ?_ (hE Φ (x * g) y).symm)
  rw [map_mul, rAct_mul, Units.val_mul, mul_assoc]
  rfl

end Lower

section Open

variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

theorem isLocallyConstant_char {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) : IsLocallyConstant fun y => (ψ y : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set G)) := IsOpen.preimage (by fun_prop) h
  filter_upwards [this.mem_nhds (show x ∈ _ by simp)] with y hy
  have hy' : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at hy'
  rw [hy']

def divChar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) : SB G ≃ₗ[ℂ] SB G where
  toFun w := ⟨fun y => (ψ⁻¹ y : ℂ) * w.1 y, (isLocallyConstant_char h.inv).mul w.2.1, w.2.2.mul_left⟩
  invFun w := ⟨fun y => (ψ y : ℂ) * w.1 y, (isLocallyConstant_char h).mul w.2.1, w.2.2.mul_left⟩
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => mul_left_comm _ _ _)
  left_inv w := Subtype.ext (funext fun y => by simp)
  right_inv w := Subtype.ext (funext fun y => by simp)

def topM (e : a ⊕ c ≃ b) (y : Matrix a a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype c] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype a] [Fintype b] in
@[simp] theorem topM_inl (e : a ⊕ c ≃ b) (y : Matrix a a k) (i l : a) : topM e y (e (.inl i)) l = y i l := by
  simp [topM]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype c] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype a] [Fintype b] in
@[simp] theorem topM_inr (e : a ⊕ c ≃ b) (y : Matrix a a k) (i : c) (l : a) :
    topM e y (e (.inr i)) l = 0 := by
  simp [topM]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] in
theorem mul_topM (e : a ⊕ c ≃ b) (g : Matrix b b k) (y : Matrix a a k) (i : b) (l : a) :
    (g * topM e y) i l = ∑ m, g i (e (.inl m)) * y m l := by
  rw [mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype c] [Fintype b] in
theorem topM_mul (e : a ⊕ c ≃ b) (y g : Matrix a a k) : topM e (y * g) = topM e y * g := by
  ext i l
  obtain ⟨i | i, rfl⟩ := e.surjective i <;> simp [mul_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq b] [DecidableEq c] in
theorem rank_topM (e : a ⊕ c ≃ b) (y : GL a k) : (topM e y.val).rank = Fintype.card a := by
  refine le_antisymm (rank_le_card_width _) ?_
  have h : (topM e y.val).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y.val := by
    ext i l; simp
  have h2 := rank_submatrix_le (topM e y.val) (fun i => e (.inl i)) (Equiv.refl a)
  rwa [h, rank_of_isUnit _ y.isUnit] at h2

def lAct (s : Set ℕ) (x : RankIn k a b s) (h : GL b k) : RankIn k a b s :=
  ⟨act x.1 (1, h), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL b k) : (_root_.GlobalTheory.RankStrataProof.lAct s x g).1 = (g⁻¹).val * x.1 := by
  unfold _root_.GlobalTheory.RankStrataProof.lAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.lAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL b k) :
    _root_.GlobalTheory.RankStrataProof.lAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.lAct s (_root_.GlobalTheory.RankStrataProof.lAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
theorem _root_.GlobalTheory.RankStrataProof.continuous_lAct (s : Set ℕ) : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => _root_.GlobalTheory.RankStrataProof.lAct s p.1 p.2 := by
  have h : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => ((p.2⁻¹ : GL b k) : Matrix b b k) * p.1.1 :=
    (Units.continuous_val.comp (continuous_inv.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  refine Continuous.subtype_mk (h.congr fun p => (_root_.GlobalTheory.RankStrataProof.lAct_val s p.1 p.2).symm) _

end Open

end GlobalTheory.RankStrataProof
end
end
