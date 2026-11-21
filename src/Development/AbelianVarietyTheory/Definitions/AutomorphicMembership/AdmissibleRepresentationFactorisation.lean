import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SimilitudesCorrespond
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack lowerCoeff levelMapF endF relGroup trivAt)

namespace GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l₂ : Level H}

def CxPt (Xo : Moduli Dw l) (c : Coeff l) : Type :=
  {y : Sp ℂ ⟶ Xo.XF c // y ≫ pullback.snd _ _ = spMap c.F.val.toRingHom}

def LiesOver (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}
    (y₂ : CxPt Xo₂ c₂) (y : CxPt Xo c) : Prop :=
  ∃ π : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π ∧ PullsBack Xo Xo₂ π ∧
    y₂.1 ≫ pullback.fst _ _ ≫ π = y.1 ≫ pullback.fst _ _

open Classical in

def levDeg (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) : ℕ :=
  if k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n then Nat.find k else 1

theorem levDeg_pos (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) :
    0 < levDeg h Xo c Xo₂ c₂ := by
  classical
  unfold levDeg
  split_ifs with k
  · exact (Nat.find_spec k).1
  · exact one_pos

theorem card_lifts_pos {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] [Surjective π]
    (y : Sp k ⟶ Y) : 0 < Nat.card {x : Sp k ⟶ X // x ≫ π = y} := by
  have hne : Nonempty {x : Sp k ⟶ X // x ≫ π = y} := by
    have : CompactSpace ↥(pullback π y) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π y)
    obtain ⟨p, -⟩ := (pullback.snd π y).surjective (default : PrimeSpectrum k)
    obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π y)) ⟨p, trivial⟩
    refine ⟨pointOfClosedPoint (pullback.snd π y) q hq ≫ pullback.fst π y, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  have hfin : Finite {x : Sp k ⟶ X // x ≫ π = y} := by
    have hf := (pullback.snd π y).finite_preimage_singleton (IsLocalRing.closedPoint k)
    have := hf.to_subtype
    let s : {x : Sp k ⟶ X // x ≫ π = y} → (Sp k ⟶ pullback π y) := fun x =>
      pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm)
    refine Finite.of_injective (β := (pullback.snd π y) ⁻¹' {IsLocalRing.closedPoint k})
      (fun x => ⟨s x (IsLocalRing.closedPoint k), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩) fun a b e => ?_
    have e' : s a = s b := ext_of_apply_closedPoint_eq (pullback.snd π y) (pullback.lift_snd _ _ _)
      (pullback.lift_snd _ _ _) (congrArg Subtype.val e)
    exact Subtype.ext ((pullback.lift_fst _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π y) e').trans
      (pullback.lift_fst _ _ _)))
  exact Nat.card_pos

theorem card_liesOver_eq_index (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    0 < Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ∧
      Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)).index := by
  obtain ⟨π, hπ, hpb, huniq, ρ, hρ, hone, hmul, -, hρπ, hcov⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l₂ h Xo Xo₂
  obtain ⟨k₁, -, k₃, k₄⟩ := hcov c₂
  have w : (y.1 ≫ pullback.fst _ _) ≫ Xo.s =
      spMap c₂.F.val.toRingHom ≫ spMap (IntermediateField.inclusion (lowerCoeff h c₂).le).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let y' : Sp ℂ ⟶ Xo.XF (lowerCoeff h c₂) := pullback.lift _ _ w
  have hf : levelMapF h hπ c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hs := GlobalTheory.LevelCompare.levelMapF_snd h hπ c₂
  let e : {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ≃ {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} :=
    { toFun := fun a => ⟨a.1.1, by
        obtain ⟨π', a₁, a₂, a₃⟩ := a.2
        obtain rfl := huniq π' a₁ a₂
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hf, a₃]; exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hs]; exact a.1.2.trans (pullback.lift_snd _ _ _).symm⟩
      invFun := fun x => ⟨⟨x.1, (congrArg (x.1 ≫ ·) hs.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pullback.snd _ _) x.2).trans (pullback.lift_snd _ _ _)))⟩, π, hπ, hpb, by
        change x.1 ≫ _ = _
        rw [← hf, ← Category.assoc, x.2]; exact pullback.lift_fst _ _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpos := card_lifts_pos (levelMapF h hπ c₂) y'
  rw [Nat.card_congr e]
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hF : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ρ g).hom := fun g =>
    pullback.lift_fst _ _ _
  have hS : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.snd _ _ = pullback.snd _ _ := fun g => pullback.lift_snd _ _ _
  have hm : ∀ g g', endF (ρ (g * g')).hom (hρ _) c₂ = endF (ρ g).hom (hρ g) c₂ ≫ endF (ρ g').hom (hρ g') c₂ :=
    fun g g' => pullback.hom_ext (by rw [hF, Category.assoc, hF, ← Category.assoc, hF, hmul, Category.assoc]; rfl)
      (by rw [hS, Category.assoc, hS, hS])
  have h1 : endF (ρ 1).hom (hρ _) c₂ = 𝟙 _ :=
    pullback.hom_ext (by rw [hF, hone, Category.id_comp]; exact Category.comp_id _) (by rw [hS, Category.id_comp])
  let f : relGroup Dw l l₂ → {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} := fun g =>
    ⟨x ≫ endF (ρ g).hom (hρ g) c₂, by
      rw [← hx, Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hf, ← Category.assoc, hF, Category.assoc, hρπ]
      · rw [Category.assoc, hs]; exact hS g⟩
  have hsurj : Function.Surjective f := fun a => by
    obtain ⟨g, hg⟩ := (k₄ ℂ x).1 a.1 (a.2.trans hx.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hker : Setoid.ker f = QuotientGroup.rightRel ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)) := by
    ext g g'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, ← (k₄ ℂ x).2, Setoid.ker_def, Subtype.ext_iff, hm]
    change x ≫ _ = x ≫ _ ↔ _
    constructor
    · intro a
      rw [← Category.assoc, ← a, Category.assoc, ← hm, mul_inv_cancel, h1, Category.comp_id]
    · intro a
      have := congrArg (· ≫ endF (ρ g).hom (hρ g) c₂) a
      simp only [Category.assoc] at this
      rw [← hm, inv_mul_cancel, h1, Category.comp_id] at this
      exact this.symm
  rw [← Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj), hker,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rfl

theorem card_liesOver (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = levDeg h Xo c Xo₂ c₂ := by
  classical
  have k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n :=
    ⟨_, (card_liesOver_eq_index hpq h Xo₂ c₂ y).1, fun y' =>
      (card_liesOver_eq_index hpq h Xo₂ c₂ y').2.trans (card_liesOver_eq_index hpq h Xo₂ c₂ y).2.symm⟩
  rw [levDeg, dif_pos k]
  exact (Nat.find_spec k).2 y

end GlobalTheory.ShFam.Pad
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open GlobalTheory.CechPic (cls tens dual)

namespace GlobalTheory.ShFam.Pad

abbrev FibCrv (p : ℕ) (X : Scheme.{0}) : Type :=
  {C : Closeds X // IsIrreducible (C : Set X) ∧ topologicalKrullDim (C : Set X) = 1 ∧
    ∀ x ∈ C, (p : X.residueField x) = 0}

namespace FibCrv

variable {p : ℕ} {X : Scheme.{0}} (c : FibCrv p X)

abbrev sch : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal c.1).subscheme

abbrev ι : c.sch ⟶ X := redι c.1

instance isIntegral : IsIntegral c.sch := isIntegral_red c.2.1

theorem dim_sch : topologicalKrullDim c.sch = 1 := (topologicalKrullDim_red c.1).trans c.2.2.1

theorem natCast_eq_zero : (p : Γ(c.sch, ⊤)) = 0 := by
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  refine absurd hy ((c.sch.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) y trivial _).1 ?_)
  rw [map_natCast, ← map_natCast (c.ι.residueFieldMap y).hom, c.2.2.2 _ ((range_redι c.1).le ⟨y, rfl⟩), map_zero]

instance algebra : Algebra (ZMod p) Γ(c.sch, ⊤) := ZMod.algebra' _ (ringChar _) (ringChar.dvd c.natCast_eq_zero)

def ofImm {C : Scheme.{0}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] (hd : topologicalKrullDim C = 1)
    (hp : (p : Γ(C, ⊤)) = 0) : FibCrv p X :=
  ⟨⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩,
    by simpa using (IrreducibleSpace.isIrreducible_univ C).image i i.continuous.continuousOn,
    (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding rfl).trans hd, by
      rintro _ ⟨y, rfl⟩
      apply (i.residueFieldMap y).hom.injective
      rw [map_natCast, map_zero, ← map_natCast (C.Γevaluation y).hom, hp, map_zero]⟩

variable [Fact p.Prime] {L M N H : LB X}

def deg (L : LB X) : ℤ := interNumRed (ZMod p) (⊤ : Closeds c.sch) ![L.pull c.ι]

abbrev str : c.sch ⟶ Sp (ZMod p) := strHom (ZMod p) c.sch

theorem deg_eq_of_imm {C : Scheme.{0}} [Algebra (ZMod p) Γ(C, ⊤)] (i : C ⟶ X) [IsClosedImmersion i] [IsReduced C]
    (h : Set.range i = c.1) (hL : L.IsLB) : c.deg L = interNum (ZMod p) (structureModule C) ![L.pull i] := by
  have e : Scheme.IdealSheafData.vanishingIdeal c.1 = i.ker := by
    rw [← InterModel.radical_ker i, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, h, c.1.isClosed.closure_eq]
  let j : C ⟶ c.sch := IsClosedImmersion.lift c.ι i (by rw [← e]; simp)
  have hj : j ≫ c.ι = i := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j ≫ c.ι) := hj ▸ inferInstance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j c.ι
  have hr : Set.range j = (⊤ : Closeds c.sch) := Set.eq_univ_of_forall fun y => by
    obtain ⟨x, hx⟩ := h.ge ((range_redι c.1).le ⟨y, rfl⟩)
    exact ⟨x, c.ι.isClosedEmbedding.injective (by rw [← hx, ← hj]; rfl)⟩
  have hL' := LB.isLB_pull hL c.ι
  rw [deg, InterModel.interNumRed_eq_interNumOn (ZMod p) j ⊤ hr, interNumOn_eq_interNum_pull (fun r =>
    RingHom.congr_fun (RingHom.ext_zmod (j.appTop.hom.comp (algebraMap _ _)) (algebraMap _ _)) r) (isLB_vecOne hL')]
  refine interNum_congr_cls _ _ (fun a => LB.isLB_pull (isLB_vecOne hL' a) j) (isLB_vecOne (LB.isLB_pull hL i)) fun a => ?_
  fin_cases a
  exact ((CechPic.pull_comp j c.ι (cls L hL)).symm.trans (by rw [hj])).trans (CechPic.cls_pull hL i _).symm

theorem isProper_str {O : Type} [CommRing O] [Finite (O ⧸ Ideal.span {(p : O)})] (s : X ⟶ Sp O) [IsProper s] :
    IsProper c.str := by
  let φ : O →+* Γ(c.sch, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ (c.ι ≫ s).appTop).hom
  let ψ : O ⧸ Ideal.span {(p : O)} →+* Γ(c.sch, ⊤) := Ideal.Quotient.lift _ φ fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_natCast, c.natCast_eq_zero, mul_zero]
  letI : Algebra (ZMod p) (O ⧸ Ideal.span {(p : O)}) := ZMod.algebra' _ (ringChar _) (ringChar.dvd (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _))
  let g : c.sch ⟶ Sp (O ⧸ Ideal.span {(p : O)}) := c.sch.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have h₁ : g ≫ spMap (Ideal.Quotient.mk _) = c.ι ≫ s := by
    have e : CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(p : O)})) ≫ CommRingCat.ofHom ψ =
        (Scheme.ΓSpecIso (.of O)).inv ≫ (c.ι ≫ s).appTop := rfl
    refine (Category.assoc _ _ _).trans ((congrArg (c.sch.toSpecΓ ≫ ·)
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map e))).trans ?_)
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h₂ : c.str = g ≫ spMap (algebraMap (ZMod p) _) :=
    ((Category.assoc _ _ _).trans (congrArg (c.sch.toSpecΓ ≫ ·) ((Spec.map_comp _ _).symm.trans
      (congrArg (fun f => Spec.map (CommRingCat.ofHom f))
        (RingHom.ext_zmod (ψ.comp (algebraMap (ZMod p) _)) (algebraMap _ _)))))).symm
  have : IsProper (g ≫ spMap (Ideal.Quotient.mk _)) := h₁ ▸ inferInstance
  have : IsProper g := IsProper.of_comp g (spMap (Ideal.Quotient.mk _))
  have : IsFinite (spMap (algebraMap (ZMod p) (O ⧸ Ideal.span {(p : O)}))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 Module.Finite.of_finite)
  rw [h₂]
  infer_instance

variable [IsProper c.str]

theorem isCompleteCurve_top : IsCompleteCurve (ZMod p) (⊤ : Closeds c.sch) :=
  (isCompleteCurve_iff (algebraMap_eq_strHom (ZMod p) c.sch)).2 ⟨IrreducibleSpace.isIrreducible_univ _,
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans c.dim_sch⟩

theorem deg_of_cls_eq_add (hH : IsAmpleLB H) (hN : N.IsLB) (hL : L.IsLB) (hM : M.IsLB)
    (e : cls N hN = cls L hL + cls M hM) : c.deg N = c.deg L + c.deg M :=
  c.isCompleteCurve_top.interNumRed_of_cls_eq_add (hH.pull_of_isClosedImmersion c.ι) (LB.isLB_pull hN _)
    (LB.isLB_pull hL _) (LB.isLB_pull hM _)
    (by rw [CechPic.cls_pull hN, CechPic.cls_pull hL, CechPic.cls_pull hM, e, map_add])

end FibCrv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev Crv (z : admitted Y i₀) : Type := FibCrv p z.Z.X

def cov (z : admitted Y i₀) : ℕ := levDeg z.Z.dvd (Xo i₀.l) i₀.c (Xo z.Z.i.l) z.Z.i.c

theorem cov_pos (z : admitted Y i₀) : 0 < cov z := levDeg_pos _ _ _ _ _

theorem natCast_mem_nonunits {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp)
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_comap] at h'
    simpa using h'

theorem natCast_eq_zero_iff (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : LocM.Mdl Y i₀) (x : Z.X) :
    (p : Z.X.residueField x) = 0 ↔ ¬ Z.inQ x := by
  refine ⟨fun h (k : CharZero _) => hp.ne_zero (Nat.cast_eq_zero.1 h), fun h => ?_⟩
  let φ : Z.i.c.V W →+* Z.X.residueField x :=
    ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv ≫ Z.s.appTop ≫ Z.X.Γevaluation x).hom
  have hq : (ringChar (Z.X.residueField x)).Prime :=
    (CharP.char_is_prime_or_zero (Z.X.residueField x) _).resolve_right fun k =>
      h ((CharP.ringChar_zero_iff_CharZero _).1 k)
  by_contra hne
  have hc : (ringChar (Z.X.residueField x)).Coprime p :=
    hq.coprime_iff_not_dvd.2 fun k => hne ((ringChar.spec _ _).2 k)
  have := (GlobalTheory.CoeffRings.isUnit_of_coprime _ (natCast_mem_nonunits Z.i.c hp.ne_zero hW) hc).map φ
  rw [map_natCast, ringChar.Nat.cast_ringChar] at this
  exact not_isUnit_zero this

variable [Fact p.Prime]

variable {z : admitted Y i₀}

def degLine (L : FinLB z.Z.X) (c : Crv z) : ℤ := FibCrv.deg c L.lb

variable (z) (c : Crv z)

def degStep (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : ℤ :=
  match h : letterOf Dw st with
  | some x => degLine (z.line b st x h).L c
  | none => 0

def degRoot (τ : E →+* ℂ) (i : ℕ) : ℝ :=
  if i < Dw.p then (degStep z c true (.inl (τ, i)) : ℝ)
  else -(degStep z c true (.inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) : ℝ)

section Line

open ProjSpace

variable (p) {O : Type} [CommRing O] (φ : O →+* ZMod p)

instance isClosedImmersion_baseChange (N : ℕ) : IsClosedImmersion (baseChange N φ) :=
  MorphismProperty.of_isPullback (isPullback_baseChange N φ).flip
    (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective φ))

def lineCrv : FibCrv p (PSpace O 1) :=
  FibCrv.ofImm (baseChange 1 φ) (topologicalKrullDim_eq (ZMod p) 1)
    (by rw [← map_natCast (algebraMap (ZMod p) _), ZMod.natCast_self, map_zero])

theorem degree_twistingSheaf_line : (lineCrv p φ).deg (O1 O 1) = 1 := by
  have h := interNum_const_of_polynomial (ZMod p) (structureModule (PSpace (ZMod p) 1)) (O1_isLB (ZMod p) 1) (d := 1)
    (Polynomial.preHilbertPoly ℚ 1 0) (Polynomial.natDegree_preHilbertPoly ℚ 1 0).le
    (ProjCoh.chi_sheafO_eq_eval (ZMod p) 1)
  rw [Polynomial.coeff_preHilbertPoly_self, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero 1))] at h
  rw [(lineCrv p φ).deg_eq_of_imm (baseChange 1 φ) rfl (O1_isLB O 1),
    interNum_congr_lbIso (ZMod p) _ (L' := fun _ => O1 (ZMod p) 1) (isLB_vecOne (LB.isLB_pull (O1_isLB O 1) _))
      (fun _ => O1_isLB _ 1) fun i => by fin_cases i; exact lbIso_pull_O1 1 φ]
  exact_mod_cast h

example : (lineCrv p (Int.castRingHom _)).deg (O1 ℤ 1) = 1 ∧ (lineCrv p (Int.castRingHom _)).deg (LB.triv _) = 0 ∧
    (lineCrv p (Int.castRingHom _)).deg (dual (O1 ℤ 1)) = -1 := by
  have := isProper_str ℤ 1
  have : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have := (lineCrv p (Int.castRingHom _)).isProper_str (PSpace.str ℤ 1)
  have hA := isAmple_projective_O_one ℤ 1
  have h₀ : (lineCrv p (Int.castRingHom _)).deg (LB.triv _) = 0 :=
    interNumRed_one_eq_zero (LB.isLB_pull (LB.isLB_triv _) _)
      ((CechPic.cls_pull (LB.isLB_triv _) _ _).trans (map_zero _)) _
  have h₁ := degree_twistingSheaf_line p (Int.castRingHom _)
  have h₂ := (lineCrv p (Int.castRingHom _)).deg_of_cls_eq_add hA (LB.isLB_triv _) (CechPic.isLB_dual hA.isLB) hA.isLB
    (CechPic.cls_dual_add hA.isLB).symm
  omega

end Line

end GlobalTheory.ShFam.Pad
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ShFam.Pad

namespace GenId

theorem exists_maximal {X : Scheme.{0}} (z : X) : ∃ η : X, η ⤳ z ∧ ∀ y : X, y ⤳ η → y = η := by
  have hc := irreducibleComponent_mem_irreducibleComponents z
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  refine ⟨_, hg.specializes mem_irreducibleComponent, fun y hy => (hy.antisymm (hg.specializes ?_)).eq⟩
  refine hc.2 isIrreducible_singleton.closure ?_ (subset_closure rfl)
  exact hg.def.ge.trans (closure_minimal (Set.singleton_subset_iff.2 hy.mem_closure) isClosed_closure)

theorem ext_maximal {X : Scheme.{0}} [IsReduced X] {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ η ∈ U, (∀ y : X, y ⤳ η → y = η) → ∃ (k : Type) (_ : Field k) (w : Sp k ⟶ X),
      w (closedPoint k) = η ∧ valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)
  obtain ⟨η, hη, hm⟩ := exists_maximal z
  have hb : η ∈ X.basicOpen (a - b) := hη.mem_open (X.basicOpen _).isOpen hz
  obtain ⟨k, _, w, rfl, e⟩ := h η (X.basicOpen_le _ hb) hm
  have hU : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff U).2 (X.basicOpen_le _ hb)
  exact absurd (by rw [valF_sub hU, e, sub_self]) ((valF_ne_zero_iff hU (a - b)).2 ((le_preimage_iff _).2 hb))

theorem valF_map {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {w : Sp F ⟶ X} {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap f ≫ w) U a = f (valF w U a) := by
  obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) ((le_preimage_iff U).1 h)
  obtain ⟨χ, rfl⟩ := exists_fromSpec hV w ((le_preimage_iff V).2 hz)
  rw [← Category.assoc, ModelRelProbe.spMap_comp, ← valF_restrict hle (le_of_fromSpec hV rfl),
    ← valF_restrict hle (le_of_fromSpec hV rfl), valF_fromSpec, valF_fromSpec]
  rfl

theorem valF_natCast {F : Type} [Field F] {X : Scheme.{0}} {w : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (n : ℕ) :
    valF w U (n : Γ(X, U)) = n := by
  rw [valF, dif_pos h, map_natCast, map_natCast]

theorem valF_one {F : Type} [Field F] {X : Scheme.{0}} {w : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) :
    valF w U 1 = 1 := by
  rw [valF, dif_pos h, map_one, map_one]

theorem maximal_of_stalk {X : Scheme.{0}} {x : X} {K : Type} [Field K] {f : X.presheaf.stalk x →+* K}
    (hf : Function.Injective f) (y : X) (hy : y ⤳ (spMap f ≫ X.fromSpecStalk x) (closedPoint K)) :
    y = (spMap f ≫ X.fromSpecStalk x) (closedPoint K) := by
  change y ⤳ X.fromSpecStalk x (spMap f (closedPoint K)) at hy
  change y = X.fromSpecStalk x (spMap f (closedPoint K))
  obtain ⟨q, rfl⟩ := (X.range_fromSpecStalk (x := x)).ge (hy.trans ((X.range_fromSpecStalk (x := x)).le ⟨_, rfl⟩))
  have h : spMap f (closedPoint K) ⤳ q := (PrimeSpectrum.le_iff_specializes _ q).1 fun r hr => by
    have : f r ∈ maximalIdeal K := hr
    rw [maximalIdeal_eq_bot, Ideal.mem_bot, map_eq_zero_iff _ hf] at this
    exact this ▸ q.asIdeal.zero_mem
  exact (hy.antisymm (h.map (X.fromSpecStalk x).continuous)).eq

theorem mem_range_of_norm_le {p : ℕ} (hp : p.Prime) {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (hR : (p : R) ∈ maximalIdeal R) (hc : Cardinal.mk R ≤ Cardinal.continuum) {κ : K}
    (h : ∀ (C : SCF p) (ψ : R →+* ↥(intO ↥C.S)) (θ : K →+* ↥C.S),
      θ.comp (algebraMap R K) = (intO ↥C.S).subtype.comp ψ → ‖θ κ‖ ≤ 1) : ∃ r, algebraMap R K r = κ := by
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (by_contra fun hn => ?_)
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  obtain ⟨V, hV, hd, hκ⟩ := exists_discreteValuationSubring_dominating_notMem hn
  obtain ⟨h₁, h₂⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
  have hpV : (p : V) ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using h₂ _ hR
  obtain ⟨C, φ, φi, hφ⟩ := exists_scf_embedding_dvd p V hp hpV
    ((Cardinal.mk_subtype_le _).trans ((IsLocalization.cardinalMk_le (nonZeroDivisors R)).trans hc))
  let θ : K →+* ↥C.S := IsFractionRing.lift (A := V) (g := (intO ↥C.S).subtype.comp φ)
    ((intO ↥C.S).subtype_injective.comp φi)
  have hθ (v : V) : θ v = φ v := IsFractionRing.lift_algebraMap _ v
  have h₃ := h C (φ.comp ((algebraMap R K).codRestrict V h₁)) θ (RingHom.ext fun r => hθ ⟨_, h₁ r⟩)
  have h0 : κ ≠ 0 := fun e => hκ (e ▸ V.zero_mem)
  have hi : κ⁻¹ ∈ V := (V.mem_or_inv_mem κ).resolve_left hκ
  obtain ⟨c, hc⟩ := hφ 1 ⟨_, hi⟩ (by
    rw [← hθ, ← hθ]
    simp only [OneMemClass.coe_one, map_one, norm_one, map_inv₀, norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.2 ((map_ne_zero θ).2 h0))).2 h₃)
  have : κ⁻¹ * c = 1 := (congrArg Subtype.val hc).symm
  exact hκ ((inv_mul_eq_one₀ h0).1 this ▸ c.2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {Z : LocM.Mdl Y i₀}

include hp hW

theorem exists_chart_of_maximal {η : Z.X} (h : ∀ y : Z.X, y ⤳ η → y = η) : ∃ a, η ∈ (Z.U a).1 :=
  Set.mem_iUnion.1 (Z.cover.ge (HTLine.Dvd.mem_opn hp hW Z h))

theorem ext_chart {U : Z.X.Opens} {s t : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a,
    ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ U → valF w U s = valF w U t) : s = t := by
  have := isReduced_model Z
  refine ext_maximal fun η hη hm => ?_
  obtain ⟨a, ha⟩ := exists_chart_of_maximal hp hW hm
  exact ⟨_, _, resPt Z.X η, Scheme.fromSpecResidueField_apply η _,
    h _ _ a ((resPt_le_iff _ _ _).2 ha) ((resPt_le_iff _ _ _).2 hη)⟩

theorem exists_special (z : Z.X) : ∃ x : Z.X, z ⤳ x ∧ (p : Z.X.residueField x) = 0 := by
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsProper Z.s := inferInstanceAs (IsProper (_ ≫ _))
  have hc : IsClosed (Z.s '' closure {z}) := Z.s.isClosedMap _ isClosed_closure
  obtain ⟨x, hx, e⟩ : closedPoint (Z.i.c.V W) ∈ Z.s '' closure {z} :=
    (IsLocalRing.specializes_closedPoint (Z.s z)).mem_closed hc ⟨z, subset_closure rfl, rfl⟩
  refine ⟨x, specializes_iff_mem_closure.2 hx, (natCast_eq_zero_iff hp hW Z x).2 fun hq => ?_⟩
  exact (mem_gen_iff_inQ hp hW (Z := Z)).2 hq e

theorem exists_extension {U : Z.X.Opens} (f : ∀ a, Γ(Z.X, (Z.U a).1 ⊓ U))
    (hf : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a a', ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ (Z.U a').1 → ⊤ ≤ w ⁻¹ᵁ U →
      valF w _ (f a) = valF w _ (f a'))
    (hb : ∀ (y : Z.Pt) a, ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ y.z ⁻¹ᵁ U → ‖valF y.gen _ (f a)‖ ≤ 1)
    {x : Z.X} (hx : x ∈ U) (hpx : (p : Z.X.residueField x) = 0) :
    ∃ (V : Z.X.Opens) (t : Γ(Z.X, V)), x ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a,
      ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ V → valF w V t = valF w _ (f a) := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsProper Z.s := inferInstanceAs (IsProper (_ ≫ _))
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  let R : Type := Z.X.presheaf.stalk x
  obtain ⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R := (GlobalTheory.isNormalScheme_iff _).1 hN x
  let K := FractionRing R
  let ι : Sp R ⟶ Z.X := Z.X.fromSpecStalk x
  have hι (q : Sp R) : ι q ⤳ x := (Z.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
  let w₀ : Sp K ⟶ Z.X := spMap (algebraMap R K) ≫ ι
  have hη : w₀ (closedPoint K) ⤳ x := hι _
  have hm : ∀ y : Z.X, y ⤳ w₀ (closedPoint K) → y = w₀ (closedPoint K) :=
    maximal_of_stalk (IsFractionRing.injective R K)
  obtain ⟨a₀, ha₀⟩ := exists_chart_of_maximal hp hW hm
  have w₀a := (le_preimage_iff _).2 ha₀
  have w₀U : ⊤ ≤ w₀ ⁻¹ᵁ U := (le_preimage_iff _).2 (hη.mem_open U.isOpen hx)
  obtain ⟨φ₀, -⟩ := exists_fromSpec (Z.U a₀).2 w₀ w₀a
  have : CharZero K := (φ₀.comp (Z.alg a₀)).charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hc : Cardinal.mk R ≤ Cardinal.continuum := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z.X) hx
    obtain ⟨σ, -, hσ⟩ := HTLine.Dvd.exists_base hp hW Z hV
    letI := Z.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact (IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans
      (HTLine.Dvd.mk_le_of_finiteType σ hσ
        ((Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)))
  obtain ⟨ρ, hρ⟩ := mem_range_of_norm_le (R := R) (K := K) hp
    ((residue_eq_zero_iff _).1 ((map_natCast _ p).trans hpx)) hc (κ := valF w₀ _ (f a₀)) fun C ψ θ e => by
      have g : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι = spMap θ ≫ w₀ := by
        rw [← Category.assoc, ← Category.assoc, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, e]
      obtain ⟨Q, hQ⟩ := ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ ι) (by
        rintro _ ⟨q, rfl⟩
        rw [g, ← Z.cover]
        exact Set.mem_iUnion.2 ⟨a₀, w₀a (Set.mem_univ (spMap θ q))⟩)
      let y : Z.Pt := ⟨C, Q, spMap ψ ≫ ι, hQ⟩
      have hy : y.gen = spMap θ ≫ w₀ := g
      have := hb y a₀ (hy ▸ fun q _ => w₀a (Set.mem_univ (spMap θ q))) fun q _ => (hι (spMap ψ q)).mem_open U.isOpen hx
      rwa [hy, valF_map θ (U := (Z.U a₀).1 ⊓ U) fun q hq => ⟨w₀a hq, w₀U hq⟩] at this
  obtain ⟨V₁, hx₁, t₁, rfl⟩ := Z.X.presheaf.germ_exist ρ
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z.X) (x := x)
    (U := V₁ ⊓ (U ⊓ IsNormalScheme.component ⟨_, hC⟩)) ⟨hx₁, hx, mem_irreducibleComponent⟩
  have l₁ : V ≤ V₁ := fun q hq => (hle hq).1
  have l₂ : V ≤ U := fun q hq => (hle hq).2.1
  have hηV : w₀ (closedPoint K) ∈ V := hη.mem_open V.isOpen hxV
  have v : valF w₀ V (resG Z.X l₁ t₁) = valF w₀ _ (f a₀) := by
    have e : w₀ = spMap ((algebraMap R K).comp (Z.X.presheaf.germ V x hxV).hom) ≫ hV.fromSpec := by
      rw [← ModelRelProbe.spMap_comp, Category.assoc]
      exact congrArg (spMap (algebraMap R K) ≫ ·) (hV.fromSpecStalk_eq_fromSpecStalk hxV).symm
    rw [← hρ, e, valF_fromSpec]
    exact congrArg (algebraMap R K) (Z.X.presheaf.germ_res_apply (homOfLE l₁) x hxV t₁)
  refine ⟨V, resG Z.X l₁ t₁, hxV, l₂, fun k _ w a ha hw => ?_⟩
  have e : resG Z.X (inf_le_right : (Z.U a).1 ⊓ V ≤ V) (resG Z.X l₁ t₁) = resG Z.X (inf_le_inf_left _ l₂) (f a) := by
    refine ext_maximal fun η hη' hm' => ?_
    obtain rfl : η = w₀ (closedPoint K) :=
      (hm' _ (hg.specializes (hle hη'.2).2.2)).symm.trans (hm _ (hg.specializes (hle hηV).2.2))
    have h' := (le_preimage_iff (x := w₀) _).2 hη'
    refine ⟨K, inferInstance, w₀, rfl, ?_⟩
    rw [valF_restrict _ h', valF_restrict _ h', v]
    exact hf K w₀ a₀ a w₀a (fun q hq => (h' hq).1) w₀U
  have h' : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ V) := fun q hq => ⟨ha hq, hw hq⟩
  rw [← valF_restrict inf_le_right h', ← valF_restrict (inf_le_inf_left _ l₂) h']
  exact congrArg _ e

variable {b b' : Bool} {st st' : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

omit hp hW in

theorem val_ne_zero (M : LineModel Z b st x) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m} {i : Fin M.L.n}
    (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i) : valF w _ (M.r a i).val ≠ 0 :=
  left_ne_zero_of_mul_eq_one (valF_mul_inv (U := (Z.U a).1 ⊓ M.L.U i) (fun _ hq => ⟨ha hq, hi hq⟩) _)

omit hp hW in

theorem cross_eq (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (M : LineModel Z b st x) (M' : LineModel Z b' st' x)
    {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a a' : Fin Z.m} {i : Fin M.L.n} {j : Fin M'.L.n}
    (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (ha' : ⊤ ≤ w ⁻¹ᵁ (Z.U a').1) (hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i) (hj : ⊤ ≤ w ⁻¹ᵁ M'.L.U j) :
    valF w _ (M'.r a j).val * valF w _ (M.r a' i).val = valF w _ (M'.r a' j).val * valF w _ (M.r a i).val := by
  obtain ⟨φ, h⟩ := exists_fromSpec (Z.U a).2 w ha
  obtain ⟨φ', h'⟩ := exists_fromSpec (Z.U a').2 w ha'
  replace h : spMap φ ≫ Z.chart a = w := h
  replace h' : spMap φ' ≫ Z.chart a' = w := h'
  obtain ⟨d, d1, d2⟩ := chart_tri Z hty h h' x.1 x.2
  have e := M.chart k a a' i φ φ' d (h.trans h'.symm) (h ▸ hi) d1 (by rwa [← Category.assoc, h])
  have e' := M'.chart k a a' j φ φ' d (h.trans h'.symm) (h ▸ hj) d1 (by rwa [← Category.assoc, h])
  rw [h] at e e'
  rw [e, e']
  ring

def IsQuot (M : LineModel Z b st x) (M' : LineModel Z b' st' x) (i : Fin M.L.n) (j : Fin M'.L.n) (c : ℕ)
    {V : Z.X.Opens} (s : Γ(Z.X, V)) : Prop :=
  ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a, ⊤ ≤ w ⁻¹ᵁ (Z.U a).1 → ⊤ ≤ w ⁻¹ᵁ V →
    valF w V s * valF w _ (M.r a i).val = c * valF w _ (M'.r a j).val

variable (Z b st b' st') in

def Bdd : Prop := ∃ m : ℕ, ∀ (y : Z.Pt) a (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen →
  |lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st - lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b' st'| ≤
    m * Real.log p

omit hp hW in

theorem Bdd.symm (h : Bdd Z b b' st st') : Bdd Z b' b st' st :=
  h.imp fun _ h y a φ e => (abs_sub_comm _ _).trans_le (h y a φ e)

omit hW in

theorem bdd_step (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : Bdd Z false true st st := by
  have := Fact.mk hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hv : 0 ≤ vDiff E p := by unfold vDiff; positivity
  refine ⟨1 + ⌈vDiff E p⌉₊, fun y a φ _ => ?_⟩
  have hv' := mul_le_mul_of_nonneg_right (Nat.le_ceil (vDiff E p)) hl
  have hv'' := mul_nonneg hv hl
  have g : y.gen ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π := Category.assoc _ _ _
  have key {m : ℕ} (u : Fin m → _) (i : Fin m) : |Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (latDR _ (y.gen ≫ Z.π)) u i) -
      Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (latHT _ p (y.gen ≫ Z.π)) u i)| ≤ Real.log p := by
    refine (HTFrame.abs_log_grNorm_sub_le _ _ (a := (p : ↥y.C.S)) (Nat.cast_ne_zero.2 hp.ne_zero) ?_
      (latDR_subset_latHT E H _ _ _ p _) (fun v hv => ?_) u i).trans_eq (by rw [y.C.norm_p, inv_inv])
    · rw [y.C.norm_p]
      exact inv_le_one_of_one_le₀ (by linarith)
    · rw [g] at hv ⊢
      refine HTBound.htBound E H _ _ p _ y.C.norm_p _ (ext_unique _ _) v hv _ ?_
      rw [y.C.norm_p, ← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
      rw [div_le_one (by linarith)]
      linarith
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  rcases st with ⟨τ, k⟩ | k
  · simp only [lnStep, lat, Bool.false_eq_true, false_and, if_false, true_and, sub_zero]
    split_ifs with h h'
    · have := abs_le.1 (key ((Z.fr a).bc φ τ) ⟨k, h⟩)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · have := abs_le.1 (key ((Z.fr a).bc φ τ) ⟨k, h⟩)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [sub_self, abs_zero]
      linarith
  · simp only [lnStep, lat]
    split_ifs with h
    · exact (key _ _).trans (by linarith)
    · rw [sub_self, abs_zero]
      linarith

variable (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) {M : LineModel Z b st x} {M' : LineModel Z b' st' x}

theorem IsQuot.mul_eq_one {i : Fin M.L.n} {j : Fin M'.L.n} {V V' : Z.X.Opens} {s : Γ(Z.X, V)} {s' : Γ(Z.X, V')}
    (h : IsQuot M M' i j 1 s) (h' : IsQuot M' M j i 1 s') (hi : V ≤ M.L.U i) {k : Type} [Field k] {w : Sp k ⟶ Z.X}
    (hw : ⊤ ≤ w ⁻¹ᵁ V) (hw' : ⊤ ≤ w ⁻¹ᵁ V') : valF w V s * valF w V' s' = 1 := by
  have e : resG Z.X (inf_le_left : V ⊓ V' ≤ V) s * resG Z.X (inf_le_right : V ⊓ V' ≤ V') s' = 1 := by
    refine ext_chart hp hW fun k _ w a ha hw => ?_
    have e₁ := h k w a ha fun q hq => (hw hq).1
    have e₂ := h' k w a ha fun q hq => (hw hq).2
    rw [valF_mul hw, valF_restrict _ hw, valF_restrict _ hw, valF_one hw]
    refine mul_right_cancel₀ (val_ne_zero M ha fun q hq => hi (hw hq).1) ?_
    rw [Nat.cast_one, one_mul] at e₁ e₂
    rw [mul_right_comm, e₁, mul_comm, e₂, one_mul]
  have hw₂ : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V') := fun q hq => ⟨hw hq, hw' hq⟩
  have := congrArg (valF w _) e
  rwa [valF_mul hw₂, valF_restrict _ hw₂, valF_restrict _ hw₂, valF_one hw₂] at this

include hty

theorem exists_isQuot_special (hB : Bdd Z b b' st st') (i : Fin M.L.n) (j : Fin M'.L.n) {z : Z.X}
    (hz : z ∈ M.L.U i ⊓ M'.L.U j) (hpz : (p : Z.X.residueField z) = 0) :
    ∃ (m : ℕ) (V : Z.X.Opens) (t : Γ(Z.X, V)), z ∈ V ∧ V ≤ M.L.U i ⊓ M'.L.U j ∧ IsQuot M M' i j (p ^ m) t := by
  obtain ⟨m, hm⟩ := hB
  let f (a) : Γ(Z.X, (Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j)) := Nat.cast (p ^ m) *
    (resG Z.X (inf_le_inf_left _ inf_le_right) (M'.r a j).val * resG Z.X (inf_le_inf_left _ inf_le_left) (M.r a i)⁻¹.val)
  have hf (k : Type) [Field k] (w : Sp k ⟶ Z.X) (a) (ha : ⊤ ≤ w ⁻¹ᵁ (Z.U a).1) (hw : ⊤ ≤ w ⁻¹ᵁ (M.L.U i ⊓ M'.L.U j)) :
      valF w _ (f a) * valF w _ (M.r a i).val = (p ^ m : ℕ) * valF w _ (M'.r a j).val := by
    have h' : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j)) := fun q hq => ⟨ha hq, hw hq⟩
    have v := valF_mul_inv (x := w) (U := (Z.U a).1 ⊓ M.L.U i) (fun q hq => ⟨ha hq, (hw hq).1⟩) (M.r a i)
    rw [valF_mul h', valF_mul h', valF_restrict _ h', valF_restrict _ h', valF_natCast h']
    linear_combination ((p ^ m : ℕ) : k) * valF w _ (M'.r a j).val * v
  refine ⟨m, (exists_extension hp hW f (fun k _ w a a' ha ha' hw => ?_) (fun y a ha hy => ?_) hz hpz).imp
    fun V => Exists.imp fun t ⟨hzV, hle, ht⟩ => ⟨hzV, hle, fun k _ w a ha hw => by
      rw [ht k w a ha hw, hf k w a ha fun q hq => hle (hw hq)]⟩⟩
  · have hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i := fun q hq => (hw hq).1
    refine mul_right_cancel₀ (mul_ne_zero (val_ne_zero M ha hi) (val_ne_zero M ha' hi)) ?_
    linear_combination valF w _ (M.r a' i).val * hf k w a ha hw - valF w _ (M.r a i).val * hf k w a' ha' hw +
      ((p ^ m : ℕ) : k) * cross_eq hty M M' ha ha' hi fun q hq => (hw hq).2
  · have hw : ⊤ ≤ y.gen ⁻¹ᵁ (M.L.U i ⊓ M'.L.U j) := fun q _ => hy (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 y.gen ha
    have n := M.norm y a i φ hφ fun q hq => (hy hq).1
    have n' := M'.norm y a j φ hφ fun q hq => (hy hq).2
    have r := norm_pos_iff.2 (val_ne_zero M ha fun q hq => (hw hq).1)
    have r' := norm_pos_iff.2 (val_ne_zero M' ha fun q hq => (hw hq).2)
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
    have e := congrArg norm (hf _ y.gen a ha hw)
    rw [norm_mul, norm_mul, Nat.cast_pow, norm_pow, y.C.norm_p] at e
    refine le_of_mul_le_mul_right ?_ r
    rw [e, one_mul, ← Real.log_le_log_iff (by positivity) r, Real.log_mul (by positivity) r'.ne', Real.log_pow,
      Real.log_inv]
    linarith [(abs_le.1 (hm y a φ hφ)).2]

theorem exists_isQuot (hB : Bdd Z b b' st st') (i : Fin M.L.n) (j : Fin M'.L.n) {z : Z.X}
    (hz : z ∈ (nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j)) : ∃ (V : Z.X.Opens) (s : Γ(Z.X, V)), z ∈ V ∧
      V ≤ (nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j) ∧ IsQuot M M' i j 1 s := by
  obtain ⟨z₀, hz₀, hpz⟩ := exists_special hp hW z
  obtain ⟨i₁, hi₁⟩ := LB.mem_of_cover M.L.isLB z₀
  obtain ⟨j₁, hj₁⟩ := LB.mem_of_cover M'.L.isLB z₀
  obtain ⟨m, V, t, hV, hle, ht⟩ := exists_isQuot_special hp hW hty hB i₁ j₁ ⟨hi₁, hj₁⟩ hpz
  let T := V ⊓ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))
  have l : T ≤ M.L.U i ⊓ M.L.U i₁ := fun q hq => ⟨hq.2.2.1, (hle hq.1).1⟩
  have l' : T ≤ M'.L.U j ⊓ M'.L.U j₁ := fun q hq => ⟨hq.2.2.2, (hle hq.1).2⟩
  have hu : IsUnit ((p ^ m : ℕ) : Γ(Z.X, T)) := by
    have h : IsUnit (resG Z.X (Z.X.basicOpen_le (p : Γ(Z.X, ⊤))) p) := Z.X.toRingedSpace.isUnit_res_basicOpen _
    have := h.map
      (resG Z.X (U := Z.X.basicOpen (p : Γ(Z.X, ⊤))) (V := T) fun q hq => (gen_eq_basicOpen hp hW (Z := Z)).le hq.2.1)
    rw [map_natCast, map_natCast] at this
    simpa using this.pow m
  refine ⟨T, resG Z.X inf_le_left t * resG Z.X l (M.L.g i i₁).val * resG Z.X l' (M'.L.g j j₁)⁻¹.val * hu.unit⁻¹.val,
    ⟨hz₀.mem_open V.isOpen hV, hz⟩, inf_le_right, fun k _ w a ha hw => ?_⟩
  have e₁ := ht k w a ha fun q hq => (hw hq).1
  have e₂ := M.trans k w a i i₁ fun q hq => ⟨ha hq, l (hw hq)⟩
  have e₃ := M'.trans k w a j j₁ fun q hq => ⟨ha hq, l' (hw hq)⟩
  have e₄ := valF_mul_inv (x := w) (U := M'.L.U j ⊓ M'.L.U j₁) (fun q hq => l' (hw hq)) (M'.L.g j j₁)
  have e₅ := valF_mul_inv hw hu.unit
  rw [IsUnit.unit_spec, valF_natCast hw] at e₅
  rw [e₂, e₃] at e₁
  rw [valF_mul hw, valF_mul hw, valF_mul hw, valF_restrict _ hw, valF_restrict _ hw, valF_restrict _ hw, Nat.cast_one]
  linear_combination valF w _ (M'.L.g j j₁)⁻¹.val * valF w _ hu.unit⁻¹.val * e₁ +
    ((p ^ m : ℕ) : k) * valF w _ hu.unit⁻¹.val * valF w _ (M'.r a j).val * e₄ + valF w _ (M'.r a j).val * e₅

theorem exists_unit (hB : Bdd Z b b' st st') (i : Fin M.L.n) (j : Fin M'.L.n) :
    ∃ u : Γ(Z.X, (nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))ˣ, IsQuot M M' i j 1 u.val := by
  have := isReduced_model Z
  let P (k : Type) [Field k] (w : Sp k ⟶ Z.X) (c : k) : Prop := ∃ (V : Z.X.Opens) (s : Γ(Z.X, V)),
    V ≤ M.L.U i ∧ IsQuot M M' i j 1 s ∧ ⊤ ≤ w ⁻¹ᵁ V ∧ valF w V s = c
  have key (k : Type) [Field k] (w : Sp k ⟶ Z.X) (hw : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j))) :
      ∃ d : k, ∀ c, P k w c → c * d = 1 := by
    have hz := (le_preimage_iff _).1 hw
    obtain ⟨V', s', h₁, -, h₂⟩ := exists_isQuot hp hW hty (M := M') (M' := M) hB.symm j i ⟨hz.1, hz.2.2, hz.2.1⟩
    exact ⟨_, fun c ⟨V, s, a₁, a₂, a₃, a₄⟩ => a₄ ▸ a₂.mul_eq_one hp hW h₂ a₁ a₃ ((le_preimage_iff _).2 h₁)⟩
  obtain ⟨u, hu⟩ := exists_unit_of_locally Z.X ((nmodel Z).gen ⊓ (M.L.U i ⊓ M'.L.U j)) P
    (fun k _ w c c' hw h h' => by
      obtain ⟨d, hd⟩ := key k w hw
      exact (eq_inv_of_mul_eq_one_left (hd c h)).trans (eq_inv_of_mul_eq_one_left (hd c' h')).symm)
    (fun k _ w hw h => by
      obtain ⟨d, hd⟩ := key k w hw
      simpa using hd 0 h)
    fun z hz => by
      obtain ⟨V, s, h₁, h₂, h₃⟩ := exists_isQuot hp hW hty hB i j hz
      exact ⟨V, s, h₁, h₂, fun k _ w hw => ⟨V, s, fun q hq => (h₂ hq).2.1, h₃, hw, rfl⟩⟩
  refine ⟨u, fun k _ w a ha hw => ?_⟩
  obtain ⟨V, s, -, h₁, h₂, h₃⟩ := hu k w hw
  exact h₃ ▸ h₁ k w a ha h₂

end GenId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {b b' : Bool} {st st' : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

def IsGenId (M : LineModel Z b st x) (M' : LineModel Z b' st' x) (u : GenIso Z M.L M'.L) : Prop :=
  ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a i j, ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j)) →
    valF w _ (u.u i j).val * valF w _ (M.r a i).val = valF w _ (M'.r a j).val

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {M : LineModel Z b st x} {M' : LineModel Z b' st' x}

include hp hW

theorem IsGenId.unique {u u' : GenIso Z M.L M'.L} (h : IsGenId M M' u) (h' : IsGenId M M' u') : u = u' := by
  refine NModel.GenIso.ext (funext₂ fun i j => Units.ext (GenId.ext_chart hp hW fun k _ w a ha hw => ?_))
  exact mul_right_cancel₀ (GenId.val_ne_zero M ha fun q hq => (hw hq).2.1)
    ((h k w a i j fun q hq => ⟨ha hq, (hw hq).2⟩).trans (h' k w a i j fun q hq => ⟨ha hq, (hw hq).2⟩).symm)

theorem exists_isGenId (hty : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (hB : GenId.Bdd Z b b' st st')
    (M : LineModel Z b st x) (M' : LineModel Z b' st' x) : ∃ u, IsGenId M M' u := by
  choose u hu using GenId.exists_unit hp hW hty (M := M) (M' := M') hB
  have hu' (k : Type) [Field k] (w : Sp k ⟶ Z.X) (a i j) (h : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U i ⊓ M'.L.U j))) :
      valF w _ (u i j).val * valF w _ (M.r a i).val = valF w _ (M'.r a j).val := by
    simpa using hu i j k w a (fun q hq => (h hq).1) fun q hq => ⟨chart_le_gen hp hW a (h hq).1, (h hq).2⟩
  refine ⟨⟨u, fun i i₁ j j₁ => Units.ext (GenId.ext_chart hp hW fun k _ w a ha hw => ?_)⟩, hu'⟩
  have e₁ := hu' k w a i j fun q hq => ⟨ha hq, (hw hq).1.2⟩
  have e₂ := hu' k w a i₁ j₁ fun q hq => ⟨ha hq, (hw hq).2⟩
  have e₃ := M.trans k w a i i₁ fun q hq => ⟨ha hq, (hw hq).1.2.1, (hw hq).2.1⟩
  have e₄ := M'.trans k w a j j₁ fun q hq => ⟨ha hq, (hw hq).1.2.2, (hw hq).2.2⟩
  rw [e₃, e₄] at e₂
  refine ((valF_mul hw _ _).trans (congrArg₂ (· * ·) (valF_restrict _ hw _) (valF_restrict _ hw _))).trans
    (Eq.trans ?_ ((valF_mul hw _ _).trans (congrArg₂ (· * ·) (valF_restrict _ hw _) (valF_restrict _ hw _))).symm)
  refine mul_right_cancel₀ (GenId.val_ne_zero M ha fun q hq => (hw hq).1.2.1) ?_
  linear_combination valF w _ (M'.L.g j j₁).val * e₁ - e₂

end GlobalTheory.ShFam.Pad
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (z : admitted Y i₀)

def stepLB (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : FinLB z.Z.X :=
  match h : letterOf Dw st with
  | some x => (z.line b st x h).L
  | none => FinLB.triv _

theorem stepLB_of_some (b : Bool) {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x) :
    z.stepLB b st = (z.line b st x h).L := by
  unfold stepLB
  split
  · next y hy => obtain rfl : y = x := Option.some.inj (hy.symm.trans h); rfl
  · next hy => exact absurd (hy.symm.trans h) (by simp)

def rootLB (b : Bool) (τ : E →+* ℂ) (i : ℕ) : FinLB z.Z.X :=
  if i < Dw.p then z.stepLB b (.inl (τ, i)) else (z.stepLB b (.inl (conjEmb τ, Dw.p + Dw.q - 1 - i))).dual

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

section Step

variable {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x)

def genId : GenIso z.Z (z.line false st x h).L (z.line true st x h).L :=
  (exists_isGenId hp hW z.full (GenId.bdd_step hp st) _ _).choose

theorem isGenId_genId : IsGenId (z.line false st x h) (z.line true st x h) (z.genId hp hW h) :=
  (exists_isGenId hp hW z.full (GenId.bdd_step hp st) _ _).choose_spec

theorem log_norm_genId (y : z.Z.Pt) (a : Fin z.Z.m) (φ : Γ(z.Z.X, (z.Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ z.Z.chart a = y.gen) {i j} (hi : ⊤ ≤ y.z ⁻¹ᵁ (z.line false st x h).L.U i)
    (hj : ⊤ ≤ y.z ⁻¹ᵁ (z.line true st x h).L.U j) :
    Real.log ‖valF y.gen _ ((z.genId hp hW h).u i j).val‖ =
      lnStep (Y z.Z.i).t (y.gen ≫ z.Z.π) ((z.Z.fr a).bc φ) p false st -
        lnStep (Y z.Z.i).t (y.gen ≫ z.Z.π) ((z.Z.fr a).bc φ) p true st := by
  have ha := Pull.le_of_fromSpec (z.Z.U a).2 hφ
  have hi' : ⊤ ≤ y.gen ⁻¹ᵁ (z.line false st x h).L.U i := fun q _ => hi (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  have hj' : ⊤ ≤ y.gen ⁻¹ᵁ (z.line true st x h).L.U j := fun q _ => hj (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  have e := z.isGenId_genId hp hW h _ y.gen a i j fun q hq => ⟨ha hq, hi' hq, hj' hq⟩
  have n := GenId.val_ne_zero _ ha hj'
  have e' := congrArg (fun c => Real.log ‖c‖) e
  rw [← e] at n
  simp only [norm_mul] at e'
  rw [Real.log_mul (norm_ne_zero_iff.2 (left_ne_zero_of_mul n)) (norm_ne_zero_iff.2 (right_ne_zero_of_mul n))] at e'
  linarith [(z.line false st x h).norm y a i φ hφ hi, (z.line true st x h).norm y a j φ hφ hj]

end Step

variable (d : ℕ) {r : ℕ} {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Fin r → Letter Dw}
  (h : ∀ i, letterOf Dw (st i) = some (x i))

def stepPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L) (fun i => (z.line true _ _ (h i)).L) fun i => z.genId hp hW (h i)

def dualPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L.dual) (fun i => (z.line true _ _ (h i)).L.dual)
    fun i => NModel.GenIso.dual (z.genId hp hW (h i))

theorem pair_x_eq_LB_false (i : Fin r) : (z.stepPair hp hW d h).x i = z.stepLB false (st i) := (z.stepLB_of_some _ _).symm

theorem pair_x_prime_eq_LB_true (i : Fin r) : (z.stepPair hp hW d h).x' i = z.stepLB true (st i) := (z.stepLB_of_some _ _).symm

theorem dualPair_x_eq_dual_LB_false (i : Fin r) : (z.dualPair hp hW d h).x i = (z.stepLB false (st i)).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

theorem dualPair_x_prime_eq_dual_LB_true (i : Fin r) : (z.dualPair hp hW d h).x' i = (z.stepLB true (st i)).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

theorem dualPair_Dv (i : Fin r) : (z.dualPair hp hW d h).Dv i = -vdiv hp hW d _ _ (z.genId hp hW (h i)) :=
  vdiv_dual hp hW d _ _ _

omit hp

variable [Fact p.Prime]

include hW

end admitted

section Ranks

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) {p : ℕ} [Fact p.Prime] (jc : DV.KW p →+* ℂ)

theorem comp_cEmb (τ : DV.Emb D p) : jc.comp (DV.cEmb D τ) = conjEmb (jc.comp τ) :=
  RingHom.ext fun x => Formalism.MainNotions.WeightFamilies.emb_conj D (jc.comp τ) x

theorem mult_comp (τ : DV.Emb D p) : S.Dw.mult (jc.comp τ) = DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  by_cases h : τ ∈ DV.PsiOf D jc
  · obtain ⟨t, ht⟩ := id h
    rw [DV.rkOf, if_pos h, ht, Datum.mult, if_pos (A.cm t), h₁]
  · obtain ⟨t, ht⟩ : DV.cEmb D τ ∈ DV.PsiOf D jc := by_contra fun h' => h ((cm_type_meets_conjugate_pair p jc τ).2 h')
    have h₃ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
    rw [← comp_cEmb, ht, Datum.mult.eq_1 _ (DV.tauEmb D t), if_pos (A.cm t)] at h₃
    rw [DV.rkOf, if_neg h]
    omega

theorem mult_conj_comp (τ : DV.Emb D p) : S.Dw.mult (conjEmb (jc.comp τ)) = N - DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
  have h₂ := S.rank_eq
  rw [mult_comp] at h₁
  omega

theorem length_letters : (letters S.Dw).length = D.R.f * N := by
  have h := GlobalTheory.Proof.LetterConjugation.two_mul_length S.Dw
  rw [GlobalTheory.Proof.LetterConjugation.finrank_host, S.rank_eq, mul_assoc] at h
  omega

theorem letterOf_lie (τ : DV.Emb D p) (i : Fin (DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (jc.comp τ, i)) = some ⟨jc.comp τ, i.cast (mult_comp S jc τ).symm⟩ :=
  dif_pos (i.cast (mult_comp S jc τ).symm).2

theorem letterOf_om (τ : DV.Emb D p) (i : Fin (N - DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (conjEmb (jc.comp τ), i.rev)) =
      some ⟨conjEmb (jc.comp τ), i.rev.cast (mult_conj_comp S jc τ).symm⟩ :=
  dif_pos (i.rev.cast (mult_conj_comp S jc τ).symm).2

theorem letterOf_whole (k : Fin (D.R.f * N)) :
    letterOf S.Dw (.inr k) = some ((letters S.Dw).get (k.cast (length_letters S).symm)) :=
  List.getElem?_eq_getElem (k.cast (length_letters S).symm).2

end Ranks

section Mdl

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ)

def mdlOf : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := ithOf hp hW z.Z (Formalism.DegreeFormula.dimFl D.what₂.Tau N)
  cov := cov z
  cov_pos := cov_pos z
  lvl := z.n
  lie τ := z.stepPair hp hW _ (letterOf_lie S jc τ)
  om τ := z.dualPair hp hW _ (letterOf_om S jc τ)
  lieW := z.stepPair hp hW _ (letterOf_whole S)
  omW := z.dualPair hp hW _ fun k => letterOf_whole S k.rev
  om_dual τ := ⟨Fin.revPerm.trans (finCongr (by rw [← mult_conj_comp S, ← mult_comp S, comp_cEmb])), fun i => by
    rw [admitted.dualPair_x_eq_dual_LB_false, admitted.pair_x_eq_LB_false]
    exact (FinLB.firstChern_dual _).trans
      (congrArg (fun σ => -(admitted.stepLB z false (.inl (σ, i.rev))).c1) (comp_cEmb jc τ).symm)⟩
  dim_eq := rfl
  omW_dual := ⟨Fin.revPerm, fun _ => FinLB.firstChern_dual _⟩

theorem mdlOf_lie (τ : DV.Emb D p) (i) : ((mdlOf z jc).lie τ).x i = z.stepLB false (.inl (jc.comp τ, i)) ∧
    ((mdlOf z jc).lie τ).x' i = z.stepLB true (.inl (jc.comp τ, i)) :=
  ⟨z.pair_x_eq_LB_false hp hW _ _ i, z.pair_x_prime_eq_LB_true hp hW _ _ i⟩

theorem mdlOf_om (τ : DV.Emb D p) (i) :
    ((mdlOf z jc).om τ).x i = (z.stepLB false (.inl (conjEmb (jc.comp τ), i.rev))).dual ∧
    ((mdlOf z jc).om τ).x' i = (z.stepLB true (.inl (conjEmb (jc.comp τ), i.rev))).dual :=
  ⟨z.dualPair_x_eq_dual_LB_false hp hW _ _ i, z.dualPair_x_prime_eq_dual_LB_true hp hW _ _ i⟩

theorem mdlOf_lieW (k) : (mdlOf z jc).lieW.x k = z.stepLB false (.inr k) ∧
    (mdlOf z jc).lieW.x' k = z.stepLB true (.inr k) :=
  ⟨z.pair_x_eq_LB_false hp hW _ _ k, z.pair_x_prime_eq_LB_true hp hW _ _ k⟩

theorem mdlOf_omW (k) : (mdlOf z jc).omW.x k = (z.stepLB false (.inr k.rev)).dual ∧
    (mdlOf z jc).omW.x' k = (z.stepLB true (.inr k.rev)).dual :=
  ⟨z.dualPair_x_eq_dual_LB_false hp hW _ _ k, z.dualPair_x_prime_eq_dual_LB_true hp hW _ _ k⟩

theorem mdlOf_lie_Dv (τ : DV.Emb D p) (i) :
    ((mdlOf z jc).lie τ).Dv i = vdiv hp hW _ _ _ (z.genId hp hW (letterOf_lie S jc τ i)) := rfl

theorem mdlOf_om_Dv (τ : DV.Emb D p) (i) :
    ((mdlOf z jc).om τ).Dv i = -vdiv hp hW _ _ _ (z.genId hp hW (letterOf_om S jc τ i)) :=
  z.dualPair_Dv hp hW _ _ i

theorem mdlOf_omW_Dv (k) : (mdlOf z jc).omW.Dv k = -(mdlOf z jc).lieW.Dv k.rev := z.dualPair_Dv hp hW _ _ k

def rootOf (x : Bool × DV.Rt D.what₂.Tau N) : (mdlOf z jc).Z.LB := z.rootLB x.1 (DV.tauEmb D x.2.1) x.2.2

variable {jc} {t : D.what₂.Tau} {τ : DV.Emb D p} (ht : jc.comp τ = DV.tauEmb D t)

include ht

theorem rootOf_lie (i : Fin (DV.rkOf (DV.PsiOf D jc) N j τ)) (i' : Fin N) (h : (i' : ℕ) = i) :
    rootOf z jc (false, (t, i')) = ((mdlOf z jc).lie τ).x i ∧ rootOf z jc (true, (t, i')) = ((mdlOf z jc).lie τ).x' i := by
  have hi : (i' : ℕ) < S.Dw.p := by
    have hr : DV.rkOf (DV.PsiOf D jc) N j τ = j := if_pos ⟨t, ht⟩
    have := i.2
    have := S.p_eq
    omega
  rw [(mdlOf_lie z jc τ i).1, (mdlOf_lie z jc τ i).2, ht, ← h]
  exact ⟨if_pos hi, if_pos hi⟩

theorem rootOf_om (i : Fin (N - DV.rkOf (DV.PsiOf D jc) N j τ)) (i' : Fin N) (h : (i' : ℕ) = j + i) :
    rootOf z jc (false, (t, i')) = ((mdlOf z jc).om τ).x i ∧ rootOf z jc (true, (t, i')) = ((mdlOf z jc).om τ).x' i := by
  have hr : DV.rkOf (DV.PsiOf D jc) N j τ = j := if_pos ⟨t, ht⟩
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  have hi : ¬ (i' : ℕ) < S.Dw.p := by omega
  have e : (i.rev : ℕ) = S.Dw.p + S.Dw.q - 1 - i' := by rw [Fin.val_rev]; omega
  rw [(mdlOf_om z jc τ i).1, (mdlOf_om z jc τ i).2, ht, e]
  exact ⟨if_neg hi, if_neg hi⟩

end Mdl

section PiLocalization₂

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la))

theorem one_add_lt_three {p : ℕ} (hp : p.Prime) : 1 + 1 / ((p : ℝ) - 1) < (3 : ℕ) := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  push_cast
  linarith

abbrev AdmPl (p : ℕ) [Fact p.Prime] (la : PlL D p) : Type :=
  AdmAt S κ Fact.out (placeW_over D p la (jC p la) (hj p la)).1

def admissible_representation_factorisation (hA : AdmEx S κ) : AdmSt D N j jC where
  admitted p _ la := AdmPl S κ jC hj p la
  mdl p _ la z := mdlOf z (jC p la)
  Crv _ _ _ z := Crv z
  deg _ _ _ z c x := degRoot z c (DV.tauEmb D x.1) x.2
  ht p _ _ := (hA p Fact.out _ _ 3 (one_add_lt_three Fact.out)).choose

variable (hA : AdmEx S κ) (p : ℕ) [Fact p.Prime] (la : PlL D p)

end PiLocalization₂

section Examples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

example (z : admitted Y i₀) {τ : E →+* ℂ} (hτ : τ (H.rt : E) ≠ H.rt0) (k : Fin (Dw.mult τ))
    (h : letterOf Dw (.inl (τ, k)) = some ⟨τ, k⟩) (y : z.Z.Pt) (a : Fin z.Z.m) (φ : Γ(z.Z.X, (z.Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ z.Z.chart a = y.gen) {i j} (hi : ⊤ ≤ y.z ⁻¹ᵁ (z.line false _ _ h).L.U i)
    (hj : ⊤ ≤ y.z ⁻¹ᵁ (z.line true _ _ h).L.U j) : 0 ≤ Real.log ‖valF y.gen _ ((z.genId hp hW h).u i j).val‖ := by
  have g : y.gen ≫ z.Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ z.Z.π := Category.assoc _ _ _
  have F := Pull.frame_ind (Pull.chart_frame z.Z hφ) τ
  rw [z.log_norm_genId hp hW h y a φ hφ hi hj]
  simp only [lnStep, dif_pos k.2, hτ, and_false, if_false, sub_zero, sub_nonneg]
  rw [g] at F ⊢
  have pos (b) := GlobalTheory.GrNormPos.grNorm_pos HTBound.htBound E H _ _ p y.C b _ hp (Pull.ext_unique _ _) _ _ F.1 F.2 k
  refine Real.log_le_log (pos true) (csInf_le_csInf ⟨0, ?_⟩ ?_ ?_)
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · exact Set.nonempty_iff_ne_empty.2 fun e => (pos false).ne' ((congrArg sInf e).trans Real.sInf_empty)
  · rintro r ⟨cf, h₁, h₂, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h₁, h₂, ⟨w, latDR_subset_latHT E H _ _ _ p _ hw, hc⟩, rfl⟩

example {Z : LocM.Mdl Y i₀} {b st x} (M : LineModel Z b st x) (u : GenIso Z M.L M.L) (h : IsGenId M M u) (d : ℕ) :
    vdiv hp hW d _ _ u = 0 := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have e : IsGenId M M (.ofGlobal (idIso _) (idIso_isGen M.L.isLB)) := fun k _ w a i j hw => by
    have hw' : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M.L.U j)) := fun q hq => ⟨chart_le_gen hp hW a (hw hq).1, (hw hq).2⟩
    rw [M.trans k w a i j hw]
    exact congrArg (· * _) (FieldPtGlue.valF_restrict _ hw' _)
  rw [h.unique hp hW e]
  exact (congrArg NModel.toQ (NModel.GenIso.div_ofGlobal _ _ _ _)).trans (map_zero _)

example {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} [Fact p.Prime] (z : AdmAt S κ hp hW)
    (jc : DV.KW p →+* ℂ) (h : 0 < D.R.f * N) : (mdlOf z jc).Z.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1 ∧
      (mdlOf z jc).omW.x ⟨0, h⟩ = (z.stepLB false (.inr (D.R.f * N - 1))).dual :=
  ⟨rfl, (mdlOf_omW z jc _).1⟩

end Examples

end GlobalTheory.ShFam.Pad
end
end
