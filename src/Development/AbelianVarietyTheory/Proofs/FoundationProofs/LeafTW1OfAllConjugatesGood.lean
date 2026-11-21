import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PlaceBelowAllPowers
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ToricLatticeDenominators
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenRBaseChangeSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCommensurableOfIsLatIn
import Formalism.LocalToGlobal.Columns.LocWLemmas

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.ExportCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Index

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem sIdx_eq {W : Type} [AddCommGroup W] [Module R W] (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      (signedLength M N : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  simp only [Formalism.MainNotions.IntegralHeckeForms.sIdx, Formalism.MainNotions.IntegralHeckeForms.lenR, signedLength, relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]

theorem sIdx_map {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') (hf : Function.Injective f) (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (M.map f) (N.map f) = Formalism.MainNotions.IntegralHeckeForms.sIdx l M N := by
  simp only [sIdx_eq, signedLength, relLength_map_of_injective f hf]

theorem vK_eq (l : ℕ) (x : FractionRing R) (hx : x ≠ 0) :
    vK R l x = (WithZero.log (Ring.ordFrac R x) : ℤ) /
      ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  have h := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  simp only [vK, nval]
  set p := (IsLocalization.surj (nonZeroDivisors R) x).choose
  have inj := IsFractionRing.injective R (FractionRing R)
  have h2 : (p.2 : R) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have h1 : p.1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact mul_ne_zero hx ((map_ne_zero_iff _ inj).2 h2) h
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (mt (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).mp h1)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (mt (IsDiscreteValuationRing.addVal_eq_top_iff (R := R)).mp h2)
  have h3 := congrArg (Ring.ordFrac R) h
  rw [map_mul, ordFrac_algebraMap_eq_exp hm.symm, ordFrac_algebraMap_eq_exp hn.symm] at h3
  have h4 : Ring.ordFrac R x = WithZero.exp ((m : ℤ) - n) := by
    rw [WithZero.exp_sub, ← h3, mul_div_cancel_right₀ _ WithZero.exp_ne_zero]
  rw [h4, WithZero.log_exp, ← hm, ← hn, ← sub_div]
  simp

variable {W : Type} [AddCommGroup W] [Module (FractionRing R) W] [Module R W]
  [IsScalarTower R (FractionRing R) W]

theorem isLatIn_iff (V : Submodule (FractionRing R) W) (L : Submodule R W) :
    ToricLatticeDenominators.IsLatIn V L ↔ Formalism.MainNotions.IntegralHeckeForms.IsLatIn L (V.restrictScalars R) := by
  refine and_congr_right fun _ => ⟨fun h => ⟨fun x hx => ?_, fun x hx => ?_⟩, fun h => ?_⟩
  · rw [← h]; exact Submodule.subset_span hx
  · rw [← h, Submodule.restrictScalars_mem] at hx
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) (FractionRing R)
      (L : Set W) x hx
    rw [Submodule.span_eq] at hc
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  · refine le_antisymm (Submodule.span_le.2 h.1) fun x hx => ?_
    obtain ⟨c, hc, hx⟩ := h.2 x hx
    have hc' : algebraMap R (FractionRing R) c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hc
    have : x = (algebraMap R (FractionRing R) c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul (FractionRing R) c x, inv_smul_smul₀ hc']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

def inside (V : Submodule (FractionRing R) W) (L : Submodule R W) : Submodule R ↥V :=
  L.comap (V.subtype.restrictScalars R)

theorem map_inside {V : Submodule (FractionRing R) W} {L : Submodule R W} (h : ToricLatticeDenominators.IsLatIn V L) :
    (inside V L).map (V.subtype.restrictScalars R) = L := by
  refine Submodule.map_comap_eq_self fun x hx => ⟨⟨x, ?_⟩, rfl⟩
  rw [← h.2]; exact Submodule.subset_span hx

theorem isLattice_inside {V : Submodule (FractionRing R) W} {L : Submodule R W} (h : ToricLatticeDenominators.IsLatIn V L) :
    Submodule.IsLattice (FractionRing R) (inside V L) := by
  have hinj : Function.Injective (V.subtype.restrictScalars R) := V.injective_subtype
  constructor
  · apply Submodule.fg_of_fg_map_injective _ hinj
    rw [map_inside h]; exact h.1
  · apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top]
    have : V.subtype '' (inside V L : Set V) = L := by
      conv_rhs => rw [← map_inside h]
      rfl
    rw [this, h.2]

theorem eq_sIdx_of_isIdx {l : ℕ} {V : Submodule (FractionRing R) W} {L₁ L₂ : Submodule R W} {x : ℝ}
    (h : ToricLatticeDenominators.IsIdx l V L₁ L₂ x) : x = Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ := by
  obtain ⟨h₁, h₂, g, hg, rfl⟩ := h
  have := isLattice_inside h₁
  have e₂ : (inside V L₁).map ((g : V →ₗ[FractionRing R] V).restrictScalars R) = inside V L₂ := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hg w).1 hw
    · intro hv
      refine ⟨g.symm v, (hg _).2 ?_, by simp⟩
      rw [g.apply_symm_apply]; exact hv
  rw [← map_inside h₁, ← map_inside h₂, sIdx_map _ (by exact V.injective_subtype), sIdx_eq,
    vK_eq _ _ (LinearEquiv.isUnit_det' g).ne_zero, (signedLength_eq_log_ordFrac_det_of_map_eq g e₂).2]

theorem isIdx_sIdx (l : ℕ) {V : Submodule (FractionRing R) W} {L₁ L₂ : Submodule R W}
    (h₁ : ToricLatticeDenominators.IsLatIn V L₁) (h₂ : ToricLatticeDenominators.IsLatIn V L₂) :
    ToricLatticeDenominators.IsIdx l V L₁ L₂ (Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂) := by
  suffices h : ∃ x, ToricLatticeDenominators.IsIdx l V L₁ L₂ x by
    obtain ⟨x, hx⟩ := h
    rw [← eq_sIdx_of_isIdx hx]; exact hx
  have := isLattice_inside h₁
  have := isLattice_inside h₂
  obtain ⟨g, e₃⟩ := exists_linearEquiv_map_eq_of_isLattice (FractionRing R) (inside V L₁) (inside V L₂)
  refine ⟨_, h₁, h₂, g, fun v => ?_, rfl⟩
  change v ∈ inside V L₁ ↔ g v ∈ inside V L₂
  rw [← e₃]
  constructor
  · intro hv; exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, e⟩
    have : w = v := g.injective e
    exact this ▸ hw

end Index

section Transport

theorem isLatIn_map_iff {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] (f : W →ₗ[R] W') (hf : Function.Injective f) (M V : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (M.map f) (V.map f) ↔ Formalism.MainNotions.IntegralHeckeForms.IsLatIn M V := by
  refine ⟨fun h => ⟨Submodule.fg_of_fg_map_injective f hf h.1,
    (Submodule.map_le_map_iff_of_injective hf _ _).1 h.2.1, fun x hx => ?_⟩,
    fun h => ⟨h.1.map f, Submodule.map_mono h.2.1, ?_⟩⟩
  · obtain ⟨c, hc, y, hy, e⟩ := h.2.2 (f x) ⟨x, hx, rfl⟩
    rw [← map_smul] at e
    exact ⟨c, hc, hf e ▸ hy⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hy⟩ := h.2.2 x hx
    exact ⟨c, hc, c • x, hy, map_smul _ _ _⟩

theorem isLatIn_span {R S W W' : Type} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (hi : Function.Injective (algebraMap R S)) [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] [Module S W'] [IsScalarTower R S W'] (r : W →ₗ[R] W') {L V : Submodule R W}
    (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Submodule.span S (r '' L)) (Submodule.span S (r '' V)) := by
  refine ⟨?_, Submodule.span_mono (Set.image_mono h.2.1), fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := h.1.map r
    rw [← Submodule.map_coe, ← hs, Submodule.span_span_of_tower]
    exact Submodule.fg_span s.finite_toSet
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, hc, hy⟩ := h.2.2 y hy
      refine ⟨algebraMap R S c, (map_ne_zero_iff _ hi).2 hc, Submodule.subset_span ⟨_, hy, ?_⟩⟩
      rw [map_smul, algebraMap_smul]
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ hx⟩

variable (O : Type) [CommRing O] [IsDomain O] (F : Type) [AddCommGroup F]
  [Module (FractionRing O) F] [Module O F] [IsScalarTower O (FractionRing O) F]
  (O' : Type) [CommRing O'] [IsDomain O'] [Algebra O O']

def toFrac : O' ⊗[O] F →ₗ[O'] FractionRing O' ⊗[O] F :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O' (FractionRing O')) LinearMap.id

theorem toFrac_tmul (a : O') (x : F) :
    toFrac O F O' (a ⊗ₜ x) = algebraMap O' (FractionRing O') a ⊗ₜ x := rfl

theorem toFrac_injective : Function.Injective (toFrac O F O') := by
  haveI : Module.Flat O (FractionRing O) := IsLocalization.flat _ (nonZeroDivisors O)
  haveI : Module.Flat O F := Module.Flat.trans O (FractionRing O) F
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := F)
    ((Algebra.linearMap O' (FractionRing O')).restrictScalars O) (IsFractionRing.injective O' _)
  have e : ∀ x, toFrac O F O' x =
      ((Algebra.linearMap O' (FractionRing O')).restrictScalars O).rTensor F x := by
    intro x
    induction x with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  exact h (by rw [← e, ← e, hxy])

theorem toFrac_smul_mem (hi : Function.Injective (algebraMap O O')) [Module.Finite O O']
    (V : Submodule (FractionRing O) F) (k : FractionRing O') (x : F) (hx : x ∈ V) :
    k ⊗ₜ[O] x ∈ ((V.restrictScalars O).baseChange O').map (toFrac O F O') := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O') k
  obtain ⟨a, ha, q', hq'⟩ := (Algebra.IsIntegral.isIntegral (R := O) q).isAlgebraic.exists_nonzero_dvd hq
  have ha' : algebraMap O (FractionRing O) a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha
  have hq0 : algebraMap O' (FractionRing O') q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O' _)).2 (nonZeroDivisors.ne_zero hq)
  refine ⟨(p * q') ⊗ₜ ((algebraMap O (FractionRing O) a)⁻¹ • x),
    Submodule.tmul_mem_baseChange_of_mem _ (V.smul_mem _ hx), ?_⟩
  have hx' : x = a • ((algebraMap O (FractionRing O) a)⁻¹ • x) := by
    rw [← algebraMap_smul (FractionRing O) a, smul_inv_smul₀ ha']
  conv_rhs => rw [hx', ← TensorProduct.smul_tmul]
  rw [toFrac_tmul]
  congr 1
  rw [← algebraMap_smul O' a, Algebra.smul_def, hq', map_mul, map_mul]
  field_simp

theorem toFrac_surjective (hi : Function.Injective (algebraMap O O')) [Module.Finite O O'] :
    Function.Surjective (toFrac O F O') := by
  intro y
  induction y with
  | zero => exact ⟨0, map_zero _⟩
  | tmul k x =>
    obtain ⟨z, -, hz⟩ := toFrac_smul_mem O F O' hi ⊤ k x trivial
    exact ⟨z, hz⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

theorem span_frac_eq (hi : Function.Injective (algebraMap O O')) [Module.Finite O O']
    (V : Submodule (FractionRing O) F) :
    (Submodule.span (FractionRing O') ((fun x => (1 : FractionRing O') ⊗ₜ[O] x) '' (V : Set F))).restrictScalars O' =
      ((V.restrictScalars O).baseChange O').map (toFrac O F O') := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.restrictScalars_mem] at hy
    have : ∀ k : FractionRing O', k • y ∈ ((V.restrictScalars O).baseChange O').map (toFrac O F O') := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        intro k
        rw [TensorProduct.smul_tmul']
        exact toFrac_smul_mem O F O' hi V _ x hx
      | zero => intro k; simp
      | add x y _ _ hx hy => intro k; rw [smul_add]; exact Submodule.add_mem _ (hx k) (hy k)
      | smul a x _ hx => intro k; rw [smul_smul]; exact hx _
    simpa using this 1
  · rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨x, hx, ?_⟩
    simp [toFrac_tmul]

end Transport
section Objects

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

theorem eOp_eq : ToricLatticeDenominators.eOp Y i j b = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b := rfl

theorem typePart_eq : ToricLatticeDenominators.typePart Y i j b = Formalism.MainNotions.IntegralHeckeForms.Fm0 Y i j b := by
  ext x
  simp [ToricLatticeDenominators.typePart, Formalism.MainNotions.IntegralHeckeForms.Fm0, Submodule.mem_iInf, sub_eq_zero]

theorem eOp_idem (x : Y.Fm i j b) : ToricLatticeDenominators.eOp Y i j b (ToricLatticeDenominators.eOp Y i j b x) = ToricLatticeDenominators.eOp Y i j b x := by
  rw [← Module.End.mul_apply, ToricLatticeDenominators.eOp, ← map_mul, Y.eAlg_idem]

theorem eOp_comm (g : G0g N) (x : Y.Fm i j b) :
    ToricLatticeDenominators.eOp Y i j b (Y.actG i j b g x) = Y.actG i j b g (ToricLatticeDenominators.eOp Y i j b x) := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i))
    (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)))
    (Y.eAlg_central i b (MonoidAlgebra.of _ _ g))
  rw [map_mul, map_mul, MonoidAlgebra.lift_of] at h
  exact LinearMap.congr_fun h x

theorem mem_typePart (x : Y.Fm i j b) : x ∈ ToricLatticeDenominators.typePart Y i j b ↔
    ∀ u : Y.U, Y.actG i j b u x = ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  simp [ToricLatticeDenominators.typePart, Submodule.mem_iInf]

theorem jointSpan_eq : ToricLatticeDenominators.V0 Y i j b = Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b := by
  rw [Formalism.MainNotions.IntegralHeckeForms.V0, ← typePart_eq, ← eOp_eq]
  apply le_antisymm
  · rintro x ⟨⟨y, rfl⟩, hx⟩
    exact ⟨_, hx, eOp_idem Y i j b y⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, (mem_typePart Y i j b _).2 fun u => ?_⟩
    rw [← eOp_comm, (mem_typePart Y i j b x).1 hx u, map_smul]

end Objects

section PartB

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

def away (Q : Finset (PlE D.host)) : Set (Y.Dat i j b) := {d | Disjoint (Y.lev i j b d) Q}

section Ext

variable (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']

theorem eExt_toFrac (y : O' ⊗[X.O i] Y.Fm i j b) :
    ToricLatticeDenominators.eExt Y i j b O' (toFrac _ _ O' y) =
      toFrac _ _ O' ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O' y) := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_eExt (L : Submodule O' (O' ⊗[X.O i] Y.Fm i j b)) :
    (L.map (toFrac _ _ O')).map (ToricLatticeDenominators.eExt Y i j b O') =
      (L.map ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O')).map (toFrac _ _ O') := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext (eExt_toFrac Y i j b O')

theorem thetaExt_eq : (ToricLatticeDenominators.ThetaExt Y i j b O').map (ToricLatticeDenominators.eExt Y i j b O') =
    ((Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Set.univ).baseChange O').map (toFrac _ _ O') := by
  have h1 : ToricLatticeDenominators.ThetaExt Y i j b O' =
      ((Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Set.univ).baseChange O').map (toFrac _ _ O') := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, ToricLatticeDenominators.ThetaExt, Submodule.map_coe, Set.image_image,
      Formalism.MainNotions.IntegralHeckeForms.Th, Set.image_univ]
    congr 1
    exact Set.image_congr fun x _ => by simp [toFrac_tmul]
  rw [h1, map_eExt, Formalism.MainNotions.IntegralHeckeForms.eTh]
  congr 1
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Submodule.map_coe, Submodule.map_coe, Set.image_image, Set.image_image]
  rfl

variable (k : ℕ) [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O']

def up : X.Ok i k ⊗[X.O i] Y.Fm i j b →ₗ[X.Ok i k] O' ⊗[X.O i] Y.Fm i j b :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap (X.Ok i k) O') LinearMap.id

theorem up_eq (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) : up Y i j b O' k y =
    LinearMap.rTensor (Y.Fm i j b) (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap y := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem incl_eq (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) :
    ToricLatticeDenominators.incl Y i j b O' k y = toFrac _ _ O' (up Y i j b O' k y) := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem up_e (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) :
    up Y i j b O' k ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k) y) =
      (Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O' (up Y i j b O' k y) := by
  induction y with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def ext (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Submodule O' (O' ⊗[X.O i] Y.Fm i j b) :=
  Submodule.span O' (up Y i j b O' k '' L)

theorem ext_span (S : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    ext Y i j b O' k (Submodule.span _ S) = Submodule.span O' (up Y i j b O' k '' S) := by
  rw [ext, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]

theorem span_incl_map (S : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    (Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S)).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k ((Submodule.span _ S).map ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k)))).map
        (toFrac _ _ O') := by
  have : Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S) =
      (Submodule.span O' (up Y i j b O' k '' S)).map (toFrac _ _ O') := by
    rw [Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => incl_eq Y i j b O' k x
  rw [this, map_eExt, Submodule.map_span, Submodule.map_span (R₂ := X.Ok i k), ext_span, Set.image_image,
    Set.image_image]
  congr 2
  exact Set.image_congr fun x _ => (up_e Y i j b O' k x).symm

theorem thetaPsi_eq (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) :
    (ToricLatticeDenominators.ThetaPsi Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k (Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ (away Y i j b Q))).map (toFrac _ _ O') := by
  rw [Formalism.MainNotions.IntegralHeckeForms.eThPsi, Formalism.MainNotions.IntegralHeckeForms.ThPsi, ← span_incl_map, Set.image_iUnion₂]
  rfl

theorem thetaMt_eq (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) :
    (ToricLatticeDenominators.ThetaMt Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k (Formalism.MainNotions.IntegralHeckeForms.eThPMt Y i j b k Q ψ)).map (toFrac _ _ O') := by
  rw [Formalism.MainNotions.IntegralHeckeForms.eThPMt, ← Submodule.span_eq ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)),
    ← span_incl_map, Submodule.map_coe, Set.image_image]
  rfl

theorem ext_baseChange (V : Submodule (X.O i) (Y.Fm i j b)) :
    ext Y i j b O' k (V.baseChange (X.Ok i k)) = V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span, Submodule.map_coe,
    Submodule.map_coe, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => by simp [up]

theorem isLatIn_toFrac (hi : Function.Injective (algebraMap (X.Ok i k) O')) [Module.Finite (X.Ok i k) O']
    (M : Submodule O' (O' ⊗[X.O i] Y.Fm i j b)) :
    ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O') (M.map (toFrac _ _ O')) ↔
      Formalism.MainNotions.IntegralHeckeForms.IsLatIn M (((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange O') := by
  have := X.Ok_fin i k
  have : Module.Finite (X.O i) O' := Module.Finite.trans (X.Ok i k) O'
  have hi' : Function.Injective (algebraMap (X.O i) O') := by
    rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']
    exact hi.comp (X.Ok_inj i k)
  rw [isLatIn_iff, ToricLatticeDenominators.invariantSpanBaseChange, span_frac_eq _ _ _ hi', jointSpan_eq,
    isLatIn_map_iff _ (toFrac_injective _ _ _)]

end Ext

theorem ext_self (k : ℕ) (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    ext Y i j b (X.Ok i k) k L = L := by
  have : ∀ y, up Y i j b (X.Ok i k) k y = y := by
    intro y
    induction y with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [ext, Set.image_congr fun y _ => this y, Set.image_id', Submodule.span_eq]

theorem partBAt_iff (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ) (ε : ℝ)
    (hΘ : Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Set.univ)
      ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)))
    (hQ : Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ Set.univ) :
    ToricLatticeDenominators.partBAt Y i j b k Q ψ ε ↔
      Formalism.MainNotions.IntegralHeckeForms.IdxAt Y i j b Set.univ k Q ψ ε ∧
      Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ Set.univ)
        (((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)) ∧
      Formalism.MainNotions.IntegralHeckeForms.InclAt Y i j b Set.univ k Q ψ := by
  have hQ' : Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k Q ψ Set.univ := by
    rw [Formalism.MainNotions.IntegralHeckeForms.eThPsi, hQ]; rfl
  have hup : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O'] [Algebra (X.Ok i k) O']
      [IsScalarTower (X.O i) (X.Ok i k) O'] (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)),
      Submodule.span O' ((LinearMap.rTensor (Y.Fm i j b)
        (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap) '' (L : Set _)) = ext Y i j b O' k L := by
    intro O' _ _ _ _ _ _ L
    rw [ext, Set.image_congr fun y _ => up_eq Y i j b O' k y]
  constructor
  · intro h
    refine ⟨fun O' _ _ _ _ _ _ hi hf M hM => ?_, ?_, ?_⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := (h O' hi).2.2 _ ((isLatIn_toFrac Y i j b O' k hi M).2 hM)
      rw [eq_sIdx_of_isIdx hx, eq_sIdx_of_isIdx hy, thetaPsi_eq, thetaExt_eq,
        sIdx_map _ (toFrac_injective _ _ _), sIdx_map _ (toFrac_injective _ _ _), hQ'] at hxy
      rw [hup]; exact hxy
    · have h1 := (h (X.Ok i k) Function.injective_id).1
      rwa [thetaPsi_eq, isLatIn_toFrac Y i j b _ k Function.injective_id, ext_self, hQ'] at h1
    · have h1 := (h (X.Ok i k) Function.injective_id).2.1
      rwa [thetaPsi_eq, thetaMt_eq, Submodule.map_le_map_iff_of_injective (toFrac_injective _ _ _),
        ext_self, ext_self, hQ'] at h1
  · rintro ⟨h1, h2, h3⟩ O' _ _ _ _ _ _ hf hi
    have := X.Ok_fin i k
    have : Module.Finite (X.O i) O' := Module.Finite.trans (X.Ok i k) O'
    have hi' : Function.Injective (algebraMap (X.O i) O') := by
      rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']
      exact hi.comp (X.Ok_inj i k)
    have l1 : ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O')
        ((ToricLatticeDenominators.ThetaPsi Y i j b O' k Q ψ).map (ToricLatticeDenominators.eExt Y i j b O')) := by
      rw [thetaPsi_eq, isLatIn_toFrac Y i j b O' k hi, hQ', ← ext_baseChange Y i j b O' k]
      exact isLatIn_span hi _ h2
    have l2 : ToricLatticeDenominators.IsLatIn (ToricLatticeDenominators.invariantSpanBaseChange Y i j b O')
        ((ToricLatticeDenominators.ThetaExt Y i j b O').map (ToricLatticeDenominators.eExt Y i j b O')) := by
      rw [thetaExt_eq, isLatIn_toFrac Y i j b O' k hi, Submodule.baseChange_eq_span,
        Submodule.baseChange_eq_span]
      exact isLatIn_span hi' _ hΘ
    refine ⟨l1, ?_, fun M hM => ⟨_, _, isIdx_sIdx _ hM l1, isIdx_sIdx _ hM l2, ?_⟩⟩
    · rw [thetaPsi_eq, thetaMt_eq, hQ']
      exact Submodule.map_mono (Submodule.span_mono (Set.image_mono h3))
    · obtain ⟨M, rfl⟩ : ∃ M', M = Submodule.map (toFrac _ _ O') M' :=
        ⟨_, (Submodule.map_comap_eq_of_surjective (toFrac_surjective _ _ O' hi') M).symm⟩
      have := h1 O' hi hf M ((isLatIn_toFrac Y i j b O' k hi M).1 hM)
      rw [thetaPsi_eq, thetaExt_eq, sIdx_map _ (toFrac_injective _ _ _), sIdx_map _ (toFrac_injective _ _ _),
        hQ', ← hup]
      exact this

end PartB

section Basis

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

theorem AOp_apply (x : Y.Fm i j b) : ToricLatticeDenominators.AOp Y i j b x = Formalism.MainNotions.IntegralHeckeForms.AO Y i j b x := by
  simp only [ToricLatticeDenominators.AOp, Formalism.MainNotions.IntegralHeckeForms.AO, LinearMap.smul_apply, card_eq (N := N), Nat.cast_smul_eq_nsmul]
  rfl

theorem ATheta_eq : ToricLatticeDenominators.ATheta Y i j b =
    (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Set.univ).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b) := by
  rw [ToricLatticeDenominators.ATheta, Formalism.MainNotions.IntegralHeckeForms.Th, Set.image_univ]
  congr 1
  exact LinearMap.ext (AOp_apply Y i j b)

theorem card_ne_zero : ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) ≠ 0 := by
  haveI : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  haveI : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  haveI : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  exact Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'

theorem eTh_isLatIn (Sg : Set (Y.Dat i j b))
    (h : ToricLatticeDenominators.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) ((Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b))) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg) ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)) := by
  set n : X.O i := ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) with hn
  have hn0 : algebraMap (X.O i) (FractionRing (X.O i)) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (card_ne_zero i)
  have hinj : Function.Injective (n • LinearMap.id : Y.Fm i j b →ₗ[X.O i] Y.Fm i j b) := by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    rw [← algebraMap_smul (FractionRing (X.O i)) n x, ← algebraMap_smul (FractionRing (X.O i)) n y] at hxy
    exact smul_right_injective _ hn0 hxy
  have e1 : (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg).map (n • LinearMap.id) =
      (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b) := by
    rw [Formalism.MainNotions.IntegralHeckeForms.eTh, ← Submodule.map_comp]; rfl
  have e2 : ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).map (n • LinearMap.id) =
      (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.smul_mem _ n hx
    · intro x hx
      refine ⟨(algebraMap (X.O i) (FractionRing (X.O i)) n)⁻¹ • x, Submodule.smul_mem (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) _ hx, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [← algebraMap_smul (FractionRing (X.O i)) n, smul_inv_smul₀ hn0]
  rw [← isLatIn_map_iff _ hinj, e1, e2, ← isLatIn_iff]
  exact h

variable (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y)

theorem isBasisSeries_of_basisOf (hE : E.Dat0 i j b = Set.univ) (S : Finset (Y.Dat i j b))
    (h1 : Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b))
    (h2 : Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) S) :
    ToricLatticeDenominators.IsBasisSeries Y i j b (fun a : Fin S.card => (S.equivFin.symm a : Y.Dat i j b)) := by
  rw [Formalism.MainNotions.IntegralHeckeForms.SgJ, hE] at h1 h2
  have hr : (Set.range fun a : Fin S.card => ToricLatticeDenominators.AOp Y i j b (Y.th i j b (S.equivFin.symm a))) =
      (fun a => Formalism.MainNotions.IntegralHeckeForms.AO Y i j b (Y.th i j b a)) '' ↑S := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (S.equivFin.symm a).2, (AOp_apply Y i j b _).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨S.equivFin ⟨a, ha⟩, by simp [AOp_apply]⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ATheta_eq, ← h2.2.2]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [ATheta_eq, jointSpan_eq]; exact h1.2.2
  · simp only [AOp_apply]
    exact h2.2.1.comp _ S.equivFin.symm.injective
  · rw [hr, ATheta_eq, h2.2.2]

open Classical in

theorem basisOf_of_isBasisSeries (hE : E.Dat0 i j b = Set.univ) {n : ℕ} (d : Fin n → Y.Dat i j b)
    (h : ToricLatticeDenominators.IsBasisSeries Y i j b d) :
    Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) ∧
      Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) (Finset.univ.image d) := by
  rw [Formalism.MainNotions.IntegralHeckeForms.SgJ, hE]
  obtain ⟨⟨-, h1⟩, h2, h3⟩ := h
  rw [ATheta_eq, jointSpan_eq] at h1
  rw [ATheta_eq] at h3
  simp only [AOp_apply] at h2 h3
  refine ⟨⟨by rw [hE], fun x hx => ?_, h1⟩, Set.subset_univ _, ?_, ?_⟩
  · rw [← h1]; exact Submodule.subset_span hx
  · have hc : ∀ a : ↥(Finset.univ.image d), ∃ t, d t = a := fun a => by
      obtain ⟨t, -, ht⟩ := Finset.mem_image.1 a.2
      exact ⟨t, ht⟩
    choose t ht using hc
    have := h2.comp t (fun a a' e => Subtype.ext (by rw [← ht a, ← ht a', e]))
    convert this using 1
    funext a
    simp [ht]
  · rw [← h3, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
    rfl




end Basis

section Main

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X)

theorem partA_of_partAT {i : X.Tw} {Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ} {eps' : ℝ}
    (h : partAT bkP i Q k' ψ' eps') : partA bkP i Q k' ψ' eps' := by
  obtain ⟨e, h0, h1, h2⟩ := h
  have hi : (0 : ℝ) ≤ (nu X i : ℝ) := Nat.cast_nonneg _
  refine (Finset.sum_le_sum fun s hs => h2 s ((mem_SigG bkP i s).1 hs)).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => add_nonneg hi (h0 s)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y)

open Classical in

def GoodAll (N0 : X.Tw → ℕ) (i : X.Tw) (eps' : ℝ) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b))
    (A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) : Prop :=
  PsiOk i (Formalism.MainNotions.IntegralHeckeForms.levs Y i S ∪ A) Q k' ψ' ∧ ToricLatticeDenominators.ThroughDel Y i k' Q (ψ'.comp (X.art i Q)) ∧
    ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧ ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
      ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
        (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
          Formalism.MainNotions.IntegralHeckeForms.IdxAt Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q))) (epsB j b) ∧
          Formalism.MainNotions.IntegralHeckeForms.IsLatIn
            (Formalism.MainNotions.IntegralHeckeForms.eThPsi Y i j b k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q))) (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b))
            (((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k')) ∧
          Formalism.MainNotions.IntegralHeckeForms.InclAt Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) k' Q (psiAt b ((ψ' ^ a).comp (X.art i Q)))) ∧
        partAT bkP i Q k' (ψ' ^ a) eps' ∧ partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps'

def exportAll (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), GoodAll bkP Y E N0 i eps' S A Q k' ψ'

def RankAt (i : X.Tw) : Prop :=
  ∃ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    Formalism.MainNotions.IntegralHeckeForms.FullRk Y E i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) ∧
      Formalism.MainNotions.IntegralHeckeForms.BasisOf Y i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ Y E i j b) (S j b)

open Classical in
theorem psiOk_union_iff {i : X.Tw} (B A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) :
    PsiOk i (B ∪ A) Q k' ψ' ↔ PsiOk i A Q k' ψ' ∧ Disjoint B Q := by
  simp only [PsiOk, Finset.disjoint_union_right, disjoint_comm (a := B)]
  tauto

theorem disjoint_levs_iff (i : X.Tw) (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) (Q : Finset (PlE D.host)) :
    Disjoint (Formalism.MainNotions.IntegralHeckeForms.levs Y i S) Q ↔
      ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ∀ a ∈ S j b, Disjoint (Y.lev i j b a) Q := by
  simp only [Formalism.MainNotions.IntegralHeckeForms.levs, Finset.disjoint_biUnion_left, Finset.mem_univ, true_imp_iff]

def AwaySpans (i : X.Tw) : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE N →* (X.Ok i k)ˣ),
    (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → Disjoint Q (X.S0 i) →
    Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ (away Y i j b Q) = Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ Set.univ

open Classical in

theorem exportAt_iff (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat bkP.ex) (N0 : X.Tw → ℕ) (i : X.Tw)
    (hE : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = Set.univ) (hQ : AwaySpans bkP.ex i) :
    ToricLatticeDenominators.exportAt bkP N0 i ↔ (SetHyp bkP i → RankAt bkP.ex E i) ∧ exportAll bkP bkP.ex E N0 i := by
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ {n : ℕ} (d : Fin n → bkP.ex.Dat i j b),
      ToricLatticeDenominators.IsBasisSeries bkP.ex i j b d → ∀ {A Q : Finset (PlE D.host)} {k' : ℕ}
      {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}, PsiOk i A Q k' ψ' → ∀ (ψ : GE N →* (X.Ok i k')ˣ) (ε : ℝ),
      (ToricLatticeDenominators.partBAt bkP.ex i j b k' Q ψ ε ↔
        Formalism.MainNotions.IntegralHeckeForms.IdxAt bkP.ex i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ bkP.ex E i j b) k' Q ψ ε ∧
        Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eThPsi bkP.ex i j b k' Q ψ (Formalism.MainNotions.IntegralHeckeForms.SgJ bkP.ex E i j b))
          (((Formalism.MainNotions.IntegralHeckeForms.V0 bkP.ex i j b).restrictScalars (X.O i)).baseChange (X.Ok i k')) ∧
        Formalism.MainNotions.IntegralHeckeForms.InclAt bkP.ex i j b (Formalism.MainNotions.IntegralHeckeForms.SgJ bkP.ex E i j b) k' Q ψ) := by
    intro j hj b n d hd A Q k' ψ' hψ ψ ε
    rw [Formalism.MainNotions.IntegralHeckeForms.SgJ, hE j hj b]
    refine partBAt_iff _ i j b k' Q ψ ε (eTh_isLatIn _ i j b _ ?_)
      (hQ j hj b k' Q ψ (fun P hP => (hψ.1 P hP).1) (Finset.disjoint_union_right.1 hψ.2.1).1)
    rw [← ATheta_eq, ← jointSpan_eq]; exact hd.1
  constructor
  · intro h
    refine ⟨fun hs => ?_, fun hs eps' he _ S _ A => ?_⟩
    · obtain ⟨n, d, hd, -⟩ := h hs
      exact ⟨fun j b => Finset.univ.image (d j b), fun j hj b =>
        basisOf_of_isBasisSeries _ i j b E (hE j hj b) _ (hd j hj b)⟩
    · obtain ⟨n, d, hd, H⟩ := h hs
      obtain ⟨Q, k', ψ', e, h1, -, h2, h3, h4, h5⟩ := H eps' he (Formalism.MainNotions.IntegralHeckeForms.levs bkP.ex i S ∪ A)
      refine ⟨Q, k', ψ', h1, h2, e, h3, h4, fun a ha => ?_⟩
      obtain ⟨-, g2, g3, g4⟩ := h5 a ha
      exact ⟨fun j hj b => (key j hj b _ (hd j hj b) h1 _ _).1 (g3 j hj b), g2, g4⟩
  · rintro ⟨h1, h2⟩ hs
    obtain ⟨S, hS⟩ := h1 hs
    have hd := fun j hj b => isBasisSeries_of_basisOf _ i j b E (hE j hj b) (S j b) (hS j hj b).1 (hS j hj b).2
    refine ⟨fun j b => (S j b).card, fun j b a => (S j b).equivFin.symm a, hd, fun eps' he A => ?_⟩
    obtain ⟨Q, k', ψ', g1, g2, e, g3, g4, g5⟩ :=
      h2 hs eps' he (fun j hj b => (hS j hj b).1) S (fun j hj b => (hS j hj b).2) A
    obtain ⟨g0, g1'⟩ := (psiOk_union_iff _ _ _ _ _).1 g1
    refine ⟨Q, k', ψ', e, g0, fun j hj b a => (disjoint_levs_iff _ i S Q).1 g1' j hj b _
      ((S j b).equivFin.symm a).2, g2, g3, g4, fun a ha => ?_⟩
    obtain ⟨f1, f2, f3⟩ := g5 a ha
    exact ⟨partA_of_partAT bkP f2, f2, fun j hj b => (key j hj b _ (hd j hj b) g0 _ _).2 (f1 j hj b), f3⟩

end Main

end GlobalTheory.ExportCompare

end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistIndex

open NumberField IsDedekindDomain
open scoped TensorProduct

section Local

open Formalism.L2.Col Formalism.EigenvalueLevelCeiling

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] {emb : K →+* FractionRing O'}

def Induces (emb : K →+* FractionRing O') (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : K, v.valuation K x ≤ 1 ↔ emb x ∈ (algebraMap O' (FractionRing O')).range

def Induces.hom (h : Induces emb v) : Ow v →+* O' :=
  ((RingEquiv.ofBijective (algebraMap O' (FractionRing O')).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective O' (FractionRing O') (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩).symm : _ →+* O').comp
    ((emb.comp (algebraMap (Ow v) K)).codRestrict _ fun r => (h _).1 ((mem_range_ow_iff v _).1 ⟨r, rfl⟩))

omit [IsDomain O'] [IsDiscreteValuationRing O'] in
theorem Induces.hom_spec (h : Induces emb v) (r : Ow v) :
    algebraMap O' (FractionRing O') (h.hom r) = emb (algebraMap (Ow v) K r) :=
  congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap O' (FractionRing O')).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective O' (FractionRing O') (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply _)

theorem Induces.hom_injective (h : Induces emb v) : Function.Injective h.hom := fun a b e =>
  algebraMap_ow_injective v (emb.injective (by rw [← h.hom_spec, ← h.hom_spec, e]))

theorem Induces.hom_local (h : Induces emb v) : IsLocalHom h.hom := by
  refine ⟨fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  have e : emb (algebraMap (Ow v) K r) * algebraMap O' (FractionRing O') s = 1 := by
    rw [← h.hom_spec, ← map_mul, hs, map_one]
  have r0 : algebraMap (Ow v) K r ≠ 0 := fun h0 => by simp [h0] at e
  obtain ⟨t, ht⟩ := (mem_range_ow_iff v _).2 ((h (algebraMap (Ow v) K r)⁻¹).2
    ⟨s, by rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right e⟩)
  refine IsUnit.of_mul_eq_one t (algebraMap_ow_injective v ?_)
  rw [map_mul, ht, mul_inv_cancel₀ r0, map_one]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type} [AddCommGroup W] [Module (FractionRing O') W] [Module O' W] [IsScalarTower O' (FractionRing O') W]

omit [IsScalarTower (𝓞 K) K V] in

theorem relLength_read (h : Induces emb v) (rd : V →ₛₗ[emb] W) {ι : Type} [Fintype ι] (b : Module.Basis ι K V)
    (hli : LinearIndependent (FractionRing O') fun a => rd (b a)) :
    ∃ e : ℕ, 0 < e ∧ (∀ n : ℕ, IsDiscreteValuationRing.addVal O' (n : O') =
        IsDiscreteValuationRing.addVal (Ow v) (n : Ow v) * e) ∧
      ∀ A B : Submodule (𝓞 K) V,
        relLength (Submodule.span O' (rd '' A)) (Submodule.span O' (rd '' B)) = lenW v A B * e := by
  let _ : Algebra (Ow v) O' := h.hom.toAlgebra
  have : IsLocalHom (algebraMap (Ow v) O') := h.hom_local
  have : FaithfulSMul (Ow v) O' := (faithfulSMul_iff_algebraMap_injective _ _).2 h.hom_injective
  let _ : Module (Ow v) W := Module.compHom W h.hom
  have : IsScalarTower (Ow v) O' W := ⟨fun r s x => mul_smul (h.hom r) s x⟩
  have hr : ∀ (r : Ow v) (x : V), rd (r • x) = h.hom r • rd x := fun r x => by
    rw [ow_smul_def, map_smulₛₗ, ← h.hom_spec, algebraMap_smul]
  let r : V →ₗ[Ow v] W := ⟨rd.toAddHom, hr⟩
  let g : O' ⊗[Ow v] V →ₗ[O'] W := r.liftBaseChange O'
  have hg : ∀ (s : O') (x : V), g (s ⊗ₜ x) = s • rd x := fun s x => LinearMap.liftBaseChange_tmul _ _ _ _
  have hnorm : ∀ t : O' ⊗[Ow v] V, ∃ c : Ow v, c ≠ 0 ∧ ∃ s : ι → O', c • t = ∑ a, s a ⊗ₜ b a := by
    intro t
    induction t with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul s x =>
      obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (Ow v)) (b.repr x)
      choose y hy using hc
      refine ⟨c, nonZeroDivisors.coe_ne_zero c, fun a => y a • s, ?_⟩
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← b.sum_repr x, Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [TensorProduct.smul_tmul, ← smul_assoc, ← hy a, algebraMap_smul]
    | add x y hx hy =>
      obtain ⟨c, hc, s, hs⟩ := hx
      obtain ⟨d, hd, u, hu⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, d • s + c • u, ?_⟩
      rw [smul_add, mul_comm c d, mul_smul, hs, mul_comm d c, mul_smul, hu, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, TensorProduct.smul_tmul']
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨c, hc, s, hs⟩ := hnorm t
    have h1 : ∑ a, algebraMap O' (FractionRing O') (s a) • rd (b a) = 0 := by
      have := congrArg g hs
      rw [← algebraMap_smul O' c, map_smul, ht, smul_zero, map_sum] at this
      simpa only [hg, algebraMap_smul] using this.symm
    have h2 : ∀ a, s a = 0 := fun a => (map_eq_zero_iff _ (IsFractionRing.injective O' (FractionRing O'))).1
      (Fintype.linearIndependent_iff.1 hli _ h1 a)
    have h3 : c • t = 0 := by simp [hs, h2]
    have cK : algebraMap (Ow v) K c ≠ 0 := (map_ne_zero_iff _ (algebraMap_ow_injective v)).2 hc
    let f : V →ₗ[Ow v] V := (((algebraMap (Ow v) K c)⁻¹ • LinearMap.id : V →ₗ[K] V)).restrictScalars (Ow v)
    have h4 : ∀ u : O' ⊗[Ow v] V, f.lTensor O' (c • u) = u := by
      intro u
      induction u with
      | zero => simp
      | tmul s x =>
        rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul]
        congr 1
        exact inv_smul_smul₀ cK x
      | add x y hx hy => rw [smul_add, map_add, hx, hy]
    rw [← h4 t, h3, map_zero]
  have hsp : ∀ A : Submodule (𝓞 K) V, Submodule.span O' (rd '' A) = ((atW v A).baseChange O').map g := by
    intro A
    rw [atW, Submodule.baseChange_span, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => by simp [hg]
  refine ⟨_, ramificationIdx_maximalIdeal_pos (Ow v) O', fun n => ?_, fun A B => ?_⟩
  · rw [← addVal_algebraMap O', map_natCast (algebraMap (Ow v) O')]
  · rw [hsp, hsp, relLength_map_of_injective g hinj]
    exact length_baseChange_subquotient_dvr (Ow v) O' _ _

omit [NumberField K] [IsDomain O'] [IsDiscreteValuationRing O'] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module O' W]
  [IsScalarTower O' (FractionRing O') W] in

theorem exists_read {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (x : ι → W) :
    ∃ rd : V →ₛₗ[emb] W, ∀ a, rd (b a) = x a := by
  classical
  refine ⟨⟨⟨fun y => ∑ a, emb (b.repr y a) • x a, fun y z => ?_⟩, fun r y => ?_⟩, fun a => ?_⟩
  · simp [add_smul, Finset.sum_add_distrib]
  · simp [mul_smul, Finset.smul_sum]
  · simp [Finsupp.single_apply, apply_ite emb]

variable [StarRing K]

theorem plc_eq_prW (v : HeightOneSpectrum (𝓞 K)) : plc v = prW v := eq_prW_of_mem v (plc_prime v) (plc_mem v)

theorem addVal_plc (v : HeightOneSpectrum (𝓞 K)) :
    (((IsDiscreteValuationRing.addVal (Ow v) ((plc v : ℕ) : Ow v)).toNat : ℕ) : ℤ) = ramw v := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow v)
  obtain ⟨u, hu⟩ := prW_eq_unit_mul_pow v hπ
  rw [plc_eq_prW, IsDiscreteValuationRing.addVal_def _ u hπ _ hu, ENat.toNat_natCast]
  exact Formalism.L2.DIV.lf_eW_eq_ramw v

omit [StarRing K] in
theorem lix_eq_signedLength (v : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lix v A B = signedLength (atW v A) (atW v B) := by
  rw [lix, ← lidxW_eq_lidx, lidxW, lenW_inf, inf_comm, lenW_inf]
  rfl

theorem lix_le_of_read (h : Induces emb v) (rd : V →ₛₗ[emb] W) {ι : Type} [Fintype ι] (b : Module.Basis ι K V)
    (hli : LinearIndependent (FractionRing O') fun a => rd (b a)) {Z : Submodule K V} {M Θ X : Submodule (𝓞 K) V}
    (hM : IsLatIn Z M) (hΘ : IsLatIn Z Θ)
    (hc : LengthCommensurable (Submodule.span O' (rd '' Θ)) (Submodule.span O' (rd '' X))) {ε : ℝ}
    (hs : Formalism.MainNotions.IntegralHeckeForms.sIdx (plc v) (Submodule.span O' (rd '' Θ)) (Submodule.span O' (rd '' X)) ≤ ε) :
    (lix v M X : ℝ) ≤ (lix v M Θ : ℝ) + (ramw v : ℝ) * ε := by
  obtain ⟨e, he, hv, hl⟩ := relLength_read h rd b hli
  have key : ∀ {A B : Submodule (𝓞 K) V}, IsLatIn Z A → IsLatIn Z B → relLength (atW v A) (atW v B) ≠ ⊤ := by
    intro A B hA hB
    refine relLength_ne_top_of_isLatIn (V := atW v A ⊔ atW v B) ⟨atW_fg v hA.1, le_sup_left, fun x hx => ?_⟩
      ⟨atW_fg v hB.1, le_sup_right, fun x hx => ?_⟩
    all_goals
      have hx' : x ∈ Z := by
        refine (sup_le ?_ ?_ : _ ≤ Z.restrictScalars (Ow v)) hx
        · exact Submodule.span_le.2 fun y hy => hA.2.le (Submodule.subset_span hy)
        · exact Submodule.span_le.2 fun y hy => hB.2.le (Submodule.subset_span hy)
    · rw [← hA.2] at hx'
      obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (Ow v)) K _ x hx'
      exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
    · rw [← hB.2] at hx'
      obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (Ow v)) K _ x hx'
      exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  have e0 : (e : ℕ∞) ≠ 0 := by exact_mod_cast he.ne'
  have hfin : ∀ {A B : Submodule (𝓞 K) V},
      relLength (Submodule.span O' (rd '' A)) (Submodule.span O' (rd '' B)) ≠ ⊤ → relLength (atW v A) (atW v B) ≠ ⊤ := by
    intro A B h1 h2
    rw [hl, show lenW v A B = ⊤ from h2, ENat.top_mul e0] at h1
    exact h1 rfl
  have c1 : LengthCommensurable (atW v M) (atW v Θ) := ⟨key hM hΘ, key hΘ hM⟩
  have c2 : LengthCommensurable (atW v Θ) (atW v X) := ⟨hfin hc.1, hfin hc.2⟩
  have hr : (0 : ℝ) < ramw v := by exact_mod_cast lt_of_lt_of_le zero_lt_one (one_le_ramw v)
  have hp : (((IsDiscreteValuationRing.addVal (Ow v) ((plc v : ℕ) : Ow v)).toNat : ℕ) : ℝ) = ramw v := by
    exact_mod_cast addVal_plc v
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h3 : signedLength (Submodule.span O' (rd '' Θ)) (Submodule.span O' (rd '' X)) =
      signedLength (atW v Θ) (atW v X) * e := by
    rw [signedLength, hl, hl, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_natCast, signedLength, _root_.sub_mul]
    push_cast
    rfl
  rw [sIdx_eq_signedLength_div, h3, hv, ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hp, Int.cast_mul, Int.cast_natCast,
    mul_div_mul_right _ _ he'.ne', div_le_iff₀ hr] at hs
  rw [lix_eq_signedLength, lix_eq_signedLength, c1.signedLength_eq_add c2]
  push_cast
  linarith

end Local

section Export

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.IntegralHeckeForms GlobalTheory.ExportCompare
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (φ : G D.host.E N.Om →* (X.Ok i k)ˣ)
  (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O'] [Algebra (X.Ok i k) O']
  [IsScalarTower (X.O i) (X.Ok i k) O']
  {K : Type} [Field K] [NumberField K] {emb : K →+* FractionRing O'}
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def Reads (e : V →ₗ[K] V) (Θ Θψ : Submodule (𝓞 K) V) (rd : V →ₛₗ[emb] FmExt Y i j b O') : Prop :=
  (∃ (n : ℕ) (β : Module.Basis (Fin n) K V), LinearIndependent (FractionRing O') fun a => rd (β a)) ∧
  (∀ x, rd (e x) = eExt Y i j b O' (rd x)) ∧
  Submodule.span O' (rd '' Θ) =
    Submodule.span O' ((fun a => (1 : FractionRing O') ⊗ₜ[X.O i] Y.th i j b a) '' SgJ Y E i j b) ∧
  Submodule.span O' (rd '' Θψ) =
    Submodule.span O' (incl Y i j b O' k '' ⋃ a ∈ SgJ Y E i j b, Y.thPsi i j b k Q φ a)

variable {Y E i j b k Q φ O'}

omit [IsDomain O'] [IsDiscreteValuationRing O'] [NumberField K] in

theorem Reads.comap {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    {e : V →ₗ[K] V} {Θ Θψ : Submodule (𝓞 K) V} {rd : V →ₛₗ[emb] FmExt Y i j b O'}
    (h : Reads Y E i j b k Q φ O' e Θ Θψ rd) (f : V' →ₗ[K] V) (hf : Function.Bijective f) {e' : V' →ₗ[K] V'}
    (he : f ∘ₗ e' = e ∘ₗ f) :
    Reads Y E i j b k Q φ O' e' (Θ.comap (f.restrictScalars (𝓞 K))) (Θψ.comap (f.restrictScalars (𝓞 K))) (rd.comp f) := by
  obtain ⟨⟨n, β, hβ⟩, h2, h3, h4⟩ := h
  have him : ∀ L : Submodule (𝓞 K) V, (rd.comp f) '' (L.comap (f.restrictScalars (𝓞 K))) = rd '' L := fun L => by
    rw [LinearMap.coe_comp, Set.image_comp]
    exact congrArg _ (Set.image_preimage_eq _ hf.2)
  refine ⟨⟨n, β.map (LinearEquiv.ofBijective f hf).symm, ?_⟩, fun x => ?_, by rw [him, h3], by rw [him, h4]⟩
  · convert hβ using 2 with a
    exact congrArg rd ((LinearEquiv.ofBijective f hf).apply_symm_apply _)
  · exact (congrArg rd (LinearMap.congr_fun he x)).trans (h2 _)

theorem Reads.lix_le [StarRing K] {v : HeightOneSpectrum (𝓞 K)} {e : V →ₗ[K] V} {Θ Θψ : Submodule (𝓞 K) V}
    {rd : V →ₛₗ[emb] FmExt Y i j b O'} (h : Reads Y E i j b k Q φ O' e Θ Θψ rd) (hv : Induces emb v)
    (hl : X.l i = Formalism.EigenvalueLevelCeiling.plc v) (hi : Function.Injective (algebraMap (X.Ok i k) O')) (hf : Module.Finite (X.Ok i k) O')
    (h0 : IsLatIn (eTh Y i j b (SgJ Y E i j b)) ((V0 Y i j b).restrictScalars (X.O i)))
    (h1 : IsLatIn (eThPsi Y i j b k Q φ (SgJ Y E i j b)) (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)))
    {ε : ℝ} (h2 : IdxAt Y i j b (SgJ Y E i j b) k Q φ ε) {Z : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : Formalism.EigenvalueLevelCeiling.IsLatIn Z M) (hΘ : Formalism.EigenvalueLevelCeiling.IsLatIn Z (Θ.map (e.restrictScalars (𝓞 K)))) :
    (Formalism.EigenvalueLevelCeiling.lix v M (Θψ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (Formalism.EigenvalueLevelCeiling.lix v M (Θ.map (e.restrictScalars (𝓞 K))) : ℝ) + (Formalism.EigenvalueLevelCeiling.ramw v : ℝ) * ε := by
  obtain ⟨⟨n, β, hβ⟩, g2, g3, g4⟩ := h
  have hi' : Function.Injective (algebraMap (X.O i) O') := by
    rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']
    exact hi.comp (X.Ok_inj i k)
  have hmap : ∀ L : Submodule (𝓞 K) V, Submodule.span O' (rd '' (L.map (e.restrictScalars (𝓞 K)))) =
      (Submodule.span O' (rd '' L)).map (eExt Y i j b O') := fun L => by
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    exact congrArg _ (Set.image_congr fun x _ => g2 x)
  have eΘ : Submodule.span O' (rd '' (Θ.map (e.restrictScalars (𝓞 K)))) =
      ((eTh Y i j b (SgJ Y E i j b)).baseChange O').map (toFrac _ _ O') := by
    rw [hmap, g3, eTh, Th, Submodule.map_span, Submodule.map_span, Submodule.baseChange_span, Submodule.map_span]
    simp only [Set.image_image]
    refine congrArg _ (Set.image_congr fun a _ => ?_)
    rw [TensorProduct.mk_apply, toFrac_tmul, map_one]
    rfl
  have eX : Submodule.span O' (rd '' (Θψ.map (e.restrictScalars (𝓞 K)))) =
      (ext Y i j b O' k (eThPsi Y i j b k Q φ (SgJ Y E i j b))).map (toFrac _ _ O') := by
    rw [hmap, g4, span_incl_map]
    rfl
  have l0 := isLatIn_baseChange O' hi' h0
  have l1 : IsLatIn (ext Y i j b O' k (eThPsi Y i j b k Q φ (SgJ Y E i j b)))
      (((V0 Y i j b).restrictScalars (X.O i)).baseChange O') := by
    rw [← ext_baseChange Y i j b O' k]
    exact isLatIn_span hi _ h1
  refine lix_le_of_read hv rd β hβ hM hΘ ?_ ?_
  · rw [eΘ, eX]
    have := lengthCommensurable_of_isLatIn l0 l1
    unfold LengthCommensurable at this ⊢
    rwa [relLength_map_of_injective _ (toFrac_injective _ _ _), relLength_map_of_injective _ (toFrac_injective _ _ _)]
  · have := h2 O' hi hf _ l0
    rw [← Set.image_congr fun y _ => up_eq Y i j b O' k y, sIdx_eq (X.l i) _ ((eTh Y i j b (SgJ Y E i j b)).baseChange O'),
      signedLength, sub_self, Int.cast_zero, zero_div, zero_add] at this
    rw [eΘ, eX, sIdx_map _ (toFrac_injective _ _ _), ← hl]
    exact this

end Export

section Chain

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df}
  {P : Type} [Group P] [Finite P] {oc : OnConst}

def GoodPartLattice (O : OnObj S P oc) : Prop := ∀ j, IsLatIn (O.Zg j) (cut (O.Zg j) (O.Ms j))

def ThetaFullRank (O : OnObj S P oc) : Prop := AtPair S fun v => ∀ j, IsLatIn (O.Zg j) (O.eJ v j)

theorem goodPartLattice_of_leafSup {O : OnObj S P oc} (h : LeafSup O) : GoodPartLattice O := fun j => by
  obtain ⟨h1, h2⟩ := (h j).1
  refine ⟨h1.of_le inf_le_left, le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ x (h2.ge Submodule.mem_top)
  rw [Submodule.span_eq] at hc
  have c0 : algebraMap (𝓞 K) K c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero c)
  rw [← inv_smul_smul₀ c0 x, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hc, ((O.Zg j).restrictScalars (𝓞 K)).smul_mem _ hx⟩)

theorem leafTW1_of_places {O : OnObj S P oc}
    (h : AtPair S fun v => (∀ j, 0 ≤ O.ε0 v j ∧ (lix v (cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
      (lix v (cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (ramw v : ℝ) * O.ε0 v j) ∧ ∑ j, O.ε0 v j ≤ ((plc v : ℝ) ^ 2)⁻¹) :
    LeafTW1 O := by
  refine ⟨fun w hw => ⟨(h w hw).1.1, (h w hw).2.1⟩, fun w hw => ?_⟩
  have h1 := (h w hw).1.2
  have h2 := (h w hw).2.2
  rw [plc_conjPl] at h2
  rw [Finset.sum_add_distrib, div_eq_mul_inv]
  linarith

theorem sum_side_le {J : Type} [Fintype J] {m : ℕ} {ι : J → Fin m} (hι : Function.Injective ι) {ε : ℕ → Bool → ℝ}
    (h0 : ∀ j b, 0 ≤ ε j b) (b : Bool) : ∑ j, ε ((ι j : ℕ) + 1) b ≤ ∑ j ∈ Finset.Icc 1 m, ∑ b' : Bool, ε j b' := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := fun j => (ι j : ℕ) + 1) (f := fun j => ε j b)
    fun x _ y _ e => hι (Fin.ext (Nat.succ_injective e))]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => h0 n b).trans
    (Finset.sum_le_sum fun n _ => Finset.single_le_sum (f := ε n) (fun b' _ => h0 n b') (Finset.mem_univ b))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hn
  exact Finset.mem_Icc.2 ⟨Nat.le_add_left _ _, (ι j).2⟩

end Chain

section Record

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.OnTies GlobalTheory.IndefiniteRowSideFullHecke.PlaceBelowAllPowers
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem induces_embW (c : NChoice D) (w : D.what₂.places.Pl) : Induces (c.embW w) (D.plEq w) := fun x => by
  rw [← c.embW_w]
  by_cases hx : x = 0
  · subst hx
    simp
  · have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [D.val_eq w x hx, vAdd, ← WithTop.coe_zero, WithTop.coe_le_coe, neg_nonneg, ← WithZero.log_one,
      WithZero.log_le_log h0 one_ne_zero]

theorem l_eq_plc (c : NChoice D) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    D.ntw.l (c.twI (D.plEq.symm v)) = Formalism.EigenvalueLevelCeiling.plc v := by
  rw [c.twI_l, ← Formalism.L2.Col.prW_D, Equiv.apply_symm_apply, plc_eq_prW]

def chosenChar (c : NChoice D) (w : D.what₂.places.Pl) : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ :=
  (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m)

def ExportTie (c : NChoice D) (E : IntegralHeckeForms.XD D) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (ι : Fin D.R.m) (U : Subgroup Γ) (ψ : U →* D.what₂.LLˣ) (ph : ℂ)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∃ rd : (Fin (R.nW ι) → D.what₂.LL) →ₛₗ[c.embW (D.plEq.symm v)]
      FmExt D.nexp (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (c.Oe (D.plEq.symm v)),
    Reads D.nexp E (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (c.k' (D.plEq.symm v)) (c.Q (D.plEq.symm v))
      (chosenChar c (D.plEq.symm v)) (c.Oe (D.plEq.symm v)) ((R.FW ι).eOp fun g => (idemOf A.X).coeff g)
      (thetaBase R ι U ψ ph v p) (thetaTuple R ι U ψ ph (R.mu v)) rd

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def TiedAt (c : NChoice D) (E : IntegralHeckeForms.XD D) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J)
    (ι : Fin D.R.m) : Prop :=
  ∃ (T : Full D) (_ : Algebra T.J.Q.c.F D.what₂.LL) (R : RealDat D A T.J.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ)
    (z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι))
    (act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι))
    (inc : P →* Γ)
    (ℓ : Γ → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
    (U : Subgroup Γ) (ψ : U →* D.what₂.LLˣ) (ph : ℂ)
    (y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)),
    OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y ∧ ExportTie A c E R ι U ψ ph v p

variable {A}

theorem TiedAt.lix_le {c : NChoice D} {E : IntegralHeckeForms.XD D} {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
    {ι : Fin D.R.m} (t : TiedAt A c E O v i ι)
    (hM : Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg i) (Formalism.EigenvalueLevelCeiling.cut (O.Zg i) (O.Ms i))) (hΘ : Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg i) (O.eJ v i))
    (h0 : IntegralHeckeForms.IsLatIn (IntegralHeckeForms.eTh D.nexp (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (IntegralHeckeForms.SgJ D.nexp E _ _ _))
      ((IntegralHeckeForms.V0 D.nexp _ _ _).restrictScalars _))
    {ε : ℝ} (h1 : PartBAt D.nexp E (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (c.k' (D.plEq.symm v))
      (c.Q (D.plEq.symm v)) (chosenChar c (D.plEq.symm v)) ε) :
    (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg i) (O.Ms i)) (O.X₃ v i) : ℝ) ≤
      (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg i) (O.Ms i)) (O.eJ v i) : ℝ) + (Formalism.EigenvalueLevelCeiling.ramw v : ℝ) * ε := by
  obtain ⟨T, _, R, κ, v₀, h, fw, hinj, EX, p, wL, wF, nT, z, act, inc, ℓ, U, ψ, ph, y, t, rd, hrd⟩ := t
  have hr := hrd.comap (toForms h fw ι z) (toForms_bijective h fw ι z) t.e_eq
  have hv : Induces (c.embW (D.plEq.symm v)) v := by
    simpa using induces_embW c (D.plEq.symm v)
  unfold OnObj.eJ at hΘ ⊢
  rw [t.ThJ_eq] at hΘ ⊢
  rw [t.X₃_eq]
  exact hr.lix_le hv (l_eq_plc c v) (c.Oe_inj _) (c.Oe_fin _) h0 h1.1 h1.2.1 hM hΘ

theorem isLatIn_eTh {I : TwIn D} {i : D.ntw.Tw} (h : I.Ok i) {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    IntegralHeckeForms.IsLatIn (IntegralHeckeForms.eTh D.nexp i j b (IntegralHeckeForms.SgJ D.nexp I.E i j b)) ((IntegralHeckeForms.V0 D.nexp i j b).restrictScalars _) := by
  refine GlobalTheory.ExportCompare.eTh_isLatIn D.nexp i j b _ ⟨?_, (h.1 j hj b).2.2⟩
  have := (h.2 j hj b).2.2
  unfold TwIn.Sg at this
  rw [← this]
  exact Submodule.fg_span ((I.S i j b).finite_toSet.image _)

theorem succ_mem_Icc (ι : Fin D.R.m) : (ι : ℕ) + 1 ∈ Finset.Icc 1 D.R.m := Finset.mem_Icc.2 ⟨Nat.le_add_left _ _, ι.2⟩

abbrev Twist (i : D.ntw.Tw) : Type := Σ (Q : Finset (PlE D.host)) (k : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ

theorem exists_leafTW1_of_twGoodAt (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m) (c : NChoice D) (I : TwIn D) (hG : TwGoodAt D c I)
    (O : OnObj S P oc) (ι : Bs.J → Fin D.R.m) (hι : Function.Injective ι) (hM : GoodPartLattice O) (hΘ : ThetaFullRank O)
    (hT : AtPair S fun v => TwistedAt D (D.plEq.symm v) ∧ ∀ j, TiedAt A c I.E O v j (ι j)) :
    ∃ ε, LeafTW1 ({ O with ε0 := ε } : OnObj S P oc) := by
  have loc : ∀ v, ∃ ε : Bs.J → ℝ, (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j)) →
      (TwistedAt D (D.plEq.symm v) ∧ ∀ j, TiedAt A c I.E O v j (ι j)) →
      (∀ j, 0 ≤ ε j ∧ (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
        (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (Formalism.EigenvalueLevelCeiling.ramw v : ℝ) * ε j) ∧
      ∑ j, ε j ≤ ((Formalism.EigenvalueLevelCeiling.plc v : ℝ) ^ 2)⁻¹ := fun v => by
    by_cases hv : TwistedAt D (D.plEq.symm v)
    · obtain ⟨hI, -, ⟨ε, h0, h1, h2⟩, h3, -⟩ := hG _ hv
      have hψ : BlochKatoReduction.Gen.psiAt (c.sd (D.plEq.symm v)) ((BlochKatoReduction.Gen.psiAt (c.sd (D.plEq.symm v)) (c.psi' (D.plEq.symm v))).comp
          (D.ntw.art (c.twI (D.plEq.symm v)) (c.Q (D.plEq.symm v)))) = chosenChar c (D.plEq.symm v) := by
        cases c.sd (D.plEq.symm v)
        · ext g
          simp [BlochKatoReduction.Gen.psiAt, chosenChar]
        · rfl
      refine ⟨fun j => ε ((ι j : ℕ) + 1) (c.sd (D.plEq.symm v)), fun hΘ hT => ⟨fun j => ⟨h0 _ _, ?_⟩, ?_⟩⟩
      · have g2 := h2 _ (succ_mem_Icc (ι j)) (c.sd (D.plEq.symm v))
        have g3 := h3 _ (succ_mem_Icc (ι j)) (c.sd (D.plEq.symm v))
        rw [hψ] at g2 g3
        exact (hT.2 j).lix_le (hM j) (hΘ j) (isLatIn_eTh hI (succ_mem_Icc (ι j)) _) ⟨g3.1, g2, g3.2⟩
      · rw [← l_eq_plc c v]
        exact (sum_side_le hι h0 _).trans h1
    · exact ⟨0, fun _ hT => absurd hT.1 hv⟩
  choose ε hε using loc
  exact ⟨ε, leafTW1_of_places fun w hw => ⟨hε _ (hΘ w hw).1 (hT w hw).1, hε _ (hΘ w hw).2 (hT w hw).2⟩⟩

end Record

end GlobalTheory.TwistIndex
end
end
