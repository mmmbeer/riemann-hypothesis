import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfLin
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsLast
import Development.WeilBound.CoreStatements.HodgeTatePoints.GcField
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcTors
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoTorsionTower
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionTowerWeilPairing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

end PositivityTheory.HtPt.Htat.HTBaseChange

open PositivityTheory.HtPt.Htat.HTBaseChange in

theorem PositivityTheory.HtPt.Htat.ht_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M R' _ _ _ Γ' F hF hi' L' _ _ M' β hβ hspan χ w w' hw hHT
  obtain ⟨s, hs, hv⟩ := hHT
  have hs' : Γ'.HasValues (F.appTop.hom s)
      (fun t => (((Units.map (algebraMap R R' : R →* R')).comp χ t : R'ˣ) : R')) := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (χ t) := by
      apply hj
      rw [← valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← valAt_comp_top, ← hσj', valAt_spec_map, hb, ← RingHom.comp_apply, hj'i]
    simp
  obtain ⟨l', hl'⟩ := PositivityTheory.HtPt.Htat.ht_linear R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) hi'
    L' M' ((Units.map (algebraMap R R' : R →* R')).comp χ) (F.appTop.hom s) hs'
  have key : ∀ e, l' (β e) = Ideal.Quotient.mk (Ideal.span {(N : R')}) (w' (β e)) := by
    intro e
    obtain ⟨v, hv1, hv2, hv3⟩ := hv e
    have hc : (Spec.map (CommRingCat.ofHom (dualMap (qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
        Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
          (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      all_goals simp [dualMap, qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    set v'' := hF.cart.lift _ _ hc with hv''
    have h1 := hF.cart.lift_fst _ _ hc
    have h2 := hF.cart.lift_snd _ _ hc
    rw [← hv''] at h1 h2
    have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
        (M'.pt (β e)).left := by
      rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      ext a
      all_goals simp [dualMap, qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    have h4 := hl' (β e) v'' ⟨h2, h3⟩
    rw [← valAt_comp_top, h1, valAt_spec_map, hv3] at h4
    have h5 := congrArg TrivSqZeroExt.snd h4
    simp only [dualMap, qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
    rw [← h5, hw]
  have heq : l' = (Ideal.Quotient.mkₐ R' (Ideal.span {(N : R')})).toLinearMap.comp w' :=
    LinearMap.ext_on_range hspan (fun e => by simpa using key e)
  refine ⟨F.appTop.hom s, hs', fun e' => ?_⟩
  obtain ⟨v', ⟨hv'1, hv'2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N
    (F ≫ i) hi' L' M' e'
  refine ⟨v', hv'1, hv'2, ?_⟩
  rw [hl' e' v' ⟨hv'1, hv'2⟩, heq]
  simp
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Htat

theorem lie_bc_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, M.Lifts (algebraMap R R') (𝟙 G.left) e (M'.pt (j e))) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (PositivityTheory.HtPt.Htat.lie_proj S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  unfold LieModel.Lifts at h
  rw [Category.comp_id] at h
  exact h

end PositivityTheory.HtPt.Htat
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace PositivityTheory.HtPt.Htat.ChartRed

section Alg

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  {g : M →ₗ[A] N}

theorem dual_ext (hg : IsBaseChange B g) {y y' : Module.Dual B N} (h : ∀ m, y (g m) = y' (g m)) : y = y' := by
  refine LinearMap.ext fun n => ?_
  refine hg.inductionOn n (fun n => y n = y' n) (by simp) h ?_ ?_
  · intro s n hn; simp [hn]
  · intro a b ha hb; simp [ha, hb]

theorem span_range_eq_top (hg : IsBaseChange B g) : Submodule.span B (Set.range g) = ⊤ := by
  refine eq_top_iff.2 fun n _ => ?_
  refine hg.inductionOn n (fun n => n ∈ Submodule.span B (Set.range g)) (Submodule.zero_mem _)
    (fun m => Submodule.subset_span ⟨m, rfl⟩) ?_ ?_
  · intro s n hn; exact Submodule.smul_mem _ _ hn
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

def dualOf (hg : IsBaseChange B g) : Module.Dual A M →ₗ[A] Module.Dual B N where
  toFun w := hg.lift (Algebra.linearMap A B ∘ₗ w)
  map_add' w w' := dual_ext hg fun m => by simp [IsBaseChange.lift_eq]
  map_smul' a w := dual_ext hg fun m => by simp [IsBaseChange.lift_eq, Algebra.smul_def]

@[simp] theorem dualOf_apply (hg : IsBaseChange B g) (w : Module.Dual A M) (m : M) :
    dualOf hg w (g m) = algebraMap A B (w m) := by
  simp [dualOf, IsBaseChange.lift_eq]

theorem exists_dualBasis (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ m, ∑ i, f i m • e i = m :=
  _root_.UpperTheory.Reformulated.B.DYhb1.main A M

theorem isBaseChange_dual [Module.Finite A M] [Module.Projective A M] (hg : IsBaseChange B g) :
    IsBaseChange B (dualOf hg) := by
  obtain ⟨n, e, f, hef⟩ := exists_dualBasis A M
  let Φ : B ⊗[A] Module.Dual A M →ₗ[B] Module.Dual B N := LinearMap.liftBaseChange B (dualOf hg)
  let Ψ : Module.Dual B N →ₗ[B] B ⊗[A] Module.Dual A M :=
    { toFun := fun y => ∑ i, y (g (e i)) • ((1 : B) ⊗ₜ[A] f i)
      map_add' := fun y y' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun b y => by simp [Finset.smul_sum, mul_smul] }
  have hΨΦ : ∀ z, Ψ (Φ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b w =>
      have hw : ∑ i, w (e i) • f i = w := by
        refine LinearMap.ext fun m => ?_
        have := congrArg w (hef m)
        simp only [map_sum, map_smul, smul_eq_mul] at this
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [← this]
        exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _
      have h1 : ∀ i, (Φ (b ⊗ₜ w)) (g (e i)) • ((1 : B) ⊗ₜ[A] f i) = b ⊗ₜ[A] (w (e i) • f i) := by
        intro i
        simp only [Φ, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, dualOf_apply, smul_eq_mul]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, _root_.mul_comm,
          TensorProduct.smul_tmul', Algebra.smul_def]
      show ∑ i, (Φ (b ⊗ₜ w)) (g (e i)) • ((1 : B) ⊗ₜ[A] f i) = _
      rw [Finset.sum_congr rfl fun i _ => h1 i, ← TensorProduct.tmul_sum, hw]
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y
    refine dual_ext hg fun m => ?_
    show Φ (∑ i, y (g (e i)) • ((1 : B) ⊗ₜ[A] f i)) (g m) = _
    have h3 : y (g m) = ∑ i, algebraMap A B (f i m) * y (g (e i)) := by
      conv_lhs => rw [← hef m]
      simp [map_sum, Algebra.smul_def, ← IsScalarTower.algebraMap_smul B]
    rw [h3, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Φ, _root_.mul_comm]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ
    ⟨Function.LeftInverse.injective hΨΦ, Function.RightInverse.surjective hΦΨ⟩)
    (fun w => by
      show Φ ((1 : B) ⊗ₜ w) = _
      simp [Φ])

end Alg

section Rank

variable {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

theorem finrank_tensor_eq (F F' : Type) [Field F] [Field F'] [Algebra R F] [Algebra R F'] :
    Module.finrank F (F ⊗[R] P) = Module.finrank F' (F' ⊗[R] P) := by
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  have hc : ∀ a b : PrimeSpectrum R, Module.rankAtStalk (R := R) P a = Module.rankAtStalk (R := R) P b :=
    fun a b => Module.isLocallyConstant_rankAtStalk.apply_eq_of_preconnectedSpace a b
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := P) (S := F) ⊥
  have h2 := Module.rankAtStalk_baseChange (R := R) (M := P) (S := F') ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1 h2
  simp only [Pi.natCast_apply, Nat.cast_id] at h1 h2
  rw [h1, h2]; exact hc _ _

end Rank

section Lattice

variable {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

theorem exists_sum_add_pow {c : E ≃+* E} {p N : ℕ} {EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ} {u : Fin N → La}
    (hu : IsPolLattice c p EF u) (n : ℕ) (b : La) :
    ∃ (z : Fin N → 𝓞 E) (x : La), b = ∑ k, z k • u k + (p ^ n) • x := by
  induction n with
  | zero => exact ⟨0, b, by simp⟩
  | succ n ih =>
    obtain ⟨z, x, rfl⟩ := ih
    obtain ⟨a, x', rfl⟩ := hu.span x
    refine ⟨z + (p ^ n) • a, x', ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
      smul_assoc, pow_succ, mul_smul, add_assoc]

theorem finite_lev (p : ℕ) [hp : Fact p.Prime] (hfin : Module.Finite ℤ La) (n : ℕ) : Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (pow_pos hp.out.pos n).ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

end Lattice

theorem pow_val_intCast {G : Type} [CommGroup G] {m : ℕ} [NeZero m] {g : G} (hg : g ^ m = 1) (a : ℤ) :
    g ^ ((a : ZMod m).val) = g ^ a := by
  have h1 : (((a : ZMod m).val : ℕ) : ℤ) = a % (m : ℤ) := ZMod.val_intCast a
  rw [← zpow_natCast, h1]
  conv_rhs => rw [← Int.emod_add_mul_ediv a (m : ℤ), zpow_add, zpow_mul, zpow_natCast, hg, one_zpow, _root_.mul_one]

theorem injective_of_isBaseChange {R K L Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup L] [Module R L] [AddCommGroup Ω] [Module K Ω] [Module R Ω]
    [IsScalarTower R K Ω] {j : Module.Dual R L →ₗ[R] Ω} (hj : IsBaseChange K j) : Function.Injective j := by
  haveI := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K j).2 hj
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) j).1 hw
  refine LinearMap.ext fun e => ?_
  have h := LinearMap.congr_fun hc e
  have hc0 : (c : R) ≠ 0 := nonZeroDivisors.ne_zero c.2
  simpa [Submonoid.smul_def, hc0] using h

theorem finrank_chain {R O K C Ω P Q : Type} [CommRing R] [IsDomain R] [CommRing O] [Field K] [Field C]
    [Algebra R K] [Algebra R O] [Algebra O C] [Algebra R C] [IsScalarTower R O C]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω]
    [AddCommGroup Q] [Module O Q] [Module R Q] [IsScalarTower R O Q]
    {j : P →ₗ[R] Ω} (hj : IsBaseChange K j) {D : P →ₗ[R] Q} (hD : IsBaseChange O D) :
    Module.finrank K Ω = Module.finrank C (C ⊗[O] Q) := by
  rw [← hj.equiv.finrank_eq, finrank_tensor_eq (R := R) (P := P) K C]
  exact ((AlgebraTensorModule.congr (LinearEquiv.refl C C) hD.equiv).symm.trans
    (AlgebraTensorModule.cancelBaseChange R O C C P)).symm.finrank_eq.symm ▸ rfl

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] [IsDomain O]
  {y : Spec (CommRingCat.of O) ⟶ S}

theorem isDer_of_isHT {p : ℕ} {La : Type} [AddCommGroup La] (X : TorsTower p G y La) {L : Type} [AddCommGroup L]
    [Module O L] (M : LieModel G y L) (n : ℕ) (χ : LevGrp La p n →* Oˣ) (w : Module.Dual O L)
    (h : (X.Γ n).IsHT (X.i n) M (p ^ n) χ w) : X.IsDer M n (fun t => ((χ t : Oˣ) : O)) w := by
  obtain ⟨s, hs, he⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := he e
  refine ⟨v, h1, h2, ?_⟩
  rw [h3]
  simp

theorem act_comm {R : Type} [CommRing R] [Algebra R O] {x : Spec (CommRingCat.of R) ⟶ S} {L L' : Type}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module O L'] (M : LieModel G x L)
    (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) L') (β : L → L')
    (hβ : ∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R O))) ≫ (M.pt e).left)
    {f : G ⟶ G} {A : L →ₗ[R] L} {A' : L' →ₗ[O] L'} (hA : M.IsDiffOf f A) (hA' : M'.IsDiffOf f A') (e : L) :
    A' (β e) = β (A e) := by
  apply M'.inj
  apply Over.OverMorphism.ext
  rw [hA' (β e), hβ (A e), hA e, Over.comp_left, hβ e, Over.comp_left, Category.assoc]

end Group

theorem reducesTo_of_isHTChartOf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra R O] (n N : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (D : HTChart R K c p n N Ω) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (u : Fin N → La) (hu : IsPolLattice c p EF u) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) (x : Spec (CommRingCat.of R) ⟶ S) (Γ₀ : QFGroup R (LevGrp La p n)) (i : Γ₀.G.left ⟶ G.left) (hi : Γ₀.IsTorsionAlong G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (act : 𝓞 E → (G ⟶ G)) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n) (ζ₀ : Rˣ) (X : TorsTower p G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) La) (F : (X.Γ n).G.left ⟶ Γ₀.G.left) (L' : Type) [AddCommGroup L'] [Module O L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) L') (ρ' : 𝓞 E →+* Module.End O L') (hρ' : M'.IsActOf act ρ') (ζ : ℕ → Oˣ) (κ : O) (P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L')), IsHTChartOf D Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', D.e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → (X.Γ n).IsBaseChange Γ₀ (algebraMap R O) F → F ≫ i = X.i n → algebraMap R O (ζ₀ : R) = (ζ n : O) → ζ n ^ p ^ n = 1 → IsPointOf p (X.IsDer M') EF ζ ρ' u P → ∃ io : D.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L'), D.ReducesTo (algebraMap R O) P io := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c R K _ _ _ _ _ _ _ n N Ω _ _ _ _ D La _ _ EF u hu S G _ _ hG x Γ₀ i hi
    L _ _ M act ρ hρ j hj π ζ₀ X F L' _ _ M' ρ' hρ' ζ κ P hD hπ he hbc hF hζ hζn hP
  haveI := hG
  haveI : NeZero (p ^ n) := ⟨(pow_pos (Fact.out : p.Prime).pos n).ne'⟩
  haveI : Finite (LevGrp La p n) := finite_lev p hu.finite n
  letI : Module R L' := Module.compHom L' (algebraMap R O)
  haveI : IsScalarTower R O L' := ⟨fun r o l => by
    show (r • o) • l = algebraMap R O r • (o • l)
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨β₀, hβ₀, hβs, -⟩ := PositivityTheory.HtPt.Htat.lie_bc S G R O x L L' M M'
  let β : L →ₗ[R] L' := { toFun := β₀, map_add' := β₀.map_add, map_smul' := fun a e => hβs a e }
  have hβ : IsBaseChange O β := PositivityTheory.HtPt.Htat.lie_bc_iso S G R O x L L' M M' β (fun e => by
    unfold LieModel.Lifts
    rw [Category.comp_id]
    exact hβ₀ e)
  obtain ⟨hLf, hLp⟩ := PositivityTheory.HtPt.Htat.lie_fin S G R x L M
  have hDb := isBaseChange_dual hβ
  have hinj := injective_of_isBaseChange hj
  have hom : D.om = LinearMap.range j := hD.1
  let eq : Module.Dual R L ≃ₗ[R] D.om := (LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hom.symm)
  have heq : ∀ w, ((eq w : D.om) : Ω) = j w := fun _ => rfl
  let io : D.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L') :=
    { toFun := fun y => (1 : C) ⊗ₜ[O] dualOf hβ (eq.symm y)
      map_add' := fun a b => by simp [TensorProduct.tmul_add]
      map_smul' := fun r a => by
        rw [map_smul, map_smul, ← algebraMap_smul O r (dualOf hβ (eq.symm a)), TensorProduct.tmul_smul] }
  have hio : ∀ (y : D.om) (w : Module.Dual R L), (y : Ω) = j w → io y = (1 : C) ⊗ₜ[O] dualOf hβ w := by
    intro y w h
    have : y = eq w := Subtype.ext (h.trans (heq w).symm)
    subst this
    show (1 : C) ⊗ₜ[O] dualOf hβ (eq.symm (eq w)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hioe : ∀ w, io (eq w) = (1 : C) ⊗ₜ[O] dualOf hβ w := fun w => hio _ w (heq w)
  obtain ⟨htP, hρP, heP, homP, hρΩP, hhtP⟩ := hP
  have htate : ∀ z : Fin N → 𝓞 E, P.tate z = (1 : C) ⊗ₜ[ℤ] ∑ k, z k • u k := by
    intro z
    simp only [HTPoint.tate, htP, hρP, TensorProduct.tmul_sum]
  refine ⟨io, ?_, ?_, ?_, ?_, ?_⟩
  · rw [homP]
    have hs := span_range_eq_top hDb
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rw [LinearMap.range_eq_map, ← hs, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨eq w, hioe w⟩
  · letI : Algebra R C := ((algebraMap O C).comp (algebraMap R O)).toAlgebra
    haveI : IsScalarTower R O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact finrank_chain hj hDb
  · intro a y
    obtain ⟨w, rfl⟩ := eq.surjective y
    rw [hioe w, hρΩP]
    refine (hio _ (w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) ?_).trans ?_
    · show D.ρΩ a ((eq w : D.om) : Ω) = _
      rw [heq w]
      exact hD.2.1 a w
    · congr 1
      refine dual_ext hβ fun m => ?_
      have hc := act_comm M M' β₀ hβ₀ (hρ (RingOfIntegers.mapRingEquiv c a))
        (hρ' (RingOfIntegers.mapRingEquiv c a)) m
      rw [dualOf_apply]
      show _ = dualOf hβ w (ρ' (RingOfIntegers.mapRingEquiv c a) (β m))
      rw [show ρ' (RingOfIntegers.mapRingEquiv c a) (β m) = β (ρ (RingOfIntegers.mapRingEquiv c a) m) from hc,
        dualOf_apply]
      rfl
  · intro z
    obtain ⟨χ, w, hχ, hh, hHT⟩ := hD.2.2 z
    have htors : (X.Γ n).IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) (p ^ n) (F ≫ i) := by
      rw [hF]; exact X.tors n
    have hHT' := PositivityTheory.HtPt.Htat.ht_bc R (LevGrp La p n) Γ₀ S G x (p ^ n) i hi L M O (X.Γ n) F hbc htors L' M' β₀ hβ₀
      (span_range_eq_top hβ) χ w (dualOf hβ w) (fun e => dualOf_apply hβ w e) hHT
    rw [hF] at hHT'
    have hder := isDer_of_isHT X M' n _ _ hHT'
    have hz : Units.map (algebraMap R O : R →* O) ζ₀ = ζ n := Units.ext hζ
    have hf : ∀ b, ((((Units.map (algebraMap R O : R →* O)).comp χ) (lev p n b) : Oˣ) : O) =
        ((ζ n ^ EF (∑ k, z k • u k) b : Oˣ) : O) := by
      intro b
      obtain ⟨z', x', rfl⟩ := exists_sum_add_pow hu n b
      have hl : lev p n (∑ k, z' k • u k + (p ^ n) • x') = π (Multiplicative.ofAdd z') := by
        rw [hπ]
        refine congrArg Multiplicative.ofAdd ((Submodule.Quotient.eq _).2 ⟨x', ?_⟩)
        rw [LinearMap.smul_apply, LinearMap.id_apply, add_sub_cancel_left]
      rw [hl]
      congr 1
      show Units.map (algebraMap R O : R →* O) (χ (π (Multiplicative.ofAdd z'))) = _
      rw [hχ, map_pow, hz, he, pow_val_intCast hζn, map_add, map_nsmul, zpow_add, nsmul_eq_mul,
        zpow_mul, zpow_natCast, hζn, one_zpow, _root_.mul_one]
    obtain ⟨y, hy, hyeq⟩ := hhtP n (∑ k, z k • u k) _ _ hf hder
    refine ⟨-y, P.om.neg_mem hy, ?_⟩
    rw [hio _ w hh, htate, hyeq]
    simp
  · intro a b
    rw [htate, htate, heP, he]
    generalize EF (∑ k, a k • u k) (∑ k, b k • u k) = t
    have h1 : (((t : ZMod (p ^ n)).val : ℕ) : ℤ) = t % ((p ^ n : ℕ) : ℤ) := ZMod.val_intCast t
    obtain ⟨q, hq⟩ : ∃ q : ℤ, t = (((t : ZMod (p ^ n)).val : ℕ) : ℤ) + ((p ^ n : ℕ) : ℤ) * q :=
      ⟨t / ((p ^ n : ℕ) : ℤ), by rw [h1]; exact (Int.emod_add_mul_ediv _ _).symm⟩
    refine ⟨(q : O), ?_⟩
    have h2 : (t : C) = (((t : ZMod (p ^ n)).val : ℕ) : C) + (p : C) ^ n * (q : C) := by
      have := congrArg (Int.cast : ℤ → C) hq
      push_cast at this
      exact this
    rw [h2, map_add, map_mul, map_pow, map_natCast, map_natCast, map_intCast]

end PositivityTheory.HtPt.Htat.ChartRed
end
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace PositivityTheory.HtPt.Htat.TestPts

theorem isProper_snd_comp {G S Y Z : Scheme.{0}} (f : G ⟶ S) (h : Y ⟶ S) (g : Z ⟶ Y)
    [IsProper (Limits.pullback.snd f h)] : IsProper (Limits.pullback.snd f (g ≫ h)) := by
  have hc : Limits.pullback.fst f (g ≫ h) ≫ f = (Limits.pullback.snd f (g ≫ h) ≫ g) ≫ h := by
    rw [Limits.pullback.condition, Category.assoc]
  have hp : IsPullback (Limits.pullback.lift _ _ hc) (Limits.pullback.snd f (g ≫ h))
      (Limits.pullback.snd f h) g := by
    refine IsPullback.of_right (h₁₂ := Limits.pullback.fst f h) (v₁₃ := f) (h₂₂ := h) ?_
      (Limits.pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback f h)
    rw [Limits.pullback.lift_fst]
    exact IsPullback.of_hasPullback f (g ≫ h)
  exact MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance

theorem exists_unit_of_pow {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    (u : (FractionRing O)ˣ) (m : ℕ) (hm : 0 < m) (h : u ^ m = 1) :
    ∃ w : Oˣ, algebraMap O (FractionRing O) w = u := by
  have h1 : IsIntegral O (u : FractionRing O) :=
    IsIntegral.of_pow hm (by rw [← Units.val_pow_eq_pow_val, h]; exact isIntegral_one)
  have h2 : IsIntegral O ((u⁻¹ : (FractionRing O)ˣ) : FractionRing O) :=
    IsIntegral.of_pow hm (by rw [← Units.val_pow_eq_pow_val, inv_pow, h]; simpa using isIntegral_one)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_one]; simp
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

theorem finite_levGrp (La : Type) [AddCommGroup La] [Module.Finite ℤ La] (p n : ℕ) (hp : 0 < p) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) x
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change ((p ^ n : ℕ) : ℤ) • (Submodule.Quotient.mk a : La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  exact this

theorem finrank_eq_rankAtStalk {A Q : Type} [CommRing A] [IsDomain A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Projective A Q] (P : PrimeSpectrum A) :
    Module.finrank A Q = Module.rankAtStalk Q P := by
  have hbc := TensorProduct.isBaseChange A Q (FractionRing A)
  haveI := Module.finitePresentation_of_projective A Q
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing _ hbc,
    LieRank.finrank_of_isBaseChange _ hbc (IsLocalRing.closedPoint (FractionRing A))]
  exact (Module.isLocallyConstant_rankAtStalk (R := A) (M := Q)).apply_eq_of_preconnectedSpace _ _

theorem finrank_lie_eq (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom]
    (R O : Type) [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] [Algebra R O]
    (x : Sp R ⟶ S) (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module O L']
    (M : LieModel G x L) (M' : LieModel G (spMap (algebraMap R O) ≫ x) L') :
    Module.finrank O L' = Module.finrank R L := by
  obtain ⟨hf, hp⟩ := PositivityTheory.HtPt.Htat.lie_fin S G R x L M
  letI : Module R L' := Module.compHom L' (algebraMap R O)
  haveI : IsScalarTower R O L' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G x M M'
  have hbc := PositivityTheory.HtPt.Htat.lie_bc_iso S G R O x L L' M M' j hj
  rw [← LinearEquiv.finrank_eq hbc.equiv,
    finrank_eq_rankAtStalk (IsLocalRing.closedPoint (FractionRing O) |> PrimeSpectrum.comap (algebraMap O (FractionRing O))),
    Module.rankAtStalk_baseChange]
  exact (finrank_eq_rankAtStalk _).symm

theorem reduces_at_point (hPt : PointHT) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω]
    [Module R Ω] [IsScalarTower R K Ω]
    (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La)
    (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S]
    (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left)
    (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L)
    (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω)
    (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R)
    (hc : IsHTChartOf Dc Γ₀ i M ρ j π ζ₀)
    (hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k))
    (he : ∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n)))
    (hrank : 2 * Module.finrank R L = Module.finrank ℤ D.La)
    (hprop : IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)))
    (hκ : if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1)
    (C O : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsDomain O] [Algebra O C] [Algebra R O]
    (v : Valuation C NNReal) (hv : v.Integers O) (hp : v (p : C) < 1)
    (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (hinj : Function.Injective (algebraMap R O))
    [IsAlgClosed (FractionRing O)] [IsIntegrallyClosed O]
    (f : FractionRing R →+* FractionRing O)
    (hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r))
    (z : Sp (FractionRing O) ⟶ S) (hz : z = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x)
    (I : TateIso D (FractionRing O) (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))
    (hI1 : (I.ζ (p ^ n) : FractionRing O) = f (algebraMap R _ (ζ₀ : R)))
    (hI2 : ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) :
    ∃ (L' : Type) (_ : AddCommGroup L') (_ : Module O L')
      (P : HTPoint C O (IsCMField.complexConj E).toRingEquiv (algebraMap R O κ) (D.p + D.q) (C ⊗[ℤ] D.La)
        (C ⊗[O] Module.Dual O L'))
      (io : Dc.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L')), Dc.ReducesTo (algebraMap R O) P io := by
  subst hz
  have hppos : ∀ m, 0 < p ^ m := fun m => pow_pos (Fact.out : p.Prime).pos m
  haveI : CharZero O := charZero_of_injective_ringHom hinj
  obtain ⟨X, hX, hXi⟩ := GlobalTheory.T.tate_iso_torsion_tower E H D S t p O _ I
  have hroot : ∀ m, ∃ w : Oˣ, algebraMap O (FractionRing O) w = (I.ζ (p ^ m) : (FractionRing O)ˣ) := fun m =>
    exists_unit_of_pow _ (p ^ m) (hppos m) (I.ζ_prim _ (hppos m)).pow_eq_one
  choose ζ hζ using hroot
  have hkinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hUinj : Function.Injective (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O)) :=
    Units.map_injective hkinj
  have hU : ∀ m, Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ m) = I.ζ (p ^ m) :=
    fun m => Units.ext (hζ m)
  have hprim : ∀ m, IsPrimitiveRoot (ζ m) (p ^ m) := fun m =>
    IsPrimitiveRoot.of_map_of_injective (f := Units.map (algebraMap O (FractionRing O) : O →* FractionRing O))
      (by rw [hU]; exact I.ζ_prim _ (hppos m)) hUinj
  have hcompat : ∀ m, ζ (m + 1) ^ p = ζ m := fun m => by
    apply hUinj
    rw [map_pow, hU, hU, pow_succ]
    exact I.ζ_pow _ _ (hppos m) (Fact.out : p.Prime).pos
  have hsq : (BT.genPt O).hom ≫ spMap (algebraMap R O) = spMap f ≫ (BT.genPt R).hom := by
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (hf r).symm
  have hprop' : IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x)) := by
    rw [← Category.assoc, hsq, Category.assoc]
    exact isProper_snd_comp _ _ _
  have hreg : X.PairingRegular D.EF ζ := by
    refine GlobalTheory.T.torsion_tower_weil_pairing E H S t p O _ D.La X D.EF ζ hprop' ?_
    intro m a b ga gb hga hgb
    have e1 : ga = I.ev (p ^ m) a := Over.OverMorphism.ext (hga.trans (hX m a))
    have e2 : gb = I.ev (p ^ m) b := Over.OverMorphism.ext (hgb.trans (hX m b))
    rw [e1, e2, map_zpow, hU]
    exact I.isom (p ^ m) (hppos m) a b
  haveI : Module.Finite ℤ D.La := hu.finite
  haveI := finite_levGrp D.La p n (Fact.out : p.Prime).pos
  have hSep : IsSeparated t.G.hom := t.semi.separated
  obtain ⟨F, hF1, hF2⟩ := PositivityTheory.HtPt.Htat.torsion_bc R (LevGrp D.La p n) Γ₀ S t.G x (p ^ n) i hi hSep O (algebraMap R O)
    (X.Γ n) (X.i n) (X.tors n) (FractionRing R) (algebraMap R _) (RingHom.id _) f
    (fun s => (Γ₀.pt s).left ≫ i) Function.injective_id (RingHom.id_comp _) (RingHom.ext hf)
    (fun s => by
      rw [Category.assoc, hi.isOver, ← Category.assoc, Over.w (Γ₀.pt s)]; rfl)
    (fun s => by simp)
    (fun s => by
      obtain ⟨q, rfl⟩ := Multiplicative.ofAdd.surjective s
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range ((p ^ n) • (LinearMap.id : D.La →ₗ[ℤ] D.La))) q
      change _ = ((X.Γ n).pt (lev p n a)).left ≫ X.i n
      rw [hX n a, hI2 a]; rfl)
  obtain ⟨L', iA, iM, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S t.G O (spMap (algebraMap R O) ≫ x)
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act S t.G O (spMap (algebraMap R O) ≫ x) L' M' (𝓞 E)
    t.act.act t.act.hom t.act.one t.act.mul t.act.add
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  have hrank' : 2 * Module.finrank O L' = Module.finrank ℤ D.La := by
    rw [finrank_lie_eq S t.G R O x L L' M M']; exact hrank
  obtain ⟨hκ1, -⟩ := GlobalTheory.T.hodge_tate_constant_divides_p_sq C v O hv p R (algebraMap R O) κ hp hκ
  obtain ⟨P, hP⟩ := hPt p C v O hv hp hO E (IsCMField.complexConj E).toRingEquiv
    (fun a => IsCMField.complexConj_apply_apply E a) S t.G t.semi _ D.La D.EF (D.p + D.q) u hu X L' M' t.act.act ρ'
    t.act.hom hρ' hXi hrank' ζ hprim hcompat hreg (algebraMap R O κ) hκ1
  have hζ₀ : algebraMap R O (ζ₀ : R) = (ζ n : O) := by
    apply hkinj
    rw [← hf, ← hI1, hζ n]
  obtain ⟨io, hio⟩ := PositivityTheory.HtPt.Htat.ChartRed.reducesTo_of_isHTChartOf p C v O hv hp hO E (IsCMField.complexConj E).toRingEquiv R K n (D.p + D.q) Ω Dc
    D.La D.EF u hu S t.G hsm x Γ₀ i hi L M t.act.act ρ hρ j hj π ζ₀ X F L' M' ρ' hρ' ζ (algebraMap R O κ) P hc hπ he
    hF2 hF1 hζ₀ (hprim n).pow_eq_one hP
  exact ⟨L', iA, iM, P, io, hio⟩

end PositivityTheory.HtPt.Htat.TestPts

namespace PositivityTheory.HtPt.Htat

open PositivityTheory.HtPt.Htat.TestPts in

theorem has_test_points : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → Dc.HasTestPoints κ := by
  intro hPt E _ _ _ H D p _ R K _ _ _ _ _ _ _ _ n Ω _ _ _ _ Dc u hu S _ t x Γ₀ i hi L _ _ M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hTate hκ 𝔮 hq hh hpq
  obtain ⟨C, O, iF, iAC, iCZ, iR, iD, iAl, v, φ, hv, hp, hO, hinj, hcent⟩ := PositivityTheory.HtPt.Gc.test_field R p 𝔮 hq hh hpq
  letI : Algebra R O := φ.toAlgebra
  obtain ⟨-, -, hIC, -, hAC, -⟩ := PositivityTheory.HtPt.Twhopf.padic_alg p C v O hv hp hO
  haveI := hAC
  haveI := hIC
  have hgk : Function.Injective ((algebraMap O (FractionRing O)).comp φ) :=
    (IsFractionRing.injective O _).comp hinj
  let f : FractionRing R →+* FractionRing O := IsFractionRing.lift hgk
  have hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r) :=
    fun r => IsFractionRing.lift_algebraMap hgk r
  obtain ⟨I, hI1, hI2⟩ := hTate (FractionRing O) f
  have hz : spMap f ≫ (BT.genPt R).hom ≫ x = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hf
  obtain ⟨L', iA', iM', P, io, hio⟩ := reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀ i hi L M ρ hρ j hj π ζ₀ κ hc hπ he
    hrank hprop hκ C O v hv hp hO hinj f hf _ hz I hI1 hI2
  exact ⟨C, O, iF, iAC, iCZ, iR, iAl, v, φ, C ⊗[ℤ] D.La, C ⊗[O] Module.Dual O L', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P, io, hv, hinj, hcent, hio⟩

end PositivityTheory.HtPt.Htat
end
end
