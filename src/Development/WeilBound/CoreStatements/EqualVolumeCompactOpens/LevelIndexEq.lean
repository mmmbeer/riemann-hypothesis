import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SaOpen
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Assembly
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.DiagMulVecTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cmp
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem exists_dualBasis {Λ : Submodule (𝓞 E) (Fin N → E)} (h : IsLat Λ) :
    ∃ (k : ℕ) (y : Fin k → Fin N → E) (l : Fin k → (Fin N → E) →ₗ[F] F), (∀ j, y j ∈ Λ) ∧
      (∀ j, ∀ x ∈ Λ, ∃ o : 𝓞 F, l j x = o) ∧ ∀ x, x = ∑ j, l j x • y j := by
  classical
  obtain ⟨hfg, hspan⟩ := h
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite (𝓞 F) Λ := Module.Finite.trans (𝓞 E) Λ
  haveI : Module.FinitePresentation (𝓞 F) Λ := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 F) Λ := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  haveI : Module.Projective (𝓞 F) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, g, -, -, hfg'⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 F) Λ
  have hne : ∀ s : nonZeroDivisors (𝓞 F), algebraMap (𝓞 F) F s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hunit : ∀ {M : Type} [AddCommGroup M] [Module F M] [Module (𝓞 F) M] [IsScalarTower (𝓞 F) F M]
      (s : nonZeroDivisors (𝓞 F)), IsUnit (algebraMap (𝓞 F) (Module.End (𝓞 F) M) s) := by
    intro M _ _ _ _ s
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      have hab' : (algebraMap (𝓞 F) F s) • a = (algebraMap (𝓞 F) F s) • b := by
        simpa [IsScalarTower.algebraMap_smul] using hab
      exact smul_right_injective M (hne s) hab'
    · intro b
      refine ⟨(algebraMap (𝓞 F) F s)⁻¹ • b, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← IsScalarTower.algebraMap_smul F (s : 𝓞 F), smul_smul, mul_inv_cancel₀ (hne s), one_smul]
  let ι : Λ →ₗ[𝓞 F] (Fin N → E) := Λ.subtype.restrictScalars (𝓞 F)
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 F)) ι := by
    refine IsLocalizedModule.mk (fun s => hunit s) (fun v => ?_)
      (fun {x₁ x₂} hx => ⟨1, by simpa using Subtype.ext hx⟩)
    obtain ⟨m, hm0, hm⟩ := exists_smul_mem ⟨hfg, hspan⟩ v
    refine ⟨(⟨_, hm⟩, ⟨(m : 𝓞 F), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm0)⟩), ?_⟩
    change (m : 𝓞 F) • v = _
    simp [ι, Nat.cast_smul_eq_nsmul]
  let gj : Fin n → (Λ →ₗ[𝓞 F] F) := fun j =>
    (Algebra.linearMap (𝓞 F) F) ∘ₗ (LinearMap.proj j) ∘ₗ g
  let L : Fin n → ((Fin N → E) →ₗ[F] F) := fun j =>
    (IsLocalizedModule.lift (nonZeroDivisors (𝓞 F)) ι (gj j) (fun s => hunit s)).extendScalarsOfIsLocalization
      (nonZeroDivisors (𝓞 F)) F
  have hL : ∀ j (x : Λ), L j (x : Fin N → E) = algebraMap (𝓞 F) F (g x j) := by
    intro j x
    exact LinearMap.congr_fun (IsLocalizedModule.lift_comp (nonZeroDivisors (𝓞 F)) ι (gj j) (fun s => hunit s)) x
  let yy : Fin n → Fin N → E := fun j => (f (Pi.single j 1) : Fin N → E)
  have hΛsum : ∀ x : Λ, (x : Fin N → E) = ∑ j, L j x • yy j := by
    intro x
    have hx : x = f (g x) := (LinearMap.congr_fun hfg' x).symm
    have hgx : g x = ∑ j, g x j • (Pi.single j 1 : Fin n → 𝓞 F) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx, hgx]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hL, IsScalarTower.algebraMap_smul, map_smul]
    rfl
  have hall : ∀ v, v = ∑ j, L j v • yy j := by
    intro v
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 F)) ι v
    change (s : 𝓞 F) • v = (x : Fin N → E) at hs
    have h1 : (s : 𝓞 F) • (∑ j, L j v • yy j) = (s : 𝓞 F) • v := by
      rw [Finset.smul_sum]
      have hj : ∀ j, (s : 𝓞 F) • (L j v • yy j) = L j ((s : 𝓞 F) • v) • yy j := by
        intro j
        rw [LinearMap.map_smul_of_tower, smul_assoc]
      simp_rw [hj]
      rw [hs]
      exact (hΛsum x).symm
    rw [← IsScalarTower.algebraMap_smul F (s : 𝓞 F), ← IsScalarTower.algebraMap_smul F (s : 𝓞 F)] at h1
    exact (smul_right_injective _ (hne s) h1).symm
  exact ⟨n, yy, L, fun j => (f (Pi.single j 1)).2, fun j x hx => ⟨g ⟨x, hx⟩ j, hL j ⟨x, hx⟩⟩, hall⟩

section coord

variable (l : (Fin N → E) →ₗ[F] F) (R : Type) [CommRing R] [Algebra F R]

def coordR (y : Fin N → R ⊗[F] E) : R :=
  ∑ i, TensorProduct.rid F R (LinearMap.lTensor R (l ∘ₗ LinearMap.single F (fun _ => E) i) (y i))

variable {R}

theorem coordR_add (x y : Fin N → R ⊗[F] E) : coordR l R (x + y) = coordR l R x + coordR l R y := by
  simp [coordR, Finset.sum_add_distrib]

theorem coordR_zero : coordR l R 0 = 0 := by simp [coordR]

theorem coordR_neg (x : Fin N → R ⊗[F] E) : coordR l R (-x) = -coordR l R x := by
  simp [coordR]

theorem coordR_tmul (a : R) (x : Fin N → E) : coordR l R (fun i => a ⊗ₜ[F] x i) = l x • a := by
  simp only [coordR, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, ← Finset.sum_smul, LinearMap.comp_apply,
    ← map_sum]
  congr 2
  exact Finset.univ_sum_single x

theorem pi_induction {P : (Fin N → R ⊗[F] E) → Prop} (h0 : P 0) (h1 : ∀ (a : R) (x : Fin N → E), P fun i => a ⊗ₜ[F] x i)
    (h2 : ∀ x y, P x → P y → P (x + y)) (y : Fin N → R ⊗[F] E) : P y := by
  have hs : ∀ (i : Fin N) (t : R ⊗[F] E), P (Pi.single i t) := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a e =>
      convert h1 a (Pi.single i e) using 1
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    | add s t hs ht => simpa [Pi.single_add] using h2 _ _ hs ht
  rw [← Finset.univ_sum_single y]
  exact Finset.sum_induction _ P h2 h0 (fun i _ => hs i (y i))

theorem eq_sum_coordR {k : ℕ} {y : Fin k → Fin N → E} {l : Fin k → (Fin N → E) →ₗ[F] F}
    (h : ∀ x, x = ∑ j, l j x • y j) (z : Fin N → R ⊗[F] E) : z = ∑ j, fun i => coordR (l j) R z ⊗ₜ[F] y j i := by
  induction z using pi_induction with
  | h0 =>
    funext i
    simp [coordR_zero, Finset.sum_apply]
  | h1 a x =>
    funext i
    simp only [coordR_tmul, Finset.sum_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    congr 1
    have hx := congrFun (h x) i
    simpa [Finset.sum_apply] using hx
  | h2 u v hu hv =>
    funext i
    have hu' := congrFun hu i
    have hv' := congrFun hv i
    simp only [Pi.add_apply, Finset.sum_apply, coordR_add, TensorProduct.add_tmul,
      Finset.sum_add_distrib] at hu' hv' ⊢
    rw [← hu', ← hv']

theorem map_coordR {S : Type} [CommRing S] [Algebra F S] (f : R →ₐ[F] S) (z : Fin N → R ⊗[F] E) :
    f (coordR l R z) = coordR l S fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (z i) := by
  induction z using pi_induction with
  | h0 =>
    have hz : (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) ((0 : Fin N → R ⊗[F] E) i)) = 0 := by
      funext i
      simp
    rw [hz, coordR_zero, coordR_zero, map_zero]
  | h1 a x =>
    have hz : (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (a ⊗ₜ[F] x i)) = fun i => f a ⊗ₜ[F] x i := by
      funext i
      simp [Algebra.TensorProduct.map_tmul]
    rw [hz, coordR_tmul, coordR_tmul, map_smul]
  | h2 u v hu hv =>
    have hz : (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) ((u + v) i)) =
        (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (u i)) +
          (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (v i)) := by
      funext i
      simp
    rw [hz, coordR_add, coordR_add, map_add, hu, hv]

end coord

theorem coordR_hat {Λ : Submodule (𝓞 E) (Fin N → E)} {l : (Fin N → E) →ₗ[F] F} (hl : ∀ x ∈ Λ, ∃ o : 𝓞 F, l x = o)
    {z : Fin N → Adf F E} (hz : z ∈ hatLat F Λ.toAddSubgroup) :
    coordR l _ z ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [coordR_tmul]
    obtain ⟨o, ho⟩ := hl x hx
    rw [ho, Algebra.smul_def]
    exact Subring.mul_mem _ (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F o)
      (GroundTheory.Global.mem_integralFiniteAdeles.2 ha)
  | zero =>
    rw [coordR_zero]
    exact Subring.zero_mem _
  | add u v _ _ hu hv =>
    rw [coordR_add]
    exact Subring.add_mem _ hu hv
  | neg u _ hu =>
    rw [coordR_neg]
    exact Subring.neg_mem _ hu

theorem hatRat : HatRat := by
  intro F E _ _ _ _ _ N Λ hΛ x
  constructor
  · intro hx
    obtain ⟨k, y, l, hy, hl, hsum⟩ := exists_dualBasis (F := F) hΛ
    have key : ∀ b : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F →
        b ∈ (algebraMap (𝓞 F) F).range := by
      intro b hb
      apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      intro v
      have hv := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1
        (GroundTheory.Global.mem_integralFiniteAdeles.1 hb v)
      rwa [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    have hc : ∀ j, ∃ o : 𝓞 F, l j x = algebraMap (𝓞 F) F o := by
      intro j
      have h1 := coordR_hat (hl j) hx
      have h2 : (fun i => inclAd F E (x i)) = fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i := rfl
      rw [h2, coordR_tmul, Algebra.smul_def, mul_one] at h1
      obtain ⟨o, ho⟩ := key _ h1
      exact ⟨o, ho.symm⟩
    rw [hsum x]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    obtain ⟨o, ho⟩ := hc j
    rw [ho, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_of_tower_mem Λ o (hy j)
  · intro hx
    exact incl_mem_hat hx

theorem hatCompactOpen : HatCompactOpen := by
  intro F E _ _ _ _ _ N Λ hΛ
  obtain ⟨k, y, l, hy, hl, hsum⟩ := exists_dualBasis (F := F) hΛ
  haveI : ContinuousAdd (Adf F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (Adf F E)
  have hsmul : ∀ j (r : FiniteAdeleRing (𝓞 F) F) (z : Fin N → Adf F E),
      coordR (l j) (FiniteAdeleRing (𝓞 F) F) (r • z) = r * coordR (l j) (FiniteAdeleRing (𝓞 F) F) z := by
    intro j r z
    induction z using pi_induction with
    | h0 => simp [coordR_zero]
    | h1 a x =>
      have hz : r • (fun i => a ⊗ₜ[F] x i) = fun i => (r * a) ⊗ₜ[F] x i := by
        funext i
        simp [TensorProduct.smul_tmul']
      rw [hz, coordR_tmul, coordR_tmul, mul_smul_comm]
    | h2 u v hu hv => rw [smul_add, coordR_add, coordR_add, hu, hv, mul_add]
  let Φ : (Fin N → Adf F E) →ₗ[FiniteAdeleRing (𝓞 F) F] (Fin k → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun z j => coordR (l j) (FiniteAdeleRing (𝓞 F) F) z
      map_add' := fun u v => by
        funext j
        exact coordR_add _ u v
      map_smul' := fun r z => by
        funext j
        exact hsmul j r z }
  have hΦ : Continuous Φ := IsModuleTopology.continuous_of_linearMap Φ
  let Ψ : (Fin k → FiniteAdeleRing (𝓞 F) F) → (Fin N → Adf F E) := fun a => ∑ j, fun i => a j ⊗ₜ[F] y j i
  have hΨ : Continuous Ψ := by
    apply continuous_finset_sum
    intro j _
    apply continuous_pi
    intro i
    have he : (fun a : Fin k → FiniteAdeleRing (𝓞 F) F => a j ⊗ₜ[F] y j i) =
        fun a => a j • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y j i : Adf F E) := by
      funext a
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he]
    exact Continuous.smul (continuous_apply (A := fun _ : Fin k => FiniteAdeleRing (𝓞 F) F) j)
      (continuous_const (y := ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y j i : Adf F E)))
  have hΨΦ : ∀ z, Ψ (Φ z) = z := fun z => (eq_sum_coordR hsum z).symm
  have hmemΨ : ∀ a : Fin k → FiniteAdeleRing (𝓞 F) F,
      (∀ j, a j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F) → Ψ a ∈ hatLat F Λ.toAddSubgroup := by
    intro a ha
    refine AddSubgroup.sum_mem _ (fun j _ => AddSubgroup.subset_closure ⟨a j, ?_, y j, hy j, rfl⟩)
    exact GroundTheory.Global.mem_integralFiniteAdeles.1 (ha j)
  have hset : (hatLat F Λ.toAddSubgroup : Set (Fin N → Adf F E)) =
      Φ ⁻¹' (Set.univ.pi fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)) := by
    ext z
    constructor
    · intro hz j _
      exact coordR_hat (hl j) hz
    · intro hz
      rw [← hΨΦ z]
      exact hmemΨ _ (fun j => hz j (Set.mem_univ j))
  have hset2 : (hatLat F Λ.toAddSubgroup : Set (Fin N → Adf F E)) =
      Ψ '' (Set.univ.pi fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)) := by
    ext z
    constructor
    · intro hz
      rw [hset] at hz
      exact ⟨Φ z, hz, hΨΦ z⟩
    · rintro ⟨a, ha, rfl⟩
      exact hmemΨ a (fun j => ha j (Set.mem_univ j))
  constructor
  · rw [hset2]
    exact (isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F).image hΨ
  · rw [hset]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles).preimage hΦ

end PositivityTheory.EqVol
end
end

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def BFr (X : Data E r) : Type := Frame X.Ψ r

instance (X : Data E r) : MeasurableSpace (BFr X) where
  MeasurableSet' S := MeasurableSet (α := Frame X.Ψ r) S ∧ ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl S h := ⟨h.1.compl, fun x b hb => not_congr (h.2 x b hb)⟩
  measurableSet_iUnion f h := ⟨MeasurableSet.iUnion fun i => (h i).1, fun x b hb =>
    Set.mem_iUnion.trans ((exists_congr fun i => (h i).2 x b hb).trans Set.mem_iUnion.symm)⟩

instance (X : Data E r) : MulAction (uGrp (ccH E) X.Gm) (BFr X) where
  smul γ x := lact γ.1 x
  one_smul := lact_one'
  mul_smul a b x := lact_mul a.1 b.1 x

instance (X : Data E r) : MeasurableConstSMul (uGrp (ccH E) X.Gm) (BFr X) where
  measurable_const_smul γ := fun S hS => ⟨(KU.cont_lact X γ.1).measurable hS.1, fun x b hb => by
    show lact γ.1 (rmul x b) ∈ S ↔ lact γ.1 x ∈ S
    rw [lact_rmul]
    exact hS.2 _ b hb⟩

end PositivityTheory.EqVol
end
end

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

open IsDedekindDomain
open scoped TensorProduct

theorem mem_hat_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hΛ : IsLat Λ) (y : Fin r → Adf (maximalRealSubfield E) E) :
    y ∈ hatLat (maximalRealSubfield E) Λ.toAddSubgroup ↔
      ∀ v, (fun i => GroundTheory.Heights₂.Heights.StrongApprox.compAt E v (y i)) ∈ GlobalTheory.SelfDualGenus.locLattice v Λ := by
  constructor
  · intro hy v
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hy
      have := (GlobalTheory.SelfDualGenus.locLattice v Λ).smul_mem ⟨b v, hb v⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert this using 1
      funext i
      show b v ⊗ₜ x i = b v • ((1 : v.adicCompletion (maximalRealSubfield E)) ⊗ₜ[maximalRealSubfield E] x i)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero => simp only [Pi.zero_apply, map_zero]; exact (GlobalTheory.SelfDualGenus.locLattice v Λ).zero_mem
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact (GlobalTheory.SelfDualGenus.locLattice v Λ).add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact (GlobalTheory.SelfDualGenus.locLattice v Λ).neg_mem hx
  · intro h
    obtain ⟨k, z, l, hz, hl, e⟩ := exists_dualBasis (F := maximalRealSubfield E) hΛ
    rw [eq_sum_coordR e y]
    refine AddSubgroup.sum_mem _ fun j _ => tmul_mem_hat (fun v => ?_) (hz j)
    have h1 := map_coordR (l j) (GroundTheory.Heights₂.Heights.StrongApprox.evalAt (maximalRealSubfield E) v) y
    show GroundTheory.Heights₂.Heights.StrongApprox.evalAt (maximalRealSubfield E) v _ ∈ _
    rw [h1]
    have key : ∀ w ∈ GlobalTheory.SelfDualGenus.locLattice v Λ,
        coordR (l j) (v.adicCompletion (maximalRealSubfield E)) w ∈ v.adicCompletionIntegers _ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, rfl⟩ := hw
        obtain ⟨o, ho⟩ := hl j x hx
        have : coordR (l j) (v.adicCompletion (maximalRealSubfield E)) (fun i => GlobalTheory.SelfDualGenus.locEmb v (x i)) =
            l j x • 1 := coordR_tmul _ 1 x
        rw [this, ho, ← Algebra.algebraMap_eq_smul_one]
        exact HeightOneSpectrum.coe_algebraMap_mem _ _ v o
      | zero => rw [coordR_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [coordR_add]; exact add_mem hx hy
      | smul a x _ hx =>
        have : ∀ (a : v.adicCompletion (maximalRealSubfield E)) x,
            coordR (l j) (v.adicCompletion (maximalRealSubfield E)) (a • x) = a * coordR (l j) _ x := by
          intro a x
          induction x using pi_induction with
          | h0 => simp [coordR_zero]
          | h1 b x =>
            have : (a • fun i => b ⊗ₜ[maximalRealSubfield E] x i) = fun i => (a * b) ⊗ₜ[maximalRealSubfield E] x i := rfl
            rw [this, coordR_tmul, coordR_tmul, mul_smul_comm]
          | h2 x y hx hy => rw [smul_add, coordR_add, coordR_add, hx, hy, mul_add]
        have e2 := this a x
        exact (show coordR (l j) _ (a • x) = _ from e2) ▸ mul_mem a.2 hx
    exact key _ (h v)

open GroundTheory.Heights₂.Heights.StrongApprox in
theorem localToAdelic : LocalToAdelic := by
  intro E _ _ _ r G L L' hL hL' ⟨γ, hγ, hfin⟩
  classical
  obtain ⟨hsep, hv⟩ := PlaceMaps.full (maximalRealSubfield E) E (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E)
  have hsepM : ∀ A B : Matrix (Fin r) (Fin r) (Adf (maximalRealSubfield E) E),
      (∀ v, A.map (compAt E v) = B.map (compAt E v)) → A = B := fun A B h =>
    Matrix.ext fun i j => hsep _ _ fun v => congrFun (congrFun (h v) i) j
  have glue : ∀ M : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      Matrix (Fin r) (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v), (∀ v, γ v = 1 → M v = 1) →
      ∃ A : Matrix (Fin r) (Fin r) (Adf (maximalRealSubfield E) E), ∀ v, A.map (compAt E v) = M v := by
    intro M hM
    refine ⟨1 + ∑ w ∈ hfin.toFinset, (M w - 1).map (singleV E w), fun v => Matrix.ext fun i j => ?_⟩
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, map_add, map_sum]
    rw [Finset.sum_eq_single v (fun w _ hw => (hv w).2.1 v hw.symm _) (fun h => by
      rw [hM v (by simpa using h)]; simp), (hv v).1, Matrix.one_apply, apply_ite (compAt E v), map_one, map_zero,
      Matrix.sub_apply, Matrix.one_apply]
    ring
  obtain ⟨A, hA⟩ := glue (fun v => γ v) fun v h => by rw [h, Units.val_one]
  obtain ⟨B, hB⟩ := glue (fun v => ((γ v)⁻¹ : GL (Fin r) _)) fun v h => by rw [h, inv_one, Units.val_one]
  have h1 : ∀ v, (1 : Matrix (Fin r) (Fin r) (Adf (maximalRealSubfield E) E)).map (compAt E v) = 1 := fun v =>
    Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨A, B, hsepM _ _ fun v => by rw [Matrix.map_mul, hA, hB, Units.mul_inv, h1],
    hsepM _ _ fun v => by rw [Matrix.map_mul, hA, hB, Units.inv_mul, h1]⟩, hsepM _ _ fun v => ?_, fun x => ?_⟩
  · have e1 : (G.map (inclAd (maximalRealSubfield E) E)).map (compAt E v) = G.map (GlobalTheory.SelfDualGenus.locEmb v) :=
      Matrix.ext fun i j => (hv v).2.2.2.2.2.2.2.1 _
    have e2 : (A.map (sigAd (IsCMField.complexConj E))).map (compAt E v) =
        (A.map (compAt E v)).map (GlobalTheory.SelfDualGenus.locConj v) :=
      Matrix.ext fun i j => (hv v).2.2.2.2.2.2.1 _
    show (Aᵀ * _ * A.map _).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.transpose_map, hA]
    exact (hγ v).1.symm
  · rw [mem_hat_iff hL, mem_hat_iff hL']
    refine forall_congr' fun v => ((hγ v).2 _).trans ?_
    rw [← hA]
    have : (A.map (compAt E v)) *ᵥ (fun i => compAt E v (x i)) = fun i => compAt E v ((A *ᵥ x) i) :=
      funext fun i => (RingHom.map_mulVec (compAt E v) A x i).symm
    rw [this]

end PositivityTheory.EqVol
end
end

section
namespace PositivityTheory.EqVol

theorem indexEq : IndexEq := indexEq_of (coSA saOpen) divisible

theorem levelIndexEq : LevelIndexEq :=
  levelIndexEq_of indexEq (levelCO hatCompactOpen) levelConj (levelRat hatRat)

end PositivityTheory.EqVol
end
