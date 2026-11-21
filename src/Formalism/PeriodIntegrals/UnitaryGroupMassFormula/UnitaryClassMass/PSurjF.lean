import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.CardStepOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatLocGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSSkeleton

section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def CofinStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V),
    Submodule.IsLattice E L → Submodule.IsLattice E N →
    ∃ D : ℤ, D ≠ 0 ∧ (∀ v ∈ L, (D : 𝓞 E) • v ∈ N) ∧ (∀ v ∈ N, (D : 𝓞 E) • v ∈ L)

def LocGmapStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (u : V ≃ₗ[E] V) (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V),
    loc (K := E) p (gmap u L) = gmap u (loc (K := E) p L)

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Basic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem mem_loc_iff (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ loc (K := E) p L ↔ ∃ s ∈ hcompl (K := E) p, s • x ∈ L := Iff.rfl

theorem mem_gmap_iff (u : V ≃ₗ[E] V) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ gmap u L ↔ ∃ y ∈ L, u y = x := Iff.rfl

theorem equiv_smul_O (u : V ≃ₗ[E] V) (s : 𝓞 E) (v : V) : u (s • v) = s • u v := by
  rw [← algebraMap_smul E s v, LinearEquiv.map_smul, algebraMap_smul]

theorem hcompl_le_primeCompl (p : Ideal (𝓞 E)) [p.IsPrime] : hcompl (K := E) p ≤ p.primeCompl := by
  refine Submonoid.closure_le.2 fun s hs => ?_
  exact Ideal.mem_primeCompl_iff.2 hs.1

end Basic

theorem linOf_one_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : linOf b (1 : GL (Fin M) E) v = v := by
  simp [linOf]

theorem locGmapStep : LocGmapStep := by
  intro E _ _ _ V _ _ _ _ u p L
  ext x
  rw [mem_loc_iff, mem_gmap_iff]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [mem_gmap_iff] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨u.symm x, ?_, u.apply_symm_apply x⟩
    rw [mem_loc_iff]
    refine ⟨s, hs, ?_⟩
    have h3 : s • u.symm x = y := by
      apply u.injective
      rw [equiv_smul_O, u.apply_symm_apply, hyx]
    rw [h3]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    rw [mem_loc_iff] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    exact ⟨s • y, hsy, equiv_smul_O u s y⟩

theorem cofin1 {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V)
    (hL : L.FG) (hN : Submodule.span E (N : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ v ∈ L, (y : 𝓞 E) • v ∈ N := by
  classical
  let b := Module.finBasis E V
  obtain ⟨y1, hy1, h1⟩ := crd_upper b L hL
  obtain ⟨y2, hy2, h2⟩ := crd_lower b N hN
  refine ⟨y1 * y2, mul_ne_zero hy1 hy2, fun v hv => ?_⟩
  have hx : b.equivFun v ∈ crdOf b L := by
    show ∑ i, b.equivFun v i • b i ∈ L
    rw [b.sum_equivFun]
    exact hv
  have e : ((y1 * y2 : ℤ) : 𝓞 E) • v = ∑ i, (y1 • b.equivFun v i) • (y2 • b i) := by
    conv_lhs => rw [← b.sum_equivFun v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← algebraMap_smul E ((y1 * y2 : ℤ) : 𝓞 E), map_intCast, zsmul_eq_mul,
      ← Int.cast_smul_eq_zsmul E y2 (b i), smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => int_smul_mem N (h1 _ hx i) (h2 i))

theorem cofinStep : CofinStep := by
  intro E _ _ V _ _ _ _ _ L N hL hN
  obtain ⟨y1, hy1, h1⟩ := cofin1 L N hL.fg hN.span_eq_top
  obtain ⟨y2, hy2, h2⟩ := cofin1 N L hN.fg hL.span_eq_top
  refine ⟨y1 * y2, mul_ne_zero hy1 hy2, fun v hv => ?_, fun v hv => ?_⟩
  · have h3 := N.smul_mem (y2 : 𝓞 E) (h1 v hv)
    rw [← mul_smul] at h3
    rwa [Int.cast_mul, mul_comm]
  · have h3 := L.smul_mem (y1 : 𝓞 E) (h2 v hv)
    rw [← mul_smul] at h3
    rwa [Int.cast_mul]

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Fam

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n]
  [DecidableEq n]

theorem fam_mul (e : ι → R) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (A B : ι → Matrix n n R) :
    (∑ i, e i • A i) * (∑ j, e j • B j) = ∑ i, e i • (A i * B i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i, ite_smul, zero_smul]
  simp

theorem fam_one (e : ι → R) (hs : ∑ i, e i = 1) (X : Matrix n n R) : ∑ i, e i • X = X := by
  rw [← Finset.sum_smul, hs, one_smul]

theorem cT_fam (s : R →+* R) (e : ι → R) (A : ι → Matrix n n R) :
    cT s (∑ i, e i • A i) = ∑ i, s (e i) • cT s (A i) := by
  ext a c
  simp [cT, Matrix.sum_apply, map_sum, Matrix.smul_apply, map_mul]

end Fam

section Patch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (F E) in

abbrev finE : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

def incM (U : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  (U : Matrix (Fin M) (Fin M) E).map (inclR (AF F))

theorem incM_mul_inv (U : GL (Fin M) E) : incM (F := F) U * incM (F := F) U⁻¹ = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_inv_mul (U : GL (Fin M) E) : incM (F := F) U⁻¹ * incM (F := F) U = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_unitary (U : GL (Fin M) E) (hU : U ∈ UJ (σ : E →+* E) J) :
    cT (sigR (AF F) σ) (incM (F := F) U) * JR (AF F) J * incM (F := F) U = JR (AF F) J := by
  have := PI.UnitaryGroupMassFormula.UJClassFin.bc_mem (F := F) σ J U hU
  exact this

def patchGL (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (γ : ι → GL (Fin M) E) : GL (Fin M) (AF F ⊗[F] E) where
  val := ∑ i, e i • incM (γ i)
  inv := ∑ i, e i • incM (γ i)⁻¹
  val_inv := by
    rw [fam_mul e he]
    simp_rw [incM_mul_inv]
    exact fam_one e hs 1
  inv_val := by
    rw [fam_mul e he]
    simp_rw [incM_inv_mul]
    exact fam_one e hs 1

theorem patchGL_mem (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : patchGL e he hs γ ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) (∑ i, e i • incM (γ i)) * JR (AF F) J * (∑ i, e i • incM (γ i)) = JR (AF F) J
  rw [cT_fam]
  simp_rw [hσe]
  conv_lhs => rw [← fam_one e hs (JR (AF F) J)]
  rw [fam_mul e he, fam_mul e he]
  simp_rw [incM_unitary σ J _ (hγ _)]
  exact fam_one e hs _

def patchHA (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (⟨patchGL e he hs γ, patchGL_mem σ J e he hs hσe γ hγ⟩ : HR (AF F) σ J)

theorem finE_inclR (x : E) : finE F E (inclR (AF F) x) = inclR (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem finMat_patch_inv (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) :
    finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      ∑ i, finE F E (e i) • ((γ i)⁻¹ : GL (Fin M) E).val.map (inclR (Af F)) := by
  have h0 : finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      (∑ i, e i • incM (F := F) (γ i)⁻¹).map (finE F E) := rfl
  rw [h0]
  ext a c
  simp [Matrix.map_apply, Matrix.sum_apply, incM, map_sum, map_mul, finE_inclR]

theorem patch_mulVec (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) (x : Fin M → E) :
    (finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x) =
      ∑ i, finE F E (e i) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (((γ i)⁻¹ : GL (Fin M) E).val.mulVec x) := by
  rw [finMat_patch_inv, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mulVec, PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc]

end Patch

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem Oh_smul_latHat (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    {z : Af F ⊗[F] E} (hz : z ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : z • y ∈ latHat F E L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * c, PI.UnitaryGroupMassFormula.UJClassFin.intAf_mul ha hc, t • x, hL t ht x hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y w _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add z w _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg z _ h1 => rw [neg_smul]; exact neg_mem h1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem latHat_split (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    (f : ι → Af F ⊗[F] E) (hf : ∀ i j, f i * f j = if i = j then f i else 0)
    (hO : ∀ i, f i ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) (y : ι → Fin M → Af F ⊗[F] E) :
    ∑ i, f i • y i ∈ latHat F E L ↔ ∀ i, f i • y i ∈ latHat F E L := by
  constructor
  · intro h j
    have h1 := Oh_smul_latHat L hL (hO j) h
    have e : f j • ∑ i, f i • y i = f j • y j := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hf j, ite_smul, zero_smul]
      simp
    rwa [e] at h1
  · intro h
    exact AddSubgroup.sum_mem _ (fun i _ => h i)

end Split

theorem crd_int_smul {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ} (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ crdOf b L0, e • x ∈ crdOf b L0 := by
  intro e he x hx
  show ∑ i, (e • x) i • b i ∈ L0
  have : ∑ i, (e • x) i • b i = e • ∑ i, x i • b i := by
    rw [Finset.smul_sum]
    simp [smul_smul]
  rw [this]
  exact int_smul_mem L0 he hx

theorem equivFun_toLin {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (A : Matrix (Fin M) (Fin M) E) (v : V) :
    b.equivFun (Matrix.toLin b b A v) = A.mulVec (b.equivFun v) := by
  rw [Matrix.toLin_apply, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem equivFun_linOf_symm {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (v : V) :
    b.equivFun ((linOf b U).symm v) = ((U⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  rw [← equivFun_toLin]
  rfl

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem linOf_one_symm_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : (linOf b (1 : GL (Fin M) E)).symm v = v := by
  rw [LinearEquiv.symm_apply_eq, linOf_one_apply]

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def Floc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
    [AddCommGroup V] [Module (𝓞 E) V] (v : HeightOneSpectrum (𝓞 F)) (X : Submodule (𝓞 E) V) : Set V :=
  {x | ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) s • x ∈ X}

def PatchF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    Submodule.IsLattice E L0 →
    (∀ y : Fin M → E, PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y ∈ latHat F E (crdOf b L0) → y ∈ crdOf b L0) →
    ∀ (γ : UJ (σ : E →+* E) J) (T : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ g : HA (AF F) σ J, latSet σ J b L0 g =
        {x | (∀ v ∈ T, x ∈ Floc v (gmap (linOf b (γ : GL (Fin M) E)) L0)) ∧ (∀ v ∉ T, x ∈ Floc v L0)}

def SemiApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    ∀ N ∈ genus h L0, ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∃ γ : UJ (σ : E →+* E) (gramOf h b), ∀ v ∈ T,
        Floc v (gmap (linOf b (γ : GL (Fin M) E)) L0) = Floc v N

section Cheap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem mem_Floc_self (v : HeightOneSpectrum (𝓞 F)) (X : Submodule (𝓞 E) V) {x : V} (hx : x ∈ X) :
    x ∈ Floc v X :=
  ⟨1, fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem floc_le (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) : Floc v L ⊆ Floc v N := by
  rintro x ⟨s, hs, hsx⟩
  refine ⟨(D : 𝓞 F) * s, fun h => (v.isPrime.mem_or_mem h).elim hD hs, ?_⟩
  rw [map_mul, map_intCast, mul_smul]
  exact hLN _ hsx

theorem flocEq (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) (hNL : ∀ x ∈ N, (D : 𝓞 E) • x ∈ L) :
    Floc v L = Floc v N :=
  Set.Subset.antisymm (floc_le v L N D hD hLN) (floc_le v N L D hD hNL)

omit [NumberField E] in
theorem finF (D : ℤ) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((D : 𝓞 F)) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((D : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hD
  apply (Ideal.finite_factors hI).subset
  intro v hv
  show v.asIdeal ∣ Ideal.span {((D : 𝓞 F))}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem interLocStd [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ p : Ideal (𝓞 E), p.IsMaximal → ∃ t : 𝓞 E, t ∉ p ∧ t • x ∈ N) : x ∈ N := by
  classical
  have hfull : PI.LatLocGlob.IsFullLat E N := ⟨hN.fg, hN.span_eq_top⟩
  let N' : Submodule (𝓞 E) V := N ⊔ Submodule.span (𝓞 E) {x}
  have hfull' : PI.LatLocGlob.IsFullLat E N' := by
    refine ⟨hN.fg.sup (Submodule.fg_span_singleton x), ?_⟩
    apply eq_top_iff.2
    rw [← hN.span_eq_top]
    exact Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
  have hloc : ∀ p : Ideal (𝓞 E), p.IsMaximal → PI.LatLocGlob.loc p N' = PI.LatLocGlob.loc p N := by
    intro p hp
    haveI := hp.isPrime
    ext y
    constructor
    · rintro ⟨s, hs, hsy⟩
      obtain ⟨a, ha, z, hz, haz⟩ := Submodule.mem_sup.1 hsy
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
      obtain ⟨t, ht, htx⟩ := hx p hp
      refine ⟨t * s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hs, ?_⟩
      rw [mul_smul, ← haz, smul_add, smul_comm t r x]
      exact N.add_mem (N.smul_mem t ha) (N.smul_mem r htx)
    · rintro ⟨s, hs, hsy⟩
      exact ⟨s, hs, Submodule.mem_sup_left hsy⟩
  obtain ⟨L, _, huniq⟩ := latLocGlob (𝓞 E) E V N hfull (fun p => PI.LatLocGlob.loc p N)
    (fun p _ => ⟨N, hfull, rfl⟩) (Set.finite_empty.subset (fun p hp => hp.2 rfl))
  have e1 : N = L := huniq N ⟨hfull, fun p _ => rfl⟩
  have e2 : N' = L := huniq N' ⟨hfull', hloc⟩
  have : x ∈ N' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  rwa [e2, ← e1] at this

theorem interLocF [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), x ∈ Floc v N) : x ∈ N := by
  apply interLocStd N hN x
  intro p hp
  have hne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hcb : p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral (R := 𝓞 F) a)
  haveI := hp.isPrime
  let v : HeightOneSpectrum (𝓞 F) := ⟨p.comap (algebraMap (𝓞 F) (𝓞 E)), Ideal.comap_isPrime _ _, hcb⟩
  obtain ⟨s, hs, hsx⟩ := hx v
  exact ⟨algebraMap (𝓞 F) (𝓞 E) s, hs, hsx⟩

end Cheap

theorem surjStep_of_F (hP : PatchF) (hS : SemiApprox) (hO : LSOne) : SurjStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hL hsig N hN
  classical
  obtain ⟨D, hD0, hDL, hDN⟩ := cofinStep E V L0 N hL hN.1
  set T := (finF (F := F) D hD0).toFinset with hT
  have hTm : ∀ v, v ∉ T → ((D : 𝓞 F)) ∉ v.asIdeal := by
    intro v hv hDv
    exact hv ((Set.Finite.mem_toFinset _).2 hDv)
  obtain ⟨γ, hγ⟩ := hS F E σ V h M b L0 hσ hθ hsymm hnd hL N hN T
  have hsat : ∀ y : Fin M → E, PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y ∈ latHat F E (crdOf b L0) →
      y ∈ crdOf b L0 := by
    intro y hy
    rw [← hO F E σ V h M b L0 hσ hθ hτ hsymm hnd hL hsig]
    show (finMat σ (gramOf h b) (1 : HA (AF F) σ (gramOf h b))⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) y) ∈
      latHat F E (crdOf b L0)
    rw [inv_one, finMat_one, Matrix.one_mulVec]
    exact hy
  obtain ⟨g, hg⟩ := hP F E σ V M (gramOf h b) b L0 hL hsat γ T
  refine ⟨g, ?_⟩
  rw [hg]
  ext x
  rw [Set.mem_setOf_eq]
  have hout : ∀ v, v ∉ T → Floc v L0 = Floc v N := fun v hv => flocEq v L0 N D (hTm v hv) hDL hDN
  constructor
  · rintro ⟨h1, h2⟩
    apply interLocF (F := F) N hN.1 x
    intro v
    by_cases hv : v ∈ T
    · rw [← hγ v hv]
      exact h1 v hv
    · rw [← hout v hv]
      exact h2 v hv
  · intro hx
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [hγ v hv]
      exact mem_Floc_self v N hx
    · rw [hout v hv]
      exact mem_Floc_self v N hx

end PI.UnitaryGroupMassFormula.UJClassMass

end
end
