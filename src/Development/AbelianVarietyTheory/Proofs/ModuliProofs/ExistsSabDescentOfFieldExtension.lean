import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LevelActionTransitions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft

section
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IsoLift

open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem step_coprime_one {n r : ℕ} (hnr : IsCoprime (n : ℤ) (r : ℤ)) {f : D.La →ₗ[𝓞 E] D.La}
    (hf : IsSimMod D n f 1) :
    ∃ f', IsSimMod D (n * r) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
  obtain ⟨x, y, hxy⟩ := hnr
  obtain ⟨hc, hB⟩ := hf
  refine ⟨(y * r) • f + (x * n) • LinearMap.id, ⟨isCoprime_one_left, fun a b => ?_⟩,
    fun a => ⟨x • (a - f a), ?_⟩⟩
  · obtain ⟨B, hB⟩ := hB a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_zsmul,
      smul_eq_mul]
    refine ⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩
    push_cast
    linear_combination (y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b + D.EF a b) * hxy
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h : y * (r : ℤ) = 1 - n * x := by linear_combination hxy
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]; abel

theorem step_one (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La), IsSimMod D n f 1 →
    ∃ f', IsSimMod D (n * m) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f hf
    exact ⟨f, by simpa using hf, fun a => ⟨0, by simp⟩⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f', IsSimMod D (n * p) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2⟩
      · exact step_coprime_one D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, h1, h2⟩ := h1
    obtain ⟨f₂, h4, h5⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ h1
    exact ⟨f₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x)⟩

theorem exists_tower {N : ℕ} (hN : 0 < N) {f : D.La →ₗ[𝓞 E] D.La} (hf : IsSimMod D N f 1) :
    ∃ s : ℕ → (D.La →ₗ[𝓞 E] D.La), s 0 = f ∧ (∀ k, IsSimMod D (N * k.factorial) (s k) 1) ∧
      ∀ k j, k ≤ j → ∀ a, D.ModN (N * k.factorial) (s j a - s k a) := by
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) // IsSimMod D (N * k.factorial) x 1}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1 a - x.1 a)) := by
    intro k x
    obtain ⟨f', h1, h2⟩ := step_one D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ x.2
    refine ⟨⟨f', ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨f, by
    rw [Nat.factorial_zero, Nat.mul_one]; exact hf⟩ : T 0) nx k
  refine ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k j hkj => ?_⟩
  induction j, hkj using Nat.le_induction with
  | base => exact fun a => ⟨0, by simp⟩
  | succ j hkj ih =>
    have hd : N * k.factorial ∣ N * j.factorial :=
      Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
    exact fun a => modN_trans D (modN_of_dvd_modulus D hd (hnx j (s j) a)) (ih a)

theorem cls_eq_iff_modN {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ D.ModN n (a - b) := by
  rw [Submodule.Quotient.eq, mem_nLa]
  rfl

theorem exists_equiv (n : ℕ+) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ e : LaMod D n ≃ₗ[𝓞 E] LaMod D n, ∀ a, e (cls D n a) = cls D n (f a) := by
  obtain ⟨g, hg⟩ := exists_inv D n.pos hf
  have hle : ∀ u : D.La →ₗ[𝓞 E] D.La, nLa D n ≤ (nLa D n).comap u := by
    intro u x hx
    obtain ⟨y, rfl⟩ := (mem_nLa D).mp hx
    exact (mem_nLa D).mpr ⟨u y, map_nsmul u _ y⟩
  refine ⟨LinearEquiv.ofLinear ((nLa D n).mapQ _ f (hle f)) ((nLa D n).mapQ _ g (hle g)) ?_ ?_,
    fun a => rfl⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (cls_eq_iff_modN D).mpr (hg a).2
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (cls_eq_iff_modN D).mpr (hg a).1

end GlobalTheory.IsoLift

namespace GlobalTheory

open SimLift IsoLift IndefiniteRowSideFullHecke.LevelActionTransitions

end GlobalTheory
end
end

section
noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Dominates

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
  (hb : β'.comp b = β)

end Dominates

theorem mono_spMap_of_overring {O O' F : Type} [CommRing O] [CommRing O'] [Field F] {β : O →+* F} {β' : O' →+* F}
    (hβ : IsDedFrac β) (hβ' : Function.Injective β') (b : O →+* O') (hb : β'.comp b = β) : Mono (spMap b) := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
  letI := β.toAlgebra
  letI := b.toAlgebra
  have hb' : ∀ x, β' (b x) = β x := fun x => congrArg (fun f : O →+* F => f x) hb
  have hinj : Function.Injective β := IsFractionRing.injective O F
  have : IsDomain O' := hβ'.isDomain β'
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 fun x y h =>
    hinj (by rw [← hb', ← hb']; exact congrArg β' h)
  have : Module.Flat O O' := inferInstance
  have : Algebra.IsEpi O O' := (Algebra.isEpi_iff_forall_one_tmul_eq O O').2 fun x => by
    obtain ⟨y, a, ha, hx⟩ := IsFractionRing.div_surjective (A := O) (β' x)
    have ha0 : β a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hinj (h.trans (map_zero _).symm))
    have e : a • x = y • (1 : O') := hβ' (by
      change β' (b a * x) = β' (b y * 1)
      rw [_root_.mul_one, map_mul, hb', hb', ← hx]
      exact mul_div_cancel₀ _ ha0)
    refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := TensorProduct O O' O') ha ?_
    change a • _ = a • _
    rw [← TensorProduct.tmul_smul, TensorProduct.smul_tmul', e, TensorProduct.smul_tmul]
  have : Epi (CommRingCat.ofHom b) := CommRingCat.epi_iff_epi.2 this
  exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom b).op))

section Dense

variable (Y : Model Xo c β)

theorem densePart (h : IsDedFrac β) : IsLocallyNoetherian Y.X ∧ IsReduced Y.X ∧ Y.X.IsSeparated ∧
    IsPreimmersion Y.j ∧ Flat Y.j ∧ IsDominant Y.j ∧ QuasiCompact Y.j := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := h
  letI := β.toAlgebra
  obtain ⟨h₁, -, h₂, h₃⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x ↦
    have := (Y.normal x).1
    inferInstance
  exact ⟨h₁, isReduced_of_isReduced_stalk Y.X, h₂, h₃⟩

theorem hom_ext_j (h : IsDedFrac β) {f g : Y.X ⟶ Y.X} (e : Y.j ≫ f = Y.j ≫ g) : f = g := by
  obtain ⟨-, _, _, -, -, _, -⟩ := densePart Y h
  exact ext_of_isDominant Y.j e

theorem hom_ext_φ (h : IsDedFrac β) {f g : Y.t.G.left ⟶ Y.t.G.left} (e : Y.m.φ ≫ f = Y.m.φ ≫ g) : f = g := by
  obtain ⟨-, _, _, h₁, h₂, h₃, h₄⟩ := densePart Y h
  have := Y.t.semi.smooth
  have := Y.t.semi.separated
  have : IsReduced Y.t.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Y.t.G.hom
  have : Y.t.G.left.IsSeparated := ⟨by rw [← terminal.comp_from Y.t.G.hom]; infer_instance⟩
  have := (GlobalTheory.densePart_basic _ _ Y.j h₁ h₂ h₃ h₄).2.2.2 _ Y.t.G.hom inferInstance
  have p : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have : IsDominant Y.m.φ := by
    rw [← p.isoPullback_hom_fst]
    infer_instance
  exact ext_of_isDominant Y.m.φ e

end Dense

section Transition

variable {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O₂ : Type} [CommRing O₂] {β₂ : O₂ →+* c₂.F}
  (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (hl : l.Dvd l₂) (hF : c.F ≤ c₂.F) (b : O →+* O₂)
  (hb : β₂.comp b = (IntermediateField.inclusion hF).toRingHom.comp β) (π : Y₂.X ⟶ Y.X)

end Transition

section Algebra

open IndefiniteRowSideFullHecke.LevelActionTransitions

theorem exists_lift (n : ℕ+) (u : LaMod D n →ₗ[𝓞 E] LaMod D n) :
    ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, u (cls D n a) = cls D n (f a) := by
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (nLa D n).mkQ (u ∘ₗ (nLa D n).mkQ) (nLa D n).mkQ_surjective
  exact ⟨f, fun a => (LinearMap.congr_fun hf a).symm⟩

end Algebra

section Action

open IndefiniteRowSideFullHecke.LevelActionTransitions (KMax Sends FixesLevel modulus cls exists_sends)

variable (Y : Model Xo c β)

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have h := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance
  ⟨h.1, h.2.2⟩

theorem comp_over {r : Xo.XF c ⟶ Xo.XF c} (hr : r ≫ pullback.snd _ _ = pullback.snd _ _) :
    r ≫ pullback.fst _ _ ≫ Xo.s = pullback.fst _ _ ≫ Xo.s := by
  rw [pullback.condition, ← Category.assoc, hr]

theorem move_unique {r r' : Xo.XF c ⟶ Xo.XF c} (ν : SABMap Y.oF.t Y.oF.t r) (ν' : SABMap Y.oF.t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = pullback.snd _ _) (hr' : r' ≫ pullback.snd _ _ = pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) :
    r = r' ∧ ν.φ = ν'.φ := by
  let o := objOfSABMap Y.oF ν
  have e₁ : ∀ a, (o.eta a).left ≫ ν.φ = r ≫ (Y.oF.eta a).left := (objMapOfSABMap Y.oF ν).eta
  have e₂ : ∀ a, (o.etaA a).left ≫ ν.φ = r ≫ (Y.oF.etaA a).left := (objMapOfSABMap Y.oF ν).etaA
  have e₁' : ∀ a, (o.eta a).left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left := fun a => by
    obtain ⟨x, h, h'⟩ := hM a
    obtain rfl := sec_eq_secPull ν h
    exact h'
  have e₂' : ∀ a, (o.etaA a).left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left := fun a => by
    obtain ⟨x, h, h'⟩ := hA a
    obtain rfl := sec_eq_secPull ν h
    exact h'
  have key : ∀ {q : Xo.XF c ⟶ Xo.XF c} (n : SABMap o.t Y.oF.t q), (∀ a, (o.eta a).left ≫ n.φ = q ≫ (Y.oF.eta a).left) →
      (∀ a, (o.etaA a).left ≫ n.φ = q ≫ (Y.oF.etaA a).left) → Nonempty (ObjMap o Xo.univ (q ≫ pullback.fst _ _)) :=
    fun n h₁ h₂ => (ObjComp.objMap_comp Y.m0 (⟨n, h₁, h₂⟩ : ObjMap o Y.oF _)).nonempty
  have hf : r ≫ pullback.fst _ _ = r' ≫ pullback.fst _ _ :=
    (Xo.rep _ _ (isReduced_XF Xo c).1 o).unique ⟨Category.assoc _ _ _, key ν e₁ e₂⟩
      ⟨by rw [Category.assoc, comp_over hr', comp_over hr], key ν' e₁' e₂'⟩
  obtain rfl : r = r' := pullback.hom_ext hf (hr.trans hr'.symm)
  exact ⟨rfl, obj_rigid_closed abelianSchemeLaws_all.1 E H D l _ _ _ _ _ _ _ _ Y.oF o r (Or.inl (isReduced_XF Xo c).1)
    ν ν' fun a => ⟨_, e₁ a, e₁' a⟩⟩

def Moves (k : KMax D) (r : Xo.XF c ⟶ Xo.XF c) (ν : SABMap Y.oF.t Y.oF.t r) : Prop :=
  r ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ a b, Sends l k a b →
    (Y.oF.eta b).left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ (Y.oF.etaA b).left ≫ ν.φ = r ≫ (Y.oF.etaA a).left

variable {Y}

theorem Moves.unique {k : KMax D} {r r' : Xo.XF c ⟶ Xo.XF c} {ν : SABMap Y.oF.t Y.oF.t r}
    {ν' : SABMap Y.oF.t Y.oF.t r'} (h : Moves Y k r ν) (h' : Moves Y k r' ν') : r = r' ∧ ν.φ = ν'.φ :=
  move_unique Y ν ν' h.1 h'.1
    (fun a => (exists_sends l k a).elim fun b hb => ⟨_, (h.2 a b hb).1, (h'.2 a b hb).1⟩)
    (fun a => (exists_sends l k a).elim fun b hb => ⟨_, (h.2 a b hb).2, (h'.2 a b hb).2⟩)

variable (Y)

end Action

theorem normal_genericFibre (Y : Model Xo c β) (hβ : IsDedFrac β) :
    Geo.Tor.IsNormalScheme (pullback Y.s (spMap β)) ∧ IsLocallyNoetherian (pullback Y.s (spMap β)) := by
  obtain ⟨-, -, hfr⟩ := hβ
  let := β.toAlgebra
  have hb : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := c.F) (nonZeroDivisors O)
  have hbf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat c.F (nonZeroDivisors O))
  have : IsPreimmersion (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have := SchemeWords.isProper_of_isProjOver Y.proj
  refine ⟨fun x => ?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))⟩
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst Y.s (spMap β)) x
  have i := (asIso ((pullback.fst Y.s (spMap β)).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨_, _⟩ := Y.normal (pullback.fst Y.s (spMap β) x)
  exact ⟨i.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv i⟩

theorem isDedFrac_in_use (c : Coeff l) : IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧
    ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → IsDedFrac (c.V W).subtype :=
  ⟨(CoeffRings.coeff_isDedFrac E H l c).1, fun p W hp hW => ((CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW).1⟩

end GlobalTheory.ModelRelCompare
end
end
