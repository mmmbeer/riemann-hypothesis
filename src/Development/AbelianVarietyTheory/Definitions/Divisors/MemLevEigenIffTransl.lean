import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftedCharacterResidue

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevDesc

section Right

variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]

def IsRightAct (st : G → R →ₐ[K] R) : Prop :=
  (∀ x, st 1 x = x) ∧ ∀ h h' x, st (h * h') x = st h' (st h x)


theorem IsRightAct.comp {st : G → R →ₐ[K] R} (h : IsRightAct st) {G' : Type} [Group G'] (f : G' →* G) :
    IsRightAct (fun g => st (f g)) :=
  ⟨fun x => by simp only [map_one]; exact h.1 x, fun a b x => by simp only [map_mul]; exact h.2 _ _ x⟩

def funPull (K : Type) [Field K] {Z : Type} [MulAction G Z] (h : G) : (Z → K) →ₐ[K] (Z → K) :=
  Pi.algHom _ _ fun z => Pi.evalAlgHom K (fun _ : Z => K) (h • z)


variable (st : G → R →ₐ[K] R)

def IsRightAct.equiv {st : G → R →ₐ[K] R} (hs : IsRightAct st) (h : G) : R ≃ₐ[K] R :=
  AlgEquiv.ofAlgHom (st h) (st h⁻¹)
    (AlgHom.ext fun x => (hs.2 _ _ x).symm.trans (by rw [inv_mul_cancel]; exact hs.1 x))
    (AlgHom.ext fun x => (hs.2 _ _ x).symm.trans (by rw [mul_inv_cancel]; exact hs.1 x))

theorem IsRightAct.equiv_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (h : G) (x : R) :
    hs.equiv h x = st h x := rfl

def groupMat (u : R) : Matrix G G R := Matrix.of fun h g => st (h * g) u


def eigen (χ : G →* Kˣ) : Submodule K R where
  carrier := {F | ∀ h, st h F = ((χ h : Kˣ) : K) • F}
  zero_mem' := fun h => by simp
  add_mem' := fun {a b} ha hb h => by rw [map_add, ha h, hb h, smul_add]
  smul_mem' := fun c a ha h => by rw [map_smul, ha h, smul_comm]


def IsRightAct.leftRep {st : G → R →ₐ[K] R} (hs : IsRightAct st) : Representation K G R where
  toFun g := (st g⁻¹).toLinearMap
  map_one' := LinearMap.ext fun x => by rw [inv_one]; exact hs.1 x
  map_mul' g h := LinearMap.ext fun x => by rw [mul_inv_rev]; exact hs.2 _ _ x

theorem IsRightAct.leftRep_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (g : G) (x : R) :
    hs.leftRep g x = st g⁻¹ x := rfl


def IsRightAct.subRep {st : G → R →ₐ[K] R} (hs : IsRightAct st) (C : Submodule K R)
    (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) : Representation K G C :=
  hs.leftRep.subrepresentation C fun g x hx => hC g⁻¹ x hx

def algOp (e : MonoidAlgebra K G) : Module.End K R :=
  Finsupp.linearCombination K (fun g => (st g⁻¹).toLinearMap) e.coeff

theorem algOp_single (g : G) (a : K) (x : R) : algOp st (MonoidAlgebra.single g a) x = a • st g⁻¹ x := by
  simp [algOp]


theorem IsRightAct.algOp_eq {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e : MonoidAlgebra K G) :
    algOp st e = hs.leftRep.asAlgebraHom e := by
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp [algOp]
  | add a b ha hb => rw [map_add, ← ha, ← hb]; simp [algOp]
  | single g a => ext x; rw [algOp_single, Representation.asAlgebraHom_single]; rfl



variable [Fintype G]

def tr (χ : G →* Kˣ) : R →ₗ[K] R := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • (st h).toLinearMap

theorem tr_apply (χ : G →* Kˣ) (F : R) : tr st χ F = ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F := by
  rw [tr, LinearMap.sum_apply]; rfl

def ph (χ : G →* Kˣ) (u : R) : R →ₗ[K] (G → R) :=
  LinearMap.pi fun h => tr st χ ∘ₗ LinearMap.mulRight K (st h u)

def ps (u : R) : (G → R) →ₗ[K] R := ∑ h, LinearMap.mulRight K (st h u) ∘ₗ LinearMap.proj h

theorem IsRightAct.tr_mem_eigen {st : G → R →ₐ[K] R} (hs : IsRightAct st) (χ : G →* Kˣ) (F : R) :
    tr st χ F ∈ eigen st χ := fun g => by
  rw [tr_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
  rw [map_smul, ← hs.2, smul_smul, Equiv.coe_mulRight, map_mul]
  congr 1
  simp

theorem tr_of_mem_eigen {χ : G →* Kˣ} {F : R} (hF : F ∈ eigen st χ) : tr st χ F = (Fintype.card G : K) • F := by
  rw [tr_apply, Finset.sum_congr rfl (g := fun _ => F) fun h _ => by rw [hF h, smul_smul]; simp]
  simp [Nat.cast_smul_eq_nsmul]

theorem tr_mem {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (χ : G →* Kˣ) {x : R} (hx : x ∈ C) :
    tr st χ x ∈ C := by
  rw [tr_apply]; exact C.sum_mem fun g _ => C.smul_mem _ (hC _ x hx)

example [DecidableEq G] (h g : G) :
    groupMat (funPull K (Z := G)) (Pi.single (1 : G) (1 : K)) h g 1 = if h * g = 1 then 1 else 0 := by
  show (Pi.single (1 : G) (1 : K) : G → K) ((h * g) • (1 : G)) = _
  simp [Pi.single_apply]

end Right

section Lat

variable {G K R O : Type} [Group G] [Field K] [CommRing R] [Algebra K R] [CommRing O] [Algebra O K]
  {C : Submodule K R} [Module O C] [IsScalarTower O K C]

def latCap (L : Submodule O C) (W : Submodule K R) : Submodule O C :=
  L ⊓ (W.comap C.subtype).restrictScalars O



def spanQ (N : Submodule O C) : Submodule K R := (Submodule.span K (N : Set C)).map C.subtype

omit [Algebra O K] [IsScalarTower O K C] in

theorem mem_spanQ {N : Submodule O C} {F : C} (hF : F ∈ N) : (F : R) ∈ spanQ N :=
  ⟨F, Submodule.subset_span hF, rfl⟩

def cutLat (N : Submodule O C) (T : Module.End K R) : Submodule O C := latCap N ((spanQ N).map T)

theorem mem_cutLat_iff {N : Submodule O C} {T : Module.End K R} (hT : IsIdempotentElem T) {F : C} :
    F ∈ cutLat N T ↔ F ∈ N ∧ T F = F :=
  and_congr_right fun hF => ⟨fun ⟨x, _, e⟩ => by
      have e' : T x = F := e
      rw [← e']; exact congrArg (fun S : Module.End K R => S x) hT,
    fun e => ⟨F, mem_spanQ hF, e⟩⟩

theorem cutLat_one (N : Submodule O C) : cutLat N 1 = N :=
  Submodule.ext fun _ => (mem_cutLat_iff IsIdempotentElem.one).trans (and_iff_left rfl)


end Lat

section Quot

variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]

abbrev QMod (I : Ideal O) : Type := N ⧸ (I • (⊤ : Submodule O N))

abbrev QAut (I : Ideal O) : Type := QMod N I ≃ₗ[O] QMod N I

variable {N} {I J : Ideal O}

def qProj (h : I ≤ J) : QMod N I →ₗ[O] QMod N J := Submodule.factor (Submodule.smul_mono_left h)

theorem qProj_mk (h : I ≤ J) (x : N) : qProj h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem qProj_surjective (h : I ≤ J) : Function.Surjective (qProj (N := N) h) :=
  Submodule.factor_surjective (Submodule.smul_mono_left h)

theorem qProj_eq_zero (h : I ≤ J) (q : QMod N I) : qProj h q = 0 ↔ q ∈ J • (⊤ : Submodule O (QMod N I)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e : J • (⊤ : Submodule O (QMod N I)) = (J • (⊤ : Submodule O N)).map (I • (⊤ : Submodule O N)).mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [qProj_mk, Submodule.Quotient.mk_eq_zero, e]
  refine ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => ?_⟩
  have := Submodule.smul_mono_left h ((Submodule.Quotient.eq _).1 hyx)
  simpa using sub_mem hy this

theorem map_mem_smul_top {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M')
    {x : M} (hx : x ∈ J • (⊤ : Submodule O M)) : f x ∈ J • (⊤ : Submodule O M') := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

def endRed (h : I ≤ J) (γ : QMod N I →ₗ[O] QMod N I) : QMod N J →ₗ[O] QMod N J :=
  Submodule.liftQ _ (qProj h ∘ₗ γ ∘ₗ Submodule.mkQ _) fun _ hx =>
    (qProj_eq_zero h _).2 (map_mem_smul_top (γ ∘ₗ Submodule.mkQ _) hx)

theorem endRed_qProj (h : I ≤ J) (γ : QMod N I →ₗ[O] QMod N I) (q : QMod N I) :
    endRed h γ (qProj h q) = qProj h (γ q) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

def autRed (h : I ≤ J) : QAut N I →* QAut N J where
  toFun γ := LinearEquiv.ofLinear (endRed h γ) (endRed h γ.symm)
    (LinearMap.ext fun q => by
      obtain ⟨q, rfl⟩ := qProj_surjective h q
      simp [endRed_qProj])
    (LinearMap.ext fun q => by
      obtain ⟨q, rfl⟩ := qProj_surjective h q
      simp [endRed_qProj])
  map_one' := LinearEquiv.ext fun q => by
    obtain ⟨q, rfl⟩ := qProj_surjective h q
    exact endRed_qProj h _ q
  map_mul' γ δ := LinearEquiv.ext fun q => by
    obtain ⟨q, rfl⟩ := qProj_surjective h q
    show endRed h _ _ = endRed h _ (endRed h _ _)
    simp [endRed_qProj]

theorem autRed_qProj (h : I ≤ J) (γ : QAut N I) (q : QMod N I) : autRed h γ (qProj h q) = qProj h (γ q) :=
  endRed_qProj h _ q

variable (N I J) in

def trivMod : Subgroup (QAut N I) where
  carrier := {γ | ∀ q, γ q - q ∈ J • (⊤ : Submodule O (QMod N I))}
  one_mem' := fun q => by simp
  mul_mem' := by
    intro γ δ hγ hδ q
    have h := Submodule.add_mem _ (hγ (δ q)) (hδ q)
    rwa [sub_add_sub_cancel] at h
  inv_mem' := by
    intro γ hγ q
    have h := Submodule.neg_mem _ (hγ (γ⁻¹ q))
    have e : γ (γ⁻¹ q) = q := γ.apply_symm_apply q
    rwa [e, neg_sub] at h

theorem mem_trivMod {γ : QAut N I} : γ ∈ trivMod N I J ↔ ∀ q, γ q - q ∈ J • (⊤ : Submodule O (QMod N I)) := Iff.rfl

theorem autRed_eq_one (h : I ≤ J) (γ : QAut N I) : autRed h γ = 1 ↔ γ ∈ trivMod N I J := by
  refine ⟨fun e q => (qProj_eq_zero h _).1 ?_, fun e => LinearEquiv.ext fun q => ?_⟩
  · rw [map_sub, ← autRed_qProj, e]; exact sub_self _
  · obtain ⟨q, rfl⟩ := qProj_surjective h q
    rw [autRed_qProj]
    exact sub_eq_zero.1 ((map_sub (qProj h) _ _).symm.trans ((qProj_eq_zero h _).2 (e q)))

theorem trivMod_mono {J' : Ideal O} (h : J ≤ J') : trivMod N I J ≤ trivMod N I J' :=
  fun _ hγ q => Submodule.smul_mono_left h (hγ q)

theorem smul_top_qMod : I • (⊤ : Submodule O (QMod N I)) = ⊥ :=
  eq_bot_iff.2 fun q hq => by
    have := (qProj_eq_zero (le_refl I) q).2 hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact this

theorem trivMod_sup : trivMod N I (I ⊔ J) = trivMod N I J := by
  ext γ
  rw [mem_trivMod, mem_trivMod, Submodule.sup_smul, smul_top_qMod, bot_sup_eq]

example : trivMod N I ⊤ = ⊤ ∧ trivMod N I I = ⊥ := by
  refine ⟨eq_top_iff.2 fun γ _ q => by simp, eq_bot_iff.2 fun γ hγ => LinearEquiv.ext fun q => ?_⟩
  have := hγ q
  rw [smul_top_qMod] at this
  exact sub_eq_zero.1 this

theorem mem_iInf_smul_top {ι M : Type} [Finite ι] [AddCommGroup M] [Module O M] {Js : ι → Ideal O}
    (hc : Pairwise (Function.onFun IsCoprime Js)) {x : M} (hx : ∀ i, x ∈ Js i • (⊤ : Submodule O M)) :
    x ∈ (⨅ i, Js i) • (⊤ : Submodule O M) := by
  rw [← Ideal.ker_tensorProductMk_quotient M Js hc, LinearMap.mem_ker]
  funext i
  apply (TensorProduct.quotTensorEquivQuotSMul M (Js i)).injective
  show TensorProduct.quotTensorEquivQuotSMul M (Js i) (1 ⊗ₜ x) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Pi.zero_apply, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).2 (hx i)

section CRT

variable {ι : Type} [Finite ι] {Js : ι → Ideal O} (hle : ∀ i, I ≤ Js i)
  (hc : Pairwise (Function.onFun IsCoprime Js)) (hI : ⨅ i, Js i ≤ I)

def crt : QMod N I ≃ₗ[O] ∀ i, QMod N (Js i) :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => qProj (hle i)) ⟨by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have := Submodule.smul_mono_left hI
      (mem_iInf_smul_top hc fun i => (qProj_eq_zero (hle i) q).1 (congrFun hq i))
    rwa [smul_top_qMod] at this, by
    intro y
    obtain ⟨x, hx⟩ := Ideal.pi_tensorProductMk_quotient_surjective N Js hc
      fun i => (TensorProduct.quotTensorEquivQuotSMul N (Js i)).symm (y i)
    refine ⟨Submodule.Quotient.mk x, funext fun i => ?_⟩
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul N (Js i)) (congrFun hx i)
    rw [LinearEquiv.apply_symm_apply] at this
    exact (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x).symm.trans this⟩

theorem crt_apply (q : QMod N I) (i : ι) : crt hle hc hI q i = qProj (hle i) q := rfl

def crtAut : QAut N I ≃* ∀ i, QAut N (Js i) :=
  MulEquiv.ofBijective (Pi.monoidHom fun i => autRed (hle i)) ⟨by
    intro γ δ e
    refine LinearEquiv.ext fun q => (crt hle hc hI).injective (funext fun i => ?_)
    have e' : autRed (hle i) γ = autRed (hle i) δ := congrFun e i
    rw [crt_apply, crt_apply, ← autRed_qProj, ← autRed_qProj, e'], by
    intro g
    refine ⟨(crt hle hc hI).trans ((LinearEquiv.piCongrRight g).trans (crt hle hc hI).symm),
      funext fun i => LinearEquiv.ext fun q => ?_⟩
    obtain ⟨q, rfl⟩ := qProj_surjective (hle i) q
    show autRed (hle i) _ _ = _
    rw [autRed_qProj, ← crt_apply hle hc hI, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    rfl⟩


end CRT

end Quot

section Mat

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {r p : ℕ} (e : M ≃+ (Fin r → ZMod p))

def endMat : Module.End O M →* Matrix (Fin r) (Fin r) (ZMod p) where
  toFun γ := LinearMap.toMatrix' (AddMonoidHom.toZModLinearMap p
    (e.toAddMonoidHom.comp (γ.toAddMonoidHom.comp e.symm.toAddMonoidHom)))
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp
  map_mul' γ δ := by
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp

theorem endMat_mulVec (γ : Module.End O M) (x : M) : (endMat e γ).mulVec (e x) = e (γ x) := by
  simp [endMat, LinearMap.toMatrix'_mulVec]

def autMat : (M ≃ₗ[O] M) →* GL (Fin r) (ZMod p) :=
  ((endMat e).comp (LinearEquiv.automorphismGroup.toLinearMapMonoidHom)).toHomUnits

theorem autMat_mulVec (γ : M ≃ₗ[O] M) (x : M) :
    (autMat e γ : Matrix (Fin r) (Fin r) (ZMod p)).mulVec (e x) = e (γ x) := endMat_mulVec e _ x

theorem autMat_injective : Function.Injective (autMat (O := O) e) := fun γ δ h =>
  LinearEquiv.ext fun x => e.injective (by rw [← autMat_mulVec, ← autMat_mulVec, h])

theorem autMat_surjective (hO : ∀ a : O, ∃ n : ℤ, ∀ x : M, a • x = n • x) :
    Function.Surjective (autMat (O := O) e) := fun g => by
  let f : M ≃+ M := e.trans ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.trans e.symm)
  refine ⟨f.toLinearEquiv fun a x => ?_, Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)⟩
  · obtain ⟨n, hn⟩ := hO a
    rw [hn, hn, map_zsmul]
  · rw [← e.apply_symm_apply (Pi.single i 1), autMat_mulVec]
    simp [f]

end Mat

end GlobalTheory.LevDesc
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevDesc

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

section Ideals

theorem mem_sup_span_mul {O : Type} [CommRing O] {I : Ideal O} {a b x : O} (h : IsCoprime a b)
    (ha : x ∈ I ⊔ Ideal.span {a}) (hb : x ∈ I ⊔ Ideal.span {b}) : x ∈ I ⊔ Ideal.span {a * b} := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨y, hy, _, hz, e⟩ := Submodule.mem_sup.1 ha
  obtain ⟨y', hy', _, hz', e'⟩ := Submodule.mem_sup.1 hb
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz'
  refine Submodule.mem_sup.2 ⟨u * a * y' + v * b * y, add_mem (I.mul_mem_left _ hy') (I.mul_mem_left _ hy),
    (u * t + v * s) * (a * b), Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, ?_⟩
  linear_combination (u * a) * e' + (v * b) * e + x * huv

theorem absNorm_eq_of_split {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hw : (p : 𝓞 E) ∈ P) : Ideal.absNorm P = p := by
  classical
  obtain ⟨hc, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hN : Ideal.absNorm I = p ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hprod : M.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hge : ∀ P ∈ M, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    have hd : Ideal.absNorm P ∣ p ^ Module.finrank ℚ E := hN ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    rw [hj] at h1 ⊢
    exact Nat.le_self_pow (by rintro rfl; simp at h1) p
  have hwM : P ∈ M := (Ideal.mem_normalizedFactors_iff hI0).2
    ⟨hP, by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hw⟩
  refine le_antisymm ?_ (hge _ hwM)
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hwM
  have h2 : p ^ M'.card ≤ (M'.map Ideal.absNorm).prod := by
    have := Multiset.pow_card_le_prod (s := M'.map Ideal.absNorm) (a := p) (fun x hx => by
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
      exact hge P (hM' ▸ Multiset.mem_cons_of_mem hP))
    simpa using this
  have h3 : Ideal.absNorm P * (M'.map Ideal.absNorm).prod = p * p ^ M'.card := by
    rw [← pow_succ', ← Multiset.card_cons P, ← hM', hc, ← hN, ← hprod, hM', Multiset.prod_cons, map_mul,
      map_multiset_prod]
  by_contra hlt
  have hlt' := not_le.1 hlt
  have hpos : 0 < p ^ M'.card := pow_pos hp.pos _
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def halfPrime (l : Level H) (v : Ideal (𝓞 (maximalRealSubfield E))) : Ideal (𝓞 E) :=
  l.Mb ⊔ v.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))

theorem natCast_M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem bar_bar' (a : 𝓞 E) : H.bar (H.bar a) = a :=
  Subtype.ext (by
    show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

theorem bar_algebraMap (a : 𝓞 (maximalRealSubfield E)) :
    H.bar (algebraMap _ (𝓞 E) a) = algebraMap _ (𝓞 E) a :=
  Subtype.ext (by
    show ((H.bar (algebraMap _ (𝓞 E) a) : 𝓞 E) : E) = _
    rw [H.bar_eq]
    exact (IsCMField.complexConj E).commutes (a : maximalRealSubfield E))

theorem exists_norm (y : 𝓞 E) : ∃ z : 𝓞 (maximalRealSubfield E), algebraMap _ (𝓞 E) z = y * H.bar y := by
  have h1 : ((y * H.bar y : 𝓞 E) : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, ← H.bar_eq, map_mul, bar_bar', mul_comm]
  refine ⟨⟨⟨_, h1⟩, ?_⟩, rfl⟩
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E) Subtype.val_injective).1
    (y * H.bar y).2

theorem halfPrime_eq (l : Level H) {v : Ideal (𝓞 (maximalRealSubfield E))} (hv : v.IsMaximal) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (h : halfPrime l v ≤ P) : halfPrime l v = P := by
  refine le_antisymm h fun x hx => ?_
  have hc : v = P.comap (algebraMap _ (𝓞 E)) :=
    hv.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans h))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  obtain ⟨b', hb', rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb
  change a + H.bar b' = 1 at hab
  have hab' : H.bar a + b' = 1 := by simpa [bar_bar'] using congrArg H.bar hab
  obtain ⟨z, hz⟩ := exists_norm (H := H) (H.bar b' * x + a)
  have hzv : z ∈ v := by
    rw [hc, Ideal.mem_comap, hz]
    exact P.mul_mem_right _ (add_mem (P.mul_mem_left _ hx) (h (Ideal.mem_sup_left ha)))
  have h1 := Ideal.mem_map_of_mem (algebraMap _ (𝓞 E)) hzv
  rw [hz, map_add, map_mul, bar_bar'] at h1
  refine Submodule.mem_sup.2 ⟨a * (x - 1) + b' * ((1 - H.bar x) * (H.bar b' * x + a)),
    add_mem (l.Mb.mul_mem_right _ ha) (l.Mb.mul_mem_right _ hb'), _, h1, ?_⟩
  linear_combination x * hab + (H.bar b' * x + a) * hab'

theorem halfPrime_isPrime (l : Level H) {v : Ideal (𝓞 (maximalRealSubfield E))} (hv : v.IsMaximal)
    (hM : (l.M : 𝓞 (maximalRealSubfield E)) ∈ v) : (halfPrime l v).IsPrime := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v
    (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).1
        (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  have hvQ : v.map (algebraMap _ (𝓞 E)) ≤ Q := Ideal.map_le_iff_le_comap.2 hQv.ge
  have hMQ : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Q := by
    rw [l.prod, Ideal.span_singleton_le_iff_mem]
    simpa using hvQ (Ideal.mem_map_of_mem _ hM)
  rcases hQ.isPrime.mul_le.1 hMQ with h | h
  · rw [halfPrime_eq l hv hQ.isPrime (sup_le h hvQ)]; exact hQ.isPrime
  · haveI := hQ.isPrime
    have hP : (Q.comap (H.bar : 𝓞 E →+* 𝓞 E)).IsPrime := inferInstance
    rw [halfPrime_eq l hv hP (sup_le (Ideal.map_le_iff_le_comap.1 h) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_))]
    · exact hP
    · show H.bar (algebraMap _ (𝓞 E) a) ∈ Q
      rw [bar_algebraMap]; exact hvQ (Ideal.mem_map_of_mem _ ha)

end Ideals

section Generic

theorem superDiag_mul {r : ℕ} {k : Type} [Field k] {u u' : GL (Fin r) k} (hu : u ∈ unitri r k) (hu' : u' ∈ unitri r k) :
    superDiag ((u * u' : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      superDiag (u : Matrix (Fin r) (Fin r) k) + superDiag (u' : Matrix (Fin r) (Fin r) k) := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have hij : j ≠ i := fun e => by rw [e] at h; omega
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem j i (Finset.mem_univ _) (Finset.mem_univ _) hij,
      hu.2, hu'.2, one_mul, mul_one]
    intro c _ hc
    by_cases hci : c < i
    · rw [hu.1 (show id c < id i from hci), zero_mul]
    · have h1 : (c : ℕ) ≠ j := fun e => hc.1 (Fin.ext e)
      have h2 : (c : ℕ) ≠ i := fun e => hc.2 (Fin.ext e)
      have h3 : ¬ (c : ℕ) < i := hci
      rw [hu'.1 (show id j < id c from (by show (j : ℕ) < c; omega)), mul_zero]
  · simp

variable {R : Ranks} {Hs : Host R} {K : Type} [Field K]

def genChar (ψ : ∀ v : Sq Hs, AddChar (ZMod (Hs.g v.1)) K) : levelU Hs →* Kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun u => psiU ψ (u : LevelGroup Hs)
      map_one' := by
        refine Finset.prod_eq_one fun v _ => ?_
        have : superDiag (((((1 : levelU Hs) : LevelGroup Hs) v : GL (Fin R.r) (ZMod (Hs.g v.1))) :
            Matrix (Fin R.r) (Fin R.r) (ZMod (Hs.g v.1)))) = 0 :=
          Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
            split_ifs with h
            · exact Matrix.one_apply_ne fun e => by rw [e] at h; omega
            · rfl
        rw [this, AddChar.map_zero_eq_one]
      map_mul' := fun a b => by
        simp only [psiU, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [← AddChar.map_add_eq_mul, ← superDiag_mul (a.2 v trivial) (b.2 v trivial)]
        rfl }

theorem genChar_apply (ψ : ∀ v : Sq Hs, AddChar (ZMod (Hs.g v.1)) K) (u : levelU Hs) :
    ((genChar ψ u : Kˣ) : K) = psiU ψ (u : LevelGroup Hs) := rfl

variable (Hs)

def factorG (i : Fin 2) : Subgroup (LevelGroup Hs) := Subgroup.pi {v | v.1 ≠ i} fun _ => ⊥

def levelGU (i : Fin 2) : Subgroup (LevelGroup Hs) := Subgroup.pi {v | v.1 ≠ i} fun v => unitri R.r (ZMod (Hs.g v.1))

theorem exists_factor (a : LevelGroup Hs) : ∃ b ∈ factorG Hs 0, ∃ c ∈ factorG Hs 1, a = b * c ∧
    (∀ v, v.1 = 0 → b v = a v) ∧ ∀ v, v.1 = 1 → c v = a v := by
  refine ⟨fun v => if v.1 = 0 then a v else 1, fun v hv => if_neg hv, fun v => if v.1 = 1 then a v else 1,
    fun v hv => if_neg hv, funext fun v => ?_, fun v h => if_pos h, fun v h => if_pos h⟩
  obtain ⟨i, w⟩ := v
  fin_cases i <;> simp

end Generic

section Groups

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)

def typePrime (v : Sq D.host) : Ideal (𝓞 D.host.E) := halfPrime l v.2.1.asIdeal

def cofactor : ℕ := l.M / (D.host.g 0 * D.host.g 1)

def IsTypeLevel : Prop :=
  l.A = 1 ∧ l.M = D.host.g 0 * D.host.g 1 * cofactor l ∧ Nat.Coprime (D.host.g 0 * D.host.g 1) (cofactor l)

abbrev TypeFrame : Type :=
  ∀ v : Sq D.host, QMod Dw.La (typePrime l v) ≃+ (Fin D.R.r → ZMod (D.host.g v.1))

def grpR : Subgroup (LevelAut Dw l) :=
  trivMod Dw.La l.Mb (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)})

def grpG : Subgroup (LevelAut Dw l) := trivMod Dw.La l.Mb (Ideal.span {((cofactor l : ℕ) : 𝓞 D.host.E)})

variable {Dw l}

theorem isTypeLevel_of_eq {m : ℕ} (hA : l.A = 1) (hM : l.M = D.host.g 0 * D.host.g 1 * m)
    (hm : Nat.Coprime (D.host.g 0 * D.host.g 1) m) : IsTypeLevel l ∧ cofactor l = m := by
  have h : cofactor l = m := by
    rw [cofactor, hM, Nat.mul_div_cancel_left _ (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)]
  exact ⟨⟨hA, h ▸ hM, h ▸ hm⟩, h⟩

theorem isTypeLevel_of_pin {Q : Par D} (h : Q.PinLevel) : IsTypeLevel Q.l ∧ cofactor Q.l = 1 :=
  isTypeLevel_of_eq h.2 (by rw [mul_one]; exact h.1) (Nat.coprime_one_right _)

theorem g_mem_typePrime (v : Sq D.host) : ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) ∈ typePrime l v :=
  Ideal.mem_sup_right (by simpa using Ideal.mem_map_of_mem (algebraMap _ (𝓞 D.host.E)) v.2.2)

theorem g_dvd (i : Fin 2) : D.host.g i ∣ D.host.g 0 * D.host.g 1 := by
  fin_cases i
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

theorem g_coprime {i j : Fin 2} (h : i ≠ j) : Nat.Coprime (D.host.g i) (D.host.g j) := by
  rw [Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)]
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact D.host.g_ne
  · exact D.host.g_ne.symm
  · exact absurd rfl h

theorem isCoprime_of_natCast {O : Type} [CommRing O] {I J : Ideal O} {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : O) ∈ I)
    (hb : (b : O) ∈ J) : IsCoprime I J := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := O) h
  exact Ideal.isCoprime_iff_exists.2 ⟨_, I.mul_mem_left u ha, _, J.mul_mem_left v hb, huv⟩

theorem typePrime_coprime : Pairwise (Function.onFun IsCoprime (typePrime l)) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ hne
  by_cases h : i = j
  · subst h
    have hvw : v.1 ≠ w.1 := fun e => hne (congrArg _ (Subtype.ext e))
    obtain ⟨a, ha, b, hb, e⟩ := Ideal.isCoprime_iff_exists.1 (HeightOneSpectrum.isCoprime_of_ne _ _ hvw)
    exact Ideal.isCoprime_iff_exists.2 ⟨_, Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha), _,
      Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb), by rw [← map_add, e, map_one]⟩
  · exact isCoprime_of_natCast (g_coprime h) (g_mem_typePrime ⟨i, v⟩) (g_mem_typePrime ⟨j, w⟩)

theorem iInf_typePrime_le :
    ⨅ v, typePrime l v ≤ l.Mb ⊔ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  intro x hx
  have key : ∀ i, x ∈ l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)} := by
    intro i
    have h0 : Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime i).ne_zero
    have hsq : Squarefree (l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}) :=
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
        (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D i).2).squarefree_of_dvd (Ideal.dvd_iff_le.2 le_sup_right)
    have hx' : x ∈ (l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hP, hPp⟩
      have hg : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) P := by
        rw [Ideal.mem_comap, map_natCast]; exact hP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) P, inferInstance, fun e => by
        rw [e, Ideal.mem_bot] at hg
        exact (D.host.g_prime i).ne_zero (by exact_mod_cast hg)⟩
      have hle : typePrime l ⟨i, ⟨v, hg⟩⟩ ≤ P := sup_le (le_sup_left.trans hP) Ideal.map_comap_le
      exact hle (Ideal.mem_iInf.1 hx _)
    obtain ⟨n, hn⟩ := hx'
    refine Ideal.dvd_span_singleton.1 (hsq.isRadical n _ ?_)
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_span_singleton.2 hn
  rw [Nat.cast_mul]
  exact mem_sup_span_mul (Nat.Coprime.cast (g_coprime (by decide))) (key 0) (key 1)

theorem IsTypeLevel.typePrime_spec (hl : IsTypeLevel l) (v : Sq D.host) :
    (typePrime l v).IsPrime ∧ Ideal.absNorm (typePrime l v) = D.host.g v.1 := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd v.1).mul_right (cofactor l)
    rw [hl.2.1, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  exact ⟨hP, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v)⟩

theorem IsTypeLevel.smul_eq_zsmul (hl : IsTypeLevel l) (v : Sq D.host) (a : 𝓞 D.host.E) :
    ∃ n : ℤ, ∀ x : QMod Dw.La (typePrime l v), a • x = n • x := by
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l v) = D.host.g v.1 := by
    rw [← (hl.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ typePrime l v)
  obtain ⟨z, hz⟩ := (ZMod.ringEquivOfPrime (𝓞 D.host.E ⧸ typePrime l v) (D.host.g_prime v.1)
    (by rw [← Nat.card_eq_fintype_card, hc])).surjective (Ideal.Quotient.mk _ a)
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (typePrime l v)), Ideal.Quotient.eq] at hz
  refine ⟨n, fun x => ?_⟩
  have h : ((n : 𝓞 D.host.E) - a) • x ∈ typePrime l v • (⊤ : Submodule _ (QMod Dw.La (typePrime l v))) :=
    Submodule.smul_mem_smul hz trivial
  rw [smul_top_qMod, Submodule.mem_bot, sub_smul, sub_eq_zero, Int.cast_smul_eq_zsmul] at h
  exact h.symm

theorem nonempty_addEquiv_pi {M : Type} [AddCommGroup M] {p r : ℕ} [hp : Fact p.Prime] (h : ∀ x : M, p • x = 0)
    (hN : Nat.card M = p ^ r) : Nonempty (M ≃+ (Fin r → ZMod p)) := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (hN ▸ pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨inst⟩ : Nonempty (Module (ZMod p) M) := ⟨AddCommGroup.zmodModule h⟩
  have hf : Module.finrank (ZMod p) M = Module.finrank (ZMod p) (Fin r → ZMod p) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
    rw [hN, Nat.card_zmod] at this
    rw [Module.finrank_fin_fun]
    exact (Nat.pow_right_injective hp.out.two_le this).symm
  haveI : FiniteDimensional (ZMod p) M := Module.Finite.of_finite
  exact ⟨(LinearEquiv.ofFinrankEq (R := ZMod p) M (Fin r → ZMod p) hf).toAddEquiv⟩

theorem IsTypeLevel.nonempty_typeFrame (hl : IsTypeLevel l) (hr : Dw.p + Dw.q = D.R.r) : Nonempty (TypeFrame Dw l) := by
  refine ⟨fun v => Classical.choice ?_⟩
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l v) = D.host.g v.1 := by
    rw [← (hl.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Dw.fin
  haveI := Dw.proj
  have hN : Nat.card (QMod Dw.La (typePrime l v)) = D.host.g v.1 ^ D.R.r := by
    rw [natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]
  refine nonempty_addEquiv_pi (fun x => ?_) hN
  have h : ((D.host.g v.1 : ℕ) : 𝓞 D.host.E) • x ∈ typePrime l v • (⊤ : Submodule _ (QMod Dw.La (typePrime l v))) :=
    Submodule.smul_mem_smul (g_mem_typePrime v) trivial
  rwa [smul_top_qMod, Submodule.mem_bot, Nat.cast_smul_eq_nsmul] at h

def typeRed (fr : TypeFrame Dw l) : LevelAut Dw l →* LevelGroup D.host :=
  MonoidHom.pi fun v => (autMat (fr v)).comp (autRed (N := Dw.La) (J := typePrime l v) le_sup_left)

theorem typeRed_mulVec (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host) (q : LaMod Dw l) :
    (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).mulVec
      (fr v (qProj (J := typePrime l v) le_sup_left q)) = fr v (qProj (J := typePrime l v) le_sup_left (γ q)) :=
  (autMat_mulVec (fr v) _ _).trans (congrArg _ (autRed_qProj _ γ q))

theorem mem_grpR_iff {γ : LevelAut Dw l} : γ ∈ grpR Dw l ↔ ∀ v, γ ∈ trivMod Dw.La l.Mb (typePrime l v) := by
  refine ⟨fun h v => trivMod_mono ?_ h, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := g_dvd (D := D) v.1
    rw [Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (g_mem_typePrime v)
  · rw [grpR, ← trivMod_sup]
    exact trivMod_mono iInf_typePrime_le fun q => mem_iInf_smul_top typePrime_coprime fun v => h v q

theorem typeRed_eq_one (fr : TypeFrame Dw l) {γ : LevelAut Dw l} : typeRed fr γ = 1 ↔ γ ∈ grpR Dw l := by
  rw [mem_grpR_iff, funext_iff]
  refine forall_congr' fun v => Iff.trans ?_ (autRed_eq_one (J := typePrime l v) le_sup_left γ)
  exact map_eq_one_iff _ (autMat_injective (fr v))

def partIdeal (l : Level H) : Option (Sq D.host) → Ideal (𝓞 D.host.E)
  | none => l.Mb ⊔ Ideal.span {((cofactor l : ℕ) : 𝓞 D.host.E)}
  | some v => typePrime l v

theorem le_partIdeal : ∀ o, l.Mb ≤ partIdeal l o
  | none => le_sup_left
  | some _ => le_sup_left

theorem IsTypeLevel.partIdeal_coprime (hl : IsTypeLevel l) : Pairwise (Function.onFun IsCoprime (partIdeal l)) := by
  have key : ∀ v, IsCoprime (partIdeal l (some v)) (partIdeal l none) := fun v =>
    isCoprime_of_natCast (hl.2.2.coprime_dvd_left (g_dvd v.1)) (g_mem_typePrime v)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rintro (_ | v) (_ | w) h
  · exact absurd rfl h
  · exact (key w).symm
  · exact key v
  · exact typePrime_coprime fun e => h (congrArg _ e)

theorem IsTypeLevel.iInf_partIdeal_le (hl : IsTypeLevel l) : ⨅ o, partIdeal l o ≤ l.Mb := by
  intro x hx
  have h := mem_sup_span_mul (Nat.Coprime.cast hl.2.2)
    (iInf_typePrime_le (Ideal.mem_iInf.2 fun v => Ideal.mem_iInf.1 hx (some v))) (Ideal.mem_iInf.1 hx none)
  rw [← Nat.cast_mul, ← hl.2.1] at h
  exact sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (natCast_M_mem l)) h

def IsTypeLevel.parts (hl : IsTypeLevel l) : LevelAut Dw l ≃* ∀ o, QAut Dw.La (partIdeal l o) :=
  crtAut le_partIdeal hl.partIdeal_coprime hl.iInf_partIdeal_le

theorem IsTypeLevel.grpG_inf_grpR (hl : IsTypeLevel l) : grpG Dw l ⊓ grpR Dw l = ⊥ := by
  refine eq_bot_iff.2 fun γ hγ => (map_eq_one_iff _ hl.parts.injective).1 (funext fun o => ?_)
  cases o with
  | none => exact (autRed_eq_one _ γ).2 (trivMod_mono le_sup_right hγ.1)
  | some v => exact (autRed_eq_one _ γ).2 (mem_grpR_iff.1 hγ.2 v)

theorem IsTypeLevel.typeRed_bijective (hl : IsTypeLevel l) (fr : TypeFrame Dw l) :
    Function.Bijective ((typeRed fr).comp (grpG Dw l).subtype) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun γ hγ => Subtype.ext ?_, fun a => ?_⟩
  · exact Subgroup.mem_bot.1 (hl.grpG_inf_grpR ▸ ⟨γ.2, (typeRed_eq_one fr).1 hγ⟩)
  · choose b hb using fun v => autMat_surjective (fr v) (hl.smul_eq_zsmul v) (a v)
    obtain ⟨γ, hγ⟩ := (hl.parts (Dw := Dw)).surjective fun o => match o with
      | none => 1
      | some v => b v
    refine ⟨⟨γ, ?_⟩, funext fun v => ?_⟩
    · rw [grpG, ← trivMod_sup]
      exact (autRed_eq_one (le_partIdeal none) γ).1 (congrFun hγ none)
    · exact (congrArg (autMat (fr v)) (congrFun hγ (some v))).trans (hb v)

def typeEmb (hl : IsTypeLevel l) (fr : TypeFrame Dw l) : LevelGroup D.host →* LevelAut Dw l :=
  (grpG Dw l).subtype.comp (MulEquiv.ofBijective _ (hl.typeRed_bijective fr)).symm.toMonoidHom

theorem typeRed_typeEmb (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (a : LevelGroup D.host) :
    typeRed fr (typeEmb hl fr a) = a :=
  (MulEquiv.ofBijective _ (hl.typeRed_bijective fr)).apply_symm_apply a

theorem typeEmb_mem (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (a : LevelGroup D.host) : typeEmb hl fr a ∈ grpG Dw l :=
  Subtype.property _

theorem IsTypeLevel.commute (hl : IsTypeLevel l) {γ δ : LevelAut Dw l} (hγ : γ ∈ grpG Dw l) (hδ : δ ∈ grpR Dw l) :
    Commute γ δ := by
  refine hl.parts.injective ?_
  rw [map_mul, map_mul]
  funext o
  cases o with
  | none =>
    have : hl.parts γ none = 1 := (autRed_eq_one _ γ).2 (trivMod_mono le_sup_right hγ)
    simp [this]
  | some v =>
    have : hl.parts δ (some v) = 1 := (autRed_eq_one _ δ).2 (mem_grpR_iff.1 hδ v)
    simp [this]

def prodEquiv (hl : IsTypeLevel l) (fr : TypeFrame Dw l) : LevelGroup D.host × grpR Dw l ≃* LevelAut Dw l :=
  MulEquiv.ofBijective
    ((typeEmb hl fr).noncommCoprod (grpR Dw l).subtype fun a b => hl.commute (typeEmb_mem hl fr a) b.2) ⟨by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ h
      have h' : typeEmb hl fr a * b = 1 := h
      have h1 : a = 1 := by
        have := congrArg (typeRed fr) h'
        rwa [map_mul, typeRed_typeEmb, (typeRed_eq_one fr).2 b.2, mul_one, map_one] at this
      subst h1
      rw [map_one, one_mul] at h'
      exact Prod.ext rfl (Subtype.ext h'), fun γ =>
      ⟨(typeRed fr γ, ⟨(typeEmb hl fr (typeRed fr γ))⁻¹ * γ, (typeRed_eq_one fr).1 (by
        rw [map_mul, map_inv, typeRed_typeEmb, inv_mul_cancel])⟩), mul_inv_cancel_left _ _⟩⟩

theorem prodEquiv_apply (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (a : LevelGroup D.host) (b : grpR Dw l) :
    prodEquiv hl fr (a, b) = typeEmb hl fr a * b := rfl

theorem typeRed_prodEquiv (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (x : LevelGroup D.host × grpR Dw l) :
    typeRed fr (prodEquiv hl fr x) = x.1 := by
  rw [prodEquiv_apply, map_mul, typeRed_typeEmb, (typeRed_eq_one fr).2 x.2.2, mul_one]

def grpOf (fr : TypeFrame Dw l) (S : Subgroup (LevelGroup D.host)) : Subgroup (LevelAut Dw l) := S.comap (typeRed fr)

def grpHR (fr : TypeFrame Dw l) : Subgroup (LevelAut Dw l) := grpOf fr (levelU D.host)

def grpGHR (fr : TypeFrame Dw l) (i : Fin 2) : Subgroup (LevelAut Dw l) := grpOf fr (levelGU D.host i)

def grpOfEquiv (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (S : Subgroup (LevelGroup D.host)) :
    S × grpR Dw l ≃* grpOf fr S where
  toFun x := ⟨prodEquiv hl fr (x.1, x.2), by
    show typeRed fr _ ∈ S
    rw [typeRed_prodEquiv]; exact x.1.2⟩
  invFun γ := (⟨((prodEquiv hl fr).symm γ).1, by
    rw [← typeRed_prodEquiv hl fr, MulEquiv.apply_symm_apply]; exact γ.2⟩, ((prodEquiv hl fr).symm γ).2)
  left_inv x := by simp
  right_inv γ := Subtype.ext ((prodEquiv hl fr).apply_symm_apply γ)
  map_mul' x y := Subtype.ext (map_mul (prodEquiv hl fr) ((x.1 : LevelGroup D.host), x.2) ((y.1 : LevelGroup D.host), y.2))

variable {K : Type} [Field K]

def chiHR (fr : TypeFrame Dw l) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) K) : grpHR fr →* Kˣ :=
  (genChar ψ).comp ((typeRed fr).subgroupComap (levelU D.host))

theorem chiHR_apply (fr : TypeFrame Dw l) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) K) (h : grpHR fr) :
    ((chiHR fr ψ h : Kˣ) : K) = psiU ψ (typeRed fr h) := rfl

instance fintypeSubgroup {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (S : Subgroup (LevelAut Dw l)) : Fintype S := Fintype.ofFinite _

end Groups

end GlobalTheory.LevDesc
end
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevDesc

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.AllWt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)

section Action

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : FrPt Xo c S :=
  mvPt (K := c.F) (fun S _ _ => FrPt Xo c S)
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : LevelAut Dw l) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (levFull Dw l) g y y') γ y

def transl (γ : LevelAut Dw l) : Rul Xo c →ₐ[c.F] Rul Xo c where
  toFun f := fun p y => f p (move Xo c γ y)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def pull (h : LevelAut Dw l) : Rul Xo c →ₐ[c.F] Rul Xo c := transl Xo c h⁻¹

def secRing : Subalgebra c.F (Rul Xo c) :=
  (⨆ e, secZ Xo c e).toSubalgebra (Submodule.mem_iSup_of_mem 0 one_mem_secZ) fun x y hx hy => by
    have h : (⨆ e, secZ Xo c e) * (⨆ e, secZ Xo c e) ≤ ⨆ e, secZ Xo c e := by
      rw [Submodule.iSup_mul]
      refine iSup_le fun e => ?_
      rw [Submodule.mul_iSup]
      exact iSup_le fun e' => (secZ_mul_le Xo c e e').trans (le_iSup (secZ Xo c) (e + e'))
    exact h (Submodule.mul_mem_mul hx hy)

variable {Xo c}

theorem transl_apply (γ : LevelAut Dw l) (f : Rul Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    transl Xo c γ f p y = f p (move Xo c γ y) := rfl

theorem pull_apply (h : LevelAut Dw l) (f : Rul Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    pull Xo c h f p y = f p (move Xo c h⁻¹ y) := rfl

theorem pull_inv (g : LevelAut Dw l) : pull Xo c g⁻¹ = transl Xo c g := by rw [pull, inv_inv]

theorem mem_secRing {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) : f ∈ secRing Xo c :=
  Submodule.mem_iSup_of_mem e hf

theorem toSubmodule_secRing : Subalgebra.toSubmodule (secRing Xo c) = ⨆ e, secZ Xo c e := rfl

theorem prod_mem_secZ {ι : Type} (s : Finset ι) {e : Ix Dw → ℤ} {f : ι → Rul Xo c} (hf : ∀ i, f i ∈ secZ Xo c e) :
    ∏ i ∈ s, f i ∈ secZ Xo c (s.card • e) := by
  induction s using Finset.cons_induction with
  | empty => simpa using one_mem_secZ
  | cons a s ha ih => rw [Finset.prod_cons, Finset.card_cons, succ_nsmul']; exact mul_mem_secZ (hf a) ih

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
include hpq hA

theorem levR_move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    levR (levFull Dw l γ) y (move Xo c γ y) :=
  mvPt_spec (GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA).total γ y

theorem move_unique {γ : LevelAut Dw l} {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S}
    (h : levR (levFull Dw l γ) y y') : move Xo c γ y = y' :=
  have F := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) (move Xo c γ y)
  F.1 _ _ F.2.1 ((GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA).func γ S y _ _ (levR_move hpq hA γ y) h)

theorem move_one {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : move Xo c 1 y = y :=
  move_unique hpq hA ((GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA).one S y)

theorem move_mul (γ δ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    move Xo c (γ * δ) y = move Xo c δ (move Xo c γ y) :=
  move_unique hpq hA ((GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA).mul γ δ S y _ _
    (levR_move hpq hA γ y) (levR_move hpq hA δ _))

theorem transl_one (f : Rul Xo c) : transl Xo c 1 f = f := by
  funext p y; rw [transl_apply, move_one hpq hA]

theorem transl_mul (γ δ : LevelAut Dw l) (f : Rul Xo c) :
    transl Xo c (γ * δ) f = transl Xo c γ (transl Xo c δ f) := by
  funext p y; rw [transl_apply, move_mul hpq hA]; rfl

theorem isRightAct_pull : IsRightAct (pull Xo c) :=
  ⟨fun x => by rw [pull, inv_one, transl_one hpq hA], fun h h' x => by
    rw [pull, mul_inv_rev, transl_mul hpq hA]; rfl⟩

theorem transl_mem_secZ (γ : LevelAut Dw l) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    transl Xo c γ f ∈ secZ Xo c e :=
  have L := GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA
  ⟨fun p q φ y z h => hf.1 p q φ _ _ (L.nat γ p.R q.R φ y _ z _ h (levR_move hpq hA γ y) (levR_move hpq hA γ z)),
    fun p t y y' h => hf.2 p t _ _ (L.bor γ p.R t y _ y' _ h (levR_move hpq hA γ y) (levR_move hpq hA γ y'))⟩

theorem pull_mem_secZ (h : LevelAut Dw l) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    pull Xo c h f ∈ secZ Xo c e := transl_mem_secZ hpq hA _ hf

theorem pull_mem_secRing (h : LevelAut Dw l) {f : Rul Xo c} (hf : f ∈ secRing Xo c) : pull Xo c h f ∈ secRing Xo c := by
  have : (⨆ e, secZ Xo c e) ≤ (⨆ e, secZ Xo c e).comap (pull Xo c h).toLinearMap :=
    iSup_le fun e g hg => mem_secRing (pull_mem_secZ hpq hA h hg)
  exact this hf

variable (Xo c) in

def pullSec (h : LevelAut Dw l) : secRing Xo c →ₐ[c.F] secRing Xo c :=
  ((pull Xo c h).comp (secRing Xo c).val).codRestrict _ fun f => pull_mem_secRing hpq hA h f.2

theorem isRightAct_pullSec : IsRightAct (pullSec Xo c hpq hA) :=
  ⟨fun x => Subtype.ext ((isRightAct_pull (Xo := Xo) (c := c) hpq hA).1 x),
    fun h h' x => Subtype.ext ((isRightAct_pull (Xo := Xo) (c := c) hpq hA).2 h h' x)⟩

variable (Xo c) in

def pullSecEquiv (h : LevelAut Dw l) : secRing Xo c ≃ₐ[c.F] secRing Xo c := (isRightAct_pullSec hpq hA).equiv h

end Action

section Sub

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (S : Subgroup (LevelAut Dw l))

def pullOn (h : S) : Rul Xo c →ₐ[c.F] Rul Xo c := pull Xo c h

def pullSecOn (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (h : S) : secRing Xo c →ₐ[c.F] secRing Xo c :=
  pullSec Xo c hpq hA h

def levMat (u : Rul Xo c) : Matrix S S (Rul Xo c) := groupMat (pullOn Xo c S) u

open Classical in

def levDet (u : Rul Xo c) : Rul Xo c := (levMat Xo c S u).det

def levTr (χ : S →* (c.F)ˣ) : Rul Xo c →ₗ[c.F] Rul Xo c := tr (pullOn Xo c S) χ

def levPh (χ : S →* (c.F)ˣ) (u : Rul Xo c) : Rul Xo c →ₗ[c.F] (S → Rul Xo c) := ph (pullOn Xo c S) χ u

def levEigen (χ : S →* (c.F)ˣ) : Submodule c.F (Rul Xo c) := eigen (pullOn Xo c S) χ

variable {Xo c S}

theorem levMat_apply (u : Rul Xo c) (h g : S) : levMat Xo c S u h g = pull Xo c (h * g) u := rfl

theorem levTr_apply (χ : S →* (c.F)ˣ) (F : Rul Xo c) :
    levTr Xo c S χ F = ∑ h : S, (((χ h)⁻¹ : (c.F)ˣ) : c.F) • pull Xo c h F := tr_apply _ χ F

theorem levPh_apply (χ : S →* (c.F)ˣ) (u f : Rul Xo c) (h : S) :
    levPh Xo c S χ u f h = levTr Xo c S χ (f * pull Xo c h u) := rfl

theorem mem_levEigen {χ : S →* (c.F)ˣ} {F : Rul Xo c} :
    F ∈ levEigen Xo c S χ ↔ ∀ h : S, pull Xo c h F = ((χ h : (c.F)ˣ) : c.F) • F := Iff.rfl

theorem mem_levEigen_iff_transl {χ : S →* (c.F)ˣ} {F : Rul Xo c} :
    F ∈ levEigen Xo c S χ ↔ ∀ g : S, transl Xo c g F = (((χ g)⁻¹ : (c.F)ˣ) : c.F) • F :=
  ⟨fun h g => by rw [← pull_inv, ← map_inv]; exact h g⁻¹,
    fun h g => by have := h g⁻¹; rw [map_inv, inv_inv] at this; exact this⟩

section Laws

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
include hpq hA

theorem isRightAct_pullOn : IsRightAct (pullOn Xo c S) := (isRightAct_pull hpq hA).comp S.subtype

theorem isRightAct_pullSecOn : IsRightAct (pullSecOn Xo c S hpq hA) := (isRightAct_pullSec hpq hA).comp S.subtype

theorem coe_tr_pullSecOn (χ : S →* (c.F)ˣ) (F : secRing Xo c) :
    (tr (pullSecOn Xo c S hpq hA) χ F : Rul Xo c) = levTr Xo c S χ F := by
  rw [tr_apply, levTr_apply]
  exact map_sum (secRing Xo c).val _ _

theorem coe_det_pullSecOn [DecidableEq S] (u : secRing Xo c) :
    ((groupMat (pullSecOn Xo c S hpq hA) u).det : Rul Xo c) = levDet Xo c S u := by
  have h := (secRing Xo c).val.toRingHom.map_det (groupMat (pullSecOn Xo c S hpq hA) u)
  rw [levDet]
  convert h using 2 <;> rfl

theorem levDet_mem_secZ {e : Ix Dw → ℤ} {u : Rul Xo c} (hu : u ∈ secZ Xo c e) :
    levDet Xo c S u ∈ secZ Xo c (Nat.card S • e) := by
  classical
  rw [levDet, Matrix.det_apply, Nat.card_eq_fintype_card]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_secZ Finset.univ fun i => pull_mem_secZ hpq hA _ hu) _

theorem levTr_mem_levEigen (χ : S →* (c.F)ˣ) (F : Rul Xo c) : levTr Xo c S χ F ∈ levEigen Xo c S χ :=
  (isRightAct_pullOn hpq hA).tr_mem_eigen χ F

end Laws

example : levTr Xo c S 1 1 = (Fintype.card S : c.F) • (1 : Rul Xo c) :=
  tr_of_mem_eigen _ fun h => by simp

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (S)

def chiLat (χ : S →* (c.F)ˣ) : Submodule (𝓞 c.F) (cuspW Xo c U G) := latCap (latW U G) (levEigen Xo c S χ)

theorem mem_chiLat {χ : S →* (c.F)ˣ} {F : cuspW Xo c U G} : F ∈ chiLat S U G χ ↔
    F ∈ latW U G ∧ ∀ h : S, pull Xo c h (F : Rul Xo c) = ((χ h : (c.F)ˣ) : c.F) • (F : Rul Xo c) := Iff.rfl

example (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (χ : (⊥ : Subgroup (LevelAut Dw l)) →* (c.F)ˣ) :
    chiLat ⊥ U G χ = latW U G :=
  Submodule.ext fun F => (mem_chiLat ⊥ U G).trans (and_iff_left fun h => by
    obtain rfl : h = 1 := Subsingleton.elim _ _
    rw [map_one, Units.val_one, one_smul]
    exact (isRightAct_pull hpq hA).1 _)

def KeepsCusp : Prop := ∀ h : LevelAut Dw l, ∀ f ∈ cuspW Xo c U G, pull Xo c h f ∈ cuspW Xo c U G

def cuspRep (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (hC : KeepsCusp U G) :
    Representation c.F (LevelAut Dw l) (cuspW Xo c U G) :=
  (isRightAct_pull hpq hA).subRep _ hC

theorem coe_cuspRep (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (hC : KeepsCusp U G) (g : LevelAut Dw l)
    (f : cuspW Xo c U G) : (cuspRep U G hpq hA hC g f : Rul Xo c) = transl Xo c g f :=
  DFunLike.congr_fun (pull_inv (Xo := Xo) (c := c) g) (f : Rul Xo c)

variable {U G}

def cuspPh {G' : WTZ E} (χ : S →* (c.F)ˣ) (u : Rul Xo c)
    (hm : ∀ f ∈ cuspW Xo c U G', ∀ h, levPh Xo c S χ u f h ∈ cuspW Xo c U G) :
    cuspW Xo c U G' →ₗ[c.F] (S → cuspW Xo c U G) :=
  LinearMap.pi fun h => (LinearMap.proj h ∘ₗ levPh Xo c S χ u).restrict fun f hf => hm f hf h

theorem coe_cuspPh {G' : WTZ E} (χ : S →* (c.F)ˣ) (u : Rul Xo c)
    (hm : ∀ f ∈ cuspW Xo c U G', ∀ h, levPh Xo c S χ u f h ∈ cuspW Xo c U G) (f : cuspW Xo c U G') (h : S) :
    (cuspPh S χ u hm f h : Rul Xo c) = levPh Xo c S χ u f h := rfl

end Sub

section Types

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

theorem IsTypeLevel.coprime (hl : IsTypeLevel l) : l.A.Coprime l.M := by
  rw [hl.1]; exact Nat.coprime_one_left _

variable (Xo c) in

def pullType (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (g : LevelGroup D.host) : Rul Xo c →ₐ[c.F] Rul Xo c :=
  pull Xo c (typeEmb hl fr g)

variable (Xo c) in

def typeOp (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (e : MonoidAlgebra c.F (LevelGroup D.host)) :
    Module.End c.F (Rul Xo c) :=
  algOp (pullType Xo c hl fr) e

variable (hl : IsTypeLevel l) (fr : TypeFrame Dw l)

theorem isRightAct_pullType (hpq : 1 ≤ Dw.p + Dw.q) : IsRightAct (pullType Xo c hl fr) :=
  (isRightAct_pull hpq hl.coprime).comp (typeEmb hl fr)



variable (Xo c) in

def goodOp (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* (c.F)ˣ) (j : Fin D.R.m) : Module.End c.F (Rul Xo c) :=
  typeOp Xo c hl fr (goodIdemTw om j)

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ D.host.E)
  (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) c.F)

def latN : Submodule (𝓞 c.F) (cuspW Xo c U G) := chiLat (grpHR fr) U G (chiHR fr ψ)

def latCut (e : MonoidAlgebra c.F (LevelGroup D.host)) : Submodule (𝓞 c.F) (cuspW Xo c U G) :=
  cutLat (latN fr U G ψ) (typeOp Xo c hl fr e)

variable (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* (c.F)ˣ) (j : Fin D.R.m)

def latGood : Submodule (𝓞 c.F) (cuspW Xo c U G) := cutLat (latN fr U G ψ) (goodOp Xo c hl fr om j)

def latBad : Submodule (𝓞 c.F) (cuspW Xo c U G) := cutLat (latN fr U G ψ) (1 - goodOp Xo c hl fr om j)

example (hpq : 1 ≤ Dw.p + Dw.q) : latCut hl fr U G ψ 1 = latN fr U G ψ := by
  rw [latCut, typeOp, (isRightAct_pullType hl fr hpq).algOp_eq, map_one, cutLat_one]

end Types

section Adelic

open Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue (stabLat prinLev)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (V : HSp D)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))

def ReducesTo (k : GA D V) (γ : LevelAut Dw l) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
    finVec V (ι (liftLa γ a)) - (finHom V k).1.mulVec (finVec V (ι a)) = l.M • w

def IsReduction (red : stabLat V →* LevelAut Dw l) : Prop :=
  Function.Surjective red ∧ (∀ k : stabLat V, red k = 1 ↔ (k : GA D V) ∈ prinLev V l.M) ∧
    ∀ k : stabLat V, ReducesTo V ι k (red k)

variable {V ι}

abbrev levelOver (red : stabLat V →* LevelAut Dw l) (S : Subgroup (LevelAut Dw l)) : Subgroup (stabLat V) := S.comap red

theorem IsReduction.mem_ker {red : stabLat V →* LevelAut Dw l} (h : IsReduction V ι red) (k : stabLat V) :
    k ∈ red.ker ↔ (k : GA D V) ∈ prinLev V l.M := h.2.1 k

end Adelic

end GlobalTheory.LevDesc
end
end
