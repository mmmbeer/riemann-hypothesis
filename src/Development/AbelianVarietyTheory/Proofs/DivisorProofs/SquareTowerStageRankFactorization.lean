import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageExtensionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSuccessorCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
import BuildAid.ForwardExisting

section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.HeckeUnifApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Inf

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def swapL : (InfiniteAdeleRing F ⊗[F] E) →ₗ[InfiniteAdeleRing F] (E ⊗[F] InfiniteAdeleRing F) where
  toFun := Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

def swapR : (E ⊗[F] InfiniteAdeleRing F) →ₗ[InfiniteAdeleRing F] (InfiniteAdeleRing F ⊗[F] E) where
  toFun := Algebra.TensorProduct.comm F E (InfiniteAdeleRing F)
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

theorem exists_infinite_equiv :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  letI tB : TopologicalSpace (E ⊗[F] InfiniteAdeleRing F) := moduleTopology (InfiniteAdeleRing F) _
  haveI : IsModuleTopology (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F) := ⟨rfl⟩
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have hL : Continuous (swapL (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  have hR : Continuous (swapR (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  let h := GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph (K := F) (L := E)
  refine ⟨(Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E).toRingEquiv.trans
    (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)).toRingEquiv, ?_, ?_, ?_⟩
  · exact h.continuous.comp hL
  · exact hR.comp h.symm.continuous
  · intro x
    change GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x)) = _
    rw [Algebra.TensorProduct.comm_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one,
      mul_one]

end Inf

open GlobalTheory.LFun in

theorem exists_tensor_adele_equiv :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv (F := F) (E := E)
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc,
    hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

open GlobalTheory.LFun in

theorem exists_hchar (χ : (AF F ⊗[F] E)ˣ →* Circle) (hχ : IsHecke F E χ) :
    ∃ (H : Formalism.L2.Host.HChar E) (u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ),
      (∀ y, H.1 y = Circle.toUnits (χ (u y))) ∧ Function.Surjective u ∧
      ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x := by
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv (F := F) (E := E)
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, u, fun y => rfl, fun g => ⟨Units.map Φ.toRingHom.toMonoidHom g, Units.ext (Φ.symm_apply_apply _)⟩,
    fun W x => ?_⟩
  change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
  rw [hloc]

theorem eq_one_of_unif_cofinite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), GlobalTheory.LFun.IsHecke F E χ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ → χ (GlobalTheory.LFun.locIdele F w ϖ) = 1) → χ = 1 := by
  intro F E _ _ _ _ _ χ hχ hev
  obtain ⟨H, u, hH, hsurj, hloc⟩ := exists_hchar χ hχ
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ →
      χ (GlobalTheory.LFun.locIdele F w ϖ) = 1}.Finite := Filter.eventually_cofinite.1 hev
  have h1 : H.1 = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away H.1 H.2.1 H.2.2 hfin.toFinset fun v hv x => ?_
    have hv' : ∀ ϖ, Formalism.L2.Host.IsUnifAt v ϖ → χ (GlobalTheory.LFun.locIdele F v ϖ) = 1 := by
      simpa using hv
    refine GlobalTheory.FrobDense.eq_one_of_unif (H.1.comp (Neutral.B1.localIdele E v)) (fun y hy => ?_) x
    change H.loc v y = 1
    rw [hloc, GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, hv' y hy, map_one]
  ext g
  obtain ⟨y, rfl⟩ := hsurj g
  have h2 : Circle.toUnits (χ (u y)) = 1 := (hH y).symm.trans (congrFun (congrArg DFunLike.coe h1) y)
  have h3 : ((χ (u y) : Circle) : ℂ) = 1 := by
    have := congrArg (fun z : ℂˣ => (z : ℂ)) h2
    simpa using this
  simpa using h3

end GlobalTheory.HeckeUnifApprox
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

namespace GlobalTheory.AdaptedPlaneIdeal

theorem count_eq_zero_of_val {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (h1 : ∀ s ∈ I, w.valuation E s ≤ 1)
    (h2 : ∃ s ∈ I, w.valuation E s = 1) : FractionalIdeal.count E w I = 0 := by
  obtain ⟨s₀, hs₀, hv₀⟩ := h2
  have hs0 : s₀ ≠ 0 := by rintro rfl; simp at hv₀
  apply le_antisymm
  · have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ s₀ ≤ I :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hs₀
    have := FractionalIdeal.count_mono E w ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hs0) hle
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton E w hs0, hv₀] at this
    simpa using this
  · obtain ⟨a, ha, hint⟩ := I.isFractional
    have ha0 : (a : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero ha
    set k := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(a : 𝓞 E)})).factors with hk
    have hspan : Ideal.span {(a : 𝓞 E)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]; exact ha0
    have hva : w.valuation E (algebraMap (𝓞 E) E a) = WithZero.exp (-(k : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha0]
    have hle : ((Ideal.span {(a : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I ≤
        ((w.asIdeal ^ k : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
      intro z hz
      rw [FractionalIdeal.coeIdeal_span_singleton] at hz
      obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hz
      obtain ⟨r, hr⟩ := hint s hs
      rw [Algebra.smul_def] at hr
      refine (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, hr⟩
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
      change w.valuation E (algebraMap (𝓞 E) E r) ≤ _
      rw [hr, map_mul, hva]
      exact mul_le_of_le_one_right' (h1 s hs)
    have hne : ((Ideal.span {(a : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I ≠ 0 :=
      mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hspan) hI
    have := FractionalIdeal.count_mono E w hne hle
    rw [FractionalIdeal.count_mul E w (FractionalIdeal.coeIdeal_ne_zero.2 hspan) hI, FractionalIdeal.count_coe E w hspan,
      FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow_self] at this
    omega

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    form σ J (a + b) y = form σ J a y + form σ J b y := by simp [form, add_dotProduct]

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a y : Fin n → E) :
    form σ J (s • a) y = s * form σ J a y := by simp [form, smul_dotProduct]

theorem form_swap {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_conj_conj h, Finset.mul_sum, hJ]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_ne_zero_of_hasSig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (φ : E →+* ℂ)
    (h : HasSig (J.map φ) r s) : J.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  intro h0
  have hM : (J.map φ).det = 0 := by
    have := RingHom.map_det φ J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hD : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hD
  rw [← hA] at h1
  have h2 : (Aᵀ * J.map φ * A.map star).rank ≤ (J.map φ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have h3 := LinearMap.finrank_range_add_finrank_ker (J.map φ).mulVecLin
  have h4 : 0 < Module.finrank ℂ (LinearMap.ker (J.map φ).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun e => hv0 (congrArg Subtype.val e)⟩
  rw [Module.finrank_fin_fun] at h3
  have h5 : (J.map φ).rank = Module.finrank ℂ (LinearMap.range (J.map φ).mulVecLin) := rfl
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
  omega

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

theorem apply_mem_splitLat (τ : E →ₐ[F] Fv F v) {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun i => by simp [splitVec]⟩

theorem val_le_one (τ : E →ₐ[F] Fv F v) {x₀ : Fin n → E}
    (hB : ∀ c : Fv F v, (c • fun i => τ (x₀ i)) ∈ splitLat τ L → c ∈ v.adicCompletionIntegers F)
    {s : E} (hs : s • x₀ ∈ L) : (splitPrime τ).valuation E s ≤ 1 := by
  rw [← valued_apply_eq_valuation]
  have := hB (τ s) (by
    have := apply_mem_splitLat τ hs
    convert this using 1
    funext i
    simp [map_mul])
  exact this

theorem exists_val_eq_one {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (τ : E →ₐ[F] Fv F v)
    {x₀ y₀ : Fin n → E} (hA : (fun i => τ (x₀ i)) ∈ splitLat τ L)
    (hB : ∀ c : Fv F v, (c • fun i => τ (x₀ i)) ∈ splitLat τ L → c ∈ v.adicCompletionIntegers F)
    (hxy : form σ J x₀ y₀ = 1) (hC : ∀ l ∈ L, form σ J l y₀ • x₀ ∈ L) :
    ∃ s, s • x₀ ∈ L ∧ (splitPrime τ).valuation E s = 1 := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ l ∈ L, Valued.v (τ (form σ J l y₀)) < 1 := fun l hl => by
    rw [valued_apply_eq_valuation]
    exact lt_of_le_of_ne (val_le_one τ hB (hC l hl)) (hcon _ (hC l hl))
  let φ : (Fin n → Fv F v) → Fv F v := fun u => u ⬝ᵥ (J.map τ *ᵥ fun j => τ (σ (y₀ j)))
  have hφ : ∀ l : Fin n → E, φ (fun i => τ (l i)) = τ (form σ J l y₀) := fun l => by
    simp [φ, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  have key : ∀ z ∈ latLoc F L v, Valued.v (φ (splitVec τ z)) < 1 := fun z hz => by
    refine latLoc_induction (p := fun z => Valued.v (φ (splitVec τ z)) < 1) (fun a ha l hl => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · have e : splitVec τ (fun i => a ⊗ₜ[F] l i) = a • fun i => τ (l i) := funext fun i => by simp [splitVec]
      rw [e, show φ (a • fun i => τ (l i)) = a * φ (fun i => τ (l i)) from smul_dotProduct _ _ _, hφ, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) (hlt l hl)
    · have e : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => by simp [splitVec]
      rw [e]; simp [φ]
    · rw [splitVec_add, show φ (splitVec τ y + splitVec τ z) = φ (splitVec τ y) + φ (splitVec τ z) from
        add_dotProduct _ _ _]
      exact Valuation.map_add_lt _ hy hz
    · have e : splitVec τ (-y) = -splitVec τ y := funext fun i => by simp [splitVec]
      rw [e, show φ (-splitVec τ y) = -φ (splitVec τ y) from neg_dotProduct _ _, Valuation.map_neg]
      exact hy
  obtain ⟨z, hz, hze⟩ := hA
  have := key z hz
  rw [hze, hφ, hxy, map_one, map_one] at this
  exact lt_irrefl _ this

end Split

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

theorem col_facts (τ : E →ₐ[F] Fv F v) {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (j : Fin n)
    {x₀ : Fin n → E} (hcol : ∀ r, β.1 r j = τ (x₀ r)) :
    (fun r => τ (x₀ r)) ∈ splitLat τ L ∧
      ∀ c : Fv F v, (c • fun r => τ (x₀ r)) ∈ splitLat τ L → c ∈ v.adicCompletionIntegers F := by
  have e : ∀ c : Fv F v, β.1 *ᵥ Pi.single j c = c • fun r => τ (x₀ r) := fun c => by
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol, mul_comm]
  refine ⟨?_, fun c hc => ?_⟩
  · have := (hβ (Pi.single j 1)).1 (fun i => by
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _])
    rwa [e, one_smul] at this
  · have := (hβ (Pi.single j c)).2 (by rwa [e]) j
    simpa using this

theorem pair_apply (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) (z' z : Fin n → E) :
    (fun i => (τ.comp σ) (z' i)) ⬝ᵥ Jᵀ.map τ *ᵥ (fun i => τ (z i)) = τ (form σ J z z') := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul,
    AlgHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Split

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) :
    hE σ Jᵀ x z = form σ J z x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

theorem ideal_ne_zero_and_count_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH hi₀ hi₁
  have h := hB.cm
  have hyx : form σ Y.J H.y H.x = 1 := by rw [form_swap h hY.herm, hH.xy, map_one]
  have hCx : ∀ l ∈ Y.L, form σ Y.J l H.y • H.x ∈ Y.L := by
    intro l hl
    obtain ⟨a, t, u, ha, -, -, rfl⟩ := hH.split l hl
    have e : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.y = a := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xy, hH.yy, (hH.orth u).2]; ring
    rw [e]; exact ha
  have hCy : ∀ l ∈ Y.L, form σ Y.J l H.x • H.y ∈ Y.L := by
    intro l hl
    obtain ⟨a, t, u, -, ht, -, rfl⟩ := hH.split l hl
    have e : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.x = t := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, hyx, (hH.orth u).1]; ring
    rw [e]; exact ht
  have hne : H.𝔟 ≠ 0 := by
    have hx : H.x ∈ Submodule.span E (Y.L : Set (Fin n → E)) := hY.lat.span_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E (Y.L : Set (Fin n → E)) H.x hx
    rw [Submodule.span_eq] at ht
    have hmem : algebraMap (𝓞 E) E t ∈ H.𝔟 := (hH.ideal _).2 (by rw [algebraMap_smul]; exact ht)
    intro h0
    rw [h0, FractionalIdeal.mem_zero_iff] at hmem
    exact nonZeroDivisors.coe_ne_zero t ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 hmem)
  refine ⟨hne, fun w hw => ?_⟩
  set v := w.under (𝓞 F) with hv
  let v' : B.P := ⟨v, hw⟩
  set τ := B.τ v' with hτ
  have hmem : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split h τ] at hmem
  have hbas : IsSplitBasis τ Y.L (Y.bas v) := hY.bas v'
  obtain ⟨hAx, hBx⟩ := col_facts τ hbas ⟨i₀, hi₀⟩ (x₀ := H.x) ((hH.bas v' ⟨i₀, hi₀⟩).1 rfl)
  obtain ⟨hAy, hBy⟩ := col_facts τ hbas ⟨i₁, hi₁⟩ (x₀ := H.y) ((hH.bas v' ⟨i₁, hi₁⟩).2.1 rfl)
  rcases hmem with e | e
  · have hw' : w = splitPrime τ := HeightOneSpectrum.ext e
    rw [hw']
    refine count_eq_zero_of_val _ hne (fun s hs => val_le_one τ hBx ((hH.ideal s).1 hs)) ?_
    obtain ⟨s, hs, hv1⟩ := exists_val_eq_one τ hAx hBx hH.xy hCx
    exact ⟨s, (hH.ideal s).2 hs, hv1⟩
  · have hw' : w = splitPrime (τ.comp σ) := HeightOneSpectrum.ext e
    rw [hw']
    obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hND : IsHermND σ Y.Jᵀ :=
      ⟨fun i j => by simpa [Matrix.transpose_apply] using hY.herm j i,
        by rw [Matrix.det_transpose]; exact det_ne_zero_of_hasSig _ (hY.sig w₀)⟩
    have hSD : IsSelfDualAt σ Y.Jᵀ Y.L v := by
      refine (SelfDual.forall_isSelfDualAt_iff (σ := σ) hND.2 hY.lat).2 (fun z => (hY.dual z).trans ?_) v
      simp only [hE_transpose]
      exact forall₂_congr fun x _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩
    have hint : ∀ l ∈ Y.L, τ (form σ Y.J l H.x) ∈ v.adicCompletionIntegers F := fun l hl => by
      have := val_le_one τ hBy (hCy l hl)
      rw [← valued_apply_eq_valuation] at this
      exact this
    have hA' : (fun i => (τ.comp σ) (H.x i)) ∈ splitLat (τ.comp σ) Y.L := by
      rw [mem_splitLat_comp_iff h hND hSD]
      rintro _ ⟨z, hz, rfl⟩
      refine latLoc_induction (p := fun z => (fun i => (τ.comp σ) (H.x i)) ⬝ᵥ Y.Jᵀ.map τ *ᵥ splitVec τ z ∈
        v.adicCompletionIntegers F) (fun a ha l hl => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hz
      · have e1 : splitVec τ (fun i => a ⊗ₜ[F] l i) = a • fun i => τ (l i) := funext fun i => by simp [splitVec]
        rw [e1, Matrix.mulVec_smul, dotProduct_smul, pair_apply, smul_eq_mul]
        exact mul_mem ha (hint l hl)
      · have e1 : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => by simp [splitVec]
        rw [e1]; simp
      · rw [splitVec_add, Matrix.mulVec_add, dotProduct_add]; exact add_mem hy hz
      · have e1 : splitVec τ (-y) = -splitVec τ y := funext fun i => by simp [splitVec]
        rw [e1, Matrix.mulVec_neg, dotProduct_neg]; exact neg_mem hy
    have hB' : ∀ c : Fv F v, (c • fun i => (τ.comp σ) (H.x i)) ∈ splitLat (τ.comp σ) Y.L →
        c ∈ v.adicCompletionIntegers F := fun c hc => by
      have := (mem_splitLat_comp_iff h hND hSD).1 hc _ hAy
      rwa [smul_dotProduct, pair_apply, hyx, map_one, smul_eq_mul, mul_one] at this
    refine count_eq_zero_of_val _ hne (fun s hs => val_le_one (τ.comp σ) hB' ((hH.ideal s).1 hs)) ?_
    obtain ⟨s, hs, hv1⟩ := exists_val_eq_one (τ.comp σ) hA' hB' hH.xy hCx
    exact ⟨s, (hH.ideal s).2 hs, hv1⟩

end GlobalTheory.AdaptedPlaneIdeal
end
end

section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_hermitian_ideal_coprime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  first | exact @GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero | exact GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero | (intros; apply GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors

namespace GlobalTheory.CodiffValPrimeW

theorem valuation_le_one_of_mem_codiff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P →
    ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 := by
  intro F E _ _ _ _ _ σ B hB w hw c hc

  have hF : ¬ differentIdeal ℤ (𝓞 F) ≤ (w.under (𝓞 F)).asIdeal :=
    GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std _ (hB.psiP _ hw)

  have hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI := hB.unram
    infer_instance
  have hE : ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal := by
    rw [GlobalTheory.SnMass.SkewVol.differentIdeal_eq_map_of_unramified hu]
    intro h
    exact hF (Ideal.map_le_iff_le_comap.1 h)
  obtain ⟨d, hdD, hdw⟩ := Set.not_subset.1 hE

  have hcd : c ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hc o)
    refine ⟨n, ?_⟩
    rw [hn, Algebra.traceForm_apply, mul_comm]

  have h1 : c * (d : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))
    have hmul := FractionalIdeal.mul_mem_mul hcd
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hdD, rfl⟩ :
        (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))
    rwa [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), mul_inv_cancel₀ hne] at hmul
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hvx : w.valuation E (c * (d : E)) ≤ 1 := by
    rw [← hx]
    exact w.valuation_le_one x
  have hvd : w.valuation E (d : E) = 1 :=
    le_antisymm (w.valuation_le_one d) (not_lt.1 fun h => hdw ((w.valuation_lt_one_iff_mem d).1 h))
  rw [map_mul, hvd, mul_one] at hvx
  exact hvx

end GlobalTheory.CodiffValPrimeW
end

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_one_of_integral_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 := by
  atlas_forward_decl GlobalTheory.CodiffValPrimeW.valuation_le_one_of_mem_codiff
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_unit_at_prime_mul_integral (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K) (hd : d ≠ 0)
    (hdT : ∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) (hPT : ∀ t ∈ T, P.valuation K t ≤ 1) :
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  have hspan : Ideal.span {d} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  have hirr : Irreducible P.asIdeal := (Ideal.prime_of_isPrime P.ne_bot P.isPrime).irreducible
  obtain ⟨a, J, hPJ, hdJ⟩ := WfDvdMonoid.max_power_factor hspan hirr
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  have hsJ' : J ∣ Ideal.span {s} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)
  have hvPs : P.valuation K (s : K) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (P.intValuation_le_one s) (not_lt.mp fun h => hsP ?_)
    rw [HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton] at h
    exact h

  have hQ : ∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.intValuation s ≤ Q.intValuation d := by
    intro Q hQP
    have hQd : Q.intValuation d = WithZero.exp (-((Associates.mk Q.asIdeal).count
        (Associates.mk (Ideal.span {d})).factors : ℤ)) := by
      rw [HeightOneSpectrum.intValuation_def, if_neg hd]
    set n := (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {d})).factors
    have hdiv : Q.asIdeal ^ n ∣ Ideal.span {d} :=
      (Q.intValuation_le_pow_iff_dvd d n).mp (le_of_eq hQd)
    have hne : Q.asIdeal ≠ P.asIdeal := fun h => hQP (HeightOneSpectrum.ext h)
    have hcop : IsCoprime Q.asIdeal P.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne Q.isMaximal P.isMaximal hne)
    have hcopn : IsCoprime (Q.asIdeal ^ n) (P.asIdeal ^ a) := hcop.pow
    rw [hdJ] at hdiv
    have hQJ : Q.asIdeal ^ n ∣ J := hcopn.dvd_of_dvd_mul_left hdiv
    rw [hQd]
    exact (Q.intValuation_le_pow_iff_dvd s n).mpr (hQJ.trans hsJ')
  refine ⟨s, hvPs, fun t ht => ?_⟩
  have hdt : (d : K) * t ∈ (algebraMap (𝓞 K) K).range := ⟨⟨_, hdT t ht⟩, rfl⟩
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((s : K) * t) (by
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      rw [map_mul, hvPs, one_mul]; exact hPT t ht
    · obtain ⟨z, hz⟩ := hdt
      have h1 : Q.valuation K ((d : K) * t) ≤ 1 := by
        rw [← hz]; exact Q.valuation_le_one z
      rw [map_mul] at h1 ⊢
      calc Q.valuation K (s : K) * Q.valuation K t ≤ Q.valuation K (d : K) * Q.valuation K t := by
            gcongr
            rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
            exact hQ Q hQP
        _ ≤ 1 := h1)
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

end GlobalTheory
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_denominator_integral : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) → ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  atlas_forward_decl GlobalTheory.exists_unit_at_prime_mul_integral
end

section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SkewPlaneIdeal

theorem codiff_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P →
    ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 :=
  GlobalTheory.T.valuation_le_one_of_integral_trace

theorem exists_unit_mul_integral : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) →
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) :=
  GlobalTheory.T.exists_unit_denominator_integral

theorem exists_valued_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : Fin n → E)
    (S : Set E), (0 : E) ∈ S → (∀ z ∈ L, z ⬝ᵥ c ∈ S) → ∀ u ∈ splitLat τ L,
    ∃ s ∈ S, Valued.v (u ⬝ᵥ fun i => τ (c i)) ≤ Valued.v (τ s) := by
  intro F E _ _ _ _ _ v τ n L c S h0 hS u hu
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => ∃ s ∈ S, Valued.v (splitVec τ y ⬝ᵥ fun i => τ (c i)) ≤ Valued.v (τ s))
    ?_ ?_ ?_ ?_ hy
  · intro a ha z hz
    refine ⟨z ⬝ᵥ c, hS z hz, ?_⟩
    have e : (splitVec τ fun i => a ⊗ₜ[F] z i) ⬝ᵥ (fun i => τ (c i)) = a * τ (z ⬝ᵥ c) := by
      simp [splitVec, dotProduct, map_sum, Finset.mul_sum, mul_assoc]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha)
  · refine ⟨0, h0, ?_⟩
    have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => map_zero _
    rw [this, zero_dotProduct, map_zero]
    exact zero_le
  · rintro y z ⟨s1, hs1, h1⟩ ⟨s2, hs2, h2⟩
    rw [splitVec_add, add_dotProduct]
    rcases le_total (Valued.v (τ s1)) (Valued.v (τ s2)) with h | h
    · exact ⟨s2, hs2, (Valuation.map_add _ _ _).trans (max_le (h1.trans h) h2)⟩
    · exact ⟨s1, hs1, (Valuation.map_add _ _ _).trans (max_le h1 (h2.trans h))⟩
  · rintro y ⟨s1, hs1, h1⟩
    refine ⟨s1, hs1, ?_⟩
    have : splitVec τ (-y) = -splitVec τ y := funext fun i => map_neg _ _
    rw [this, neg_dotProduct, Valuation.map_neg]
    exact h1

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)),
    L.FG → ∀ c : Fin n → E, ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ z ∈ L, IsIntegral ℤ ((d : E) * (z ⬝ᵥ c)) := by
  intro E _ _ n L hL c
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => z ⬝ᵥ c
      map_add' := fun a b => add_dotProduct a b c
      map_smul' := fun o a => by simp [smul_dotProduct] }
  obtain ⟨a, ha, hint⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 E)⁰) (P := E) (hL.map f)
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun z hz => ?_⟩
  obtain ⟨b, hb⟩ := hint _ (Submodule.mem_map_of_mem hz)
  rw [Algebra.smul_def] at hb
  have e : (a : E) * (z ⬝ᵥ c) = (b : E) := hb.symm
  rw [e]
  exact RingOfIntegers.isIntegral_coe b

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := add_dotProduct _ _ _

lemma form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a c : Fin n → E) :
    form σ J (t • a) c = t * form σ J a c := smul_dotProduct _ _ _

lemma form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  have e : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + fun i => σ (c i) := funext fun i => map_add σ _ _
  simp only [form, e, Matrix.mulVec_add, dotProduct_add]

lemma form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a b : Fin n → E) :
    form σ J a (t • b) = σ t * form σ J a b := by
  have e : (fun i => σ ((t • b) i)) = σ t • fun i => σ (b i) := funext fun i => by simp
  simp only [form, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma form_swap (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

lemma map_dotProduct {K : Type} [Field K] [Algebra F K] (τ : E →ₐ[F] K) {n : ℕ} (a c : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (fun i => τ (c i)) = τ (a ⬝ᵥ c) := by
  simp [dotProduct, map_sum, map_mul]

theorem count_eq_zero_of_valuation {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (h1 : ∀ s ∈ I, w.valuation K s ≤ 1) (h2 : ∃ s ∈ I, 1 ≤ w.valuation K s) :
    FractionalIdeal.count K w I = 0 := by
  obtain ⟨y, hy, hvy⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI w
  obtain ⟨s, hs, hvs⟩ := h2
  have a := h1 y hy
  have b := (GlobalTheory.Idele.mem_iff_valuation_le hI s).1 hs w
  rw [hvy, ← WithZero.exp_zero, WithZero.exp_le_exp] at a
  have c := hvs.trans b
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at c
  omega

lemma mem_splitLat_of_mem {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) : (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun i => by simp [splitVec]⟩

lemma col_prim {v : HeightOneSpectrum (𝓞 F)} {τ : E →ₐ[F] Fv F v} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (j : Fin n) (z : Fin n → E) (hz : ∀ r, β.1 r j = τ (z r)) :
    (fun r => τ (z r)) ∈ splitLat τ L ∧ ∀ t : Fv F v, (fun r => t * τ (z r)) ∈ splitLat τ L → Valued.v t ≤ 1 := by
  classical
  have hcol : β.1 *ᵥ Pi.single j 1 = fun r => τ (z r) := by
    rw [Matrix.mulVec_single_one]; funext r; exact hz r
  refine ⟨hcol ▸ (hβ _).1 fun i => ?_, fun t ht => ?_⟩
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e : β.1 *ᵥ (t • Pi.single j 1) = fun r => t * τ (z r) := by
      rw [Matrix.mulVec_smul, hcol]; rfl
    have := (hβ _).2 (e ▸ ht) j
    simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using this

theorem skewPlaneIdeal_ne_zero_and_count_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsSkew σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH hi₀ hi₁
  have hσ : ∀ z, σ (σ z) = z := cm_conj_conj hB.cm
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap σ hσ Y.J hY.skew, hH.xy, map_one]
  have hxι : ∀ u, form σ Y.J H.x (H.ι *ᵥ u) = 0 := fun u => by
    rw [form_swap σ hσ Y.J hY.skew, (hH.orth u).1, map_zero, neg_zero]

  have hco : ∀ z ∈ Y.L, form σ Y.J z H.y • H.x ∈ Y.L ∧ (-form σ Y.J z H.x) • H.y ∈ Y.L ∧
      ∀ a : E, form σ Y.J (a • H.x) z = a * σ (-form σ Y.J z H.x) := by
    intro z hz
    obtain ⟨a, t, u, ha, ht, _, rfl⟩ := hH.split z hz
    have e1 : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.y = a := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xy, hH.yy, (hH.orth u).2]; ring
    have e2 : -form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.x = t := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, hyx, (hH.orth u).1]; ring
    refine ⟨by rw [e1]; exact ha, by rw [e2]; exact ht, fun b => ?_⟩
    rw [e2, form_smul_left, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx, hH.xy, hxι]
    ring

  have h0 : H.𝔟 ≠ 0 := by
    intro h0
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun z => form σ Y.J z H.y
        map_add' := fun a b => form_add_left σ Y.J a b H.y
        map_smul' := fun t a => form_smul_left σ Y.J t a H.y }
    have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro z hz
      have := (hH.ideal _).2 (hco z hz).1
      rw [h0] at this
      exact (FractionalIdeal.mem_zero_iff _).1 this
    haveI := hY.lat
    rw [Submodule.IsLattice.span_eq_top] at hle
    have : f H.x = 0 := hle Submodule.mem_top
    change form σ Y.J H.x H.y = 0 at this
    rw [hH.xy] at this
    exact one_ne_zero this
  refine ⟨h0, fun w hw => ?_⟩
  set v : B.P := ⟨w.under (𝓞 F), hw⟩ with hv
  set τ := B.τ v with hτ
  have hβ := hY.bas v
  obtain ⟨hxL, hxp⟩ := col_prim hβ ⟨i₀, hi₀⟩ H.x fun r => (hH.bas v ⟨i₀, hi₀⟩).1 rfl r
  obtain ⟨hyL, hyp⟩ := col_prim hβ ⟨i₁, hi₁⟩ H.y fun r => (hH.bas v ⟨i₁, hi₁⟩).2.1 rfl r
  have hτs : ∀ a : E, ∀ z : Fin n → E, (fun i => τ ((a • z) i)) = fun i => τ a * τ (z i) := fun a z =>
    funext fun i => by simp

  have hxw : ∀ a : E, a • H.x ∈ Y.L → Valued.v (τ a) ≤ 1 := fun a ha =>
    hxp _ (hτs a H.x ▸ mem_splitLat_of_mem τ ha)
  have hyw : ∀ a : E, a • H.y ∈ Y.L → Valued.v (τ a) ≤ 1 := fun a ha =>
    hyp _ (hτs a H.y ▸ mem_splitLat_of_mem τ ha)

  have hxu : ∃ a : E, a • H.x ∈ Y.L ∧ 1 ≤ Valued.v (τ a) := by
    obtain ⟨a, ha, hle⟩ := exists_valued_le F E v.1 τ n Y.L (Y.J *ᵥ fun i => σ (H.y i)) {a | a • H.x ∈ Y.L}
      (by simp) (fun z hz => (hco z hz).1) _ hxL
    refine ⟨a, ha, le_of_eq_of_le ?_ hle⟩
    rw [map_dotProduct τ]
    change 1 = Valued.v (τ (form σ Y.J H.x H.y))
    rw [hH.xy, map_one, map_one]
  have hyu : ∃ a : E, a • H.y ∈ Y.L ∧ 1 ≤ Valued.v (τ a) := by
    obtain ⟨a, ha, hle⟩ := exists_valued_le F E v.1 τ n Y.L (-(Y.J *ᵥ fun i => σ (H.x i))) {a | a • H.y ∈ Y.L}
      (by simp) (fun z hz => by show (z ⬝ᵥ -(Y.J *ᵥ _)) • H.y ∈ Y.L; rw [dotProduct_neg]; exact (hco z hz).2.1) _ hyL
    refine ⟨a, ha, le_of_eq_of_le ?_ hle⟩
    rw [map_dotProduct τ, dotProduct_neg]
    change 1 = Valued.v (τ (-form σ Y.J H.y H.x))
    rw [hyx, neg_neg, map_one, map_one]

  have hwP : w.asIdeal ∈ v.1.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split hB.cm τ] at hwP
  rcases hwP with hw1 | hw1
  · have hw2 : w = splitPrime τ := HeightOneSpectrum.ext hw1
    have hval : ∀ a : E, w.valuation E a = Valued.v (τ a) := fun a =>
      (congrArg (fun u : HeightOneSpectrum (𝓞 E) => u.valuation E a) hw2).trans (valued_apply_eq_valuation τ a).symm
    refine count_eq_zero_of_valuation h0 _ (fun a ha => ?_) ?_
    · rw [hval]; exact hxw a ((hH.ideal a).1 ha)
    · obtain ⟨a, ha, h1⟩ := hxu
      exact ⟨a, (hH.ideal a).2 ha, by rw [hval]; exact h1⟩
  · have hw2 : w = splitPrime (τ.comp σ) := HeightOneSpectrum.ext (Set.mem_singleton_iff.1 hw1)
    have hval : ∀ a : E, w.valuation E a = Valued.v (τ (σ a)) := fun a =>
      (congrArg (fun u : HeightOneSpectrum (𝓞 E) => u.valuation E a) hw2).trans (valued_apply_eq_valuation _ a).symm
    have hwP' : w.under (𝓞 F) ∈ B.P := hw
    refine count_eq_zero_of_valuation h0 _ (fun a ha => ?_) ?_
    · obtain ⟨t, ht, h1⟩ := hyu
      have hd := (hY.dual (a • H.x)).1 ((hH.ideal a).1 ha) (t • H.y) ht
      have e : form σ Y.J (a • H.x) (t • H.y) = a * σ t := by
        rw [form_smul_left, form_smul_right, hH.xy]; ring
      rw [e] at hd
      have h2 := codiff_le_one F E σ B hB w hwP' _ hd
      rw [hval, map_mul, hσ, map_mul, map_mul] at h2
      rw [hval]
      calc Valued.v (τ (σ a)) = Valued.v (τ (σ a)) * 1 := (mul_one _).symm
        _ ≤ Valued.v (τ (σ a)) * Valued.v (τ t) := mul_le_mul' le_rfl h1
        _ ≤ 1 := h2
    · obtain ⟨d, hd0, hd⟩ := exists_denom E n Y.L hY.lat.fg (-(Y.J *ᵥ fun i => σ (H.x i)))
      have hdt : ∀ t : E, t • H.y ∈ Y.L → IsIntegral ℤ ((d : E) * t) := fun t ht => by
        have := hd _ ht
        rw [dotProduct_neg] at this
        change IsIntegral ℤ ((d : E) * -form σ Y.J (t • H.y) H.x) at this
        rwa [form_smul_left, hyx, mul_neg_one, neg_neg] at this
      let σZ : E →ₐ[ℤ] E := (σ : E →+* E).toIntAlgHom
      have hd1 : RingOfIntegers.mapRingHom (σ : E →+* E) d ≠ 0 := fun h => hd0 (by
        have h' := congrArg (fun x : 𝓞 E => (x : E)) h
        simp at h'
        exact h')
      obtain ⟨s', hs'1, hs'2⟩ := exists_unit_mul_integral E w {u | ∃ t, t • H.y ∈ Y.L ∧ u = σ t}
        (RingOfIntegers.mapRingHom (σ : E →+* E) d) hd1 (by
          rintro _ ⟨t, ht, rfl⟩
          show IsIntegral ℤ (σ (d : E) * σ t)
          rw [← map_mul]
          exact (hdt t ht).map σZ) (by
          rintro _ ⟨t, ht, rfl⟩
          rw [hval, hσ]
          exact hyw t ht)
      refine ⟨s', (hH.ideal _).2 ((hY.dual _).2 fun z hz o => ?_), by rw [hs'1]⟩
      rw [(hco z hz).2.2]
      exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (hs'2 _ ⟨_, (hco z hz).2.1, rfl⟩))

end GlobalTheory.SkewPlaneIdeal
end
end

section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_skew_ideal_coprime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsSkew σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  first | exact @GlobalTheory.SkewPlaneIdeal.skewPlaneIdeal_ne_zero_and_count_eq_zero | exact GlobalTheory.SkewPlaneIdeal.skewPlaneIdeal_ne_zero_and_count_eq_zero | (intros; apply GlobalTheory.SkewPlaneIdeal.skewPlaneIdeal_ne_zero_and_count_eq_zero <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.EulerIdeal

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.L2.Host (aboveF)
open scoped nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_count (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w 𝔞 ≠ 0}.Finite :=
  Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors 𝔞)

theorem hasFiniteMulSupport_zpow {M : Type} [DivInvMonoid M] (x : HeightOneSpectrum (𝓞 E) → M)
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    Function.HasFiniteMulSupport fun w => x w ^ FractionalIdeal.count E w 𝔞 :=
  (finite_count 𝔞).subset fun w hw h0 => hw (by simp only [h0, zpow_zero])

theorem idealVal_mul (χ : Chr F E) {𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) (h𝔠 : 𝔠 ≠ 0) :
    idealVal χ (𝔟 * 𝔠) = idealVal χ 𝔟 * idealVal χ 𝔠 := by
  unfold idealVal
  simp only [FractionalIdeal.count_mul E _ h𝔟 h𝔠, zpow_add]
  exact finprod_mul_distrib (hasFiniteMulSupport_zpow _ _) (hasFiniteMulSupport_zpow _ _)

theorem idealVal_inv (χ : Chr F E) (𝔟 : FractionalIdeal (𝓞 E)⁰ E) : idealVal χ 𝔟⁻¹ = (idealVal χ 𝔟)⁻¹ := by
  unfold idealVal
  simp only [FractionalIdeal.count_inv, zpow_neg]
  exact finprod_inv_distrib _

section Constants

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def diffK : FractionalIdeal (𝓞 K)⁰ K := (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)

end Constants

open GlobalTheory.ThK

variable {σ : E →ₐ[F] E}

end GlobalTheory.EulerIdeal
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK

section Values

open GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idealVal_mul_chr (χ ψ : Chr F E) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    idealVal (χ * ψ) 𝔞 = idealVal χ 𝔞 * idealVal ψ 𝔞 := by
  unfold idealVal
  simp_rw [val_mul, mul_zpow]
  exact finprod_mul_distrib (GlobalTheory.SqStepIdeal.mulSupport_finite _ 𝔞) (GlobalTheory.SqStepIdeal.mulSupport_finite _ 𝔞)

theorem idealVal_prime (χ : Chr F E) (w : HeightOneSpectrum (𝓞 E)) :
    idealVal χ (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = val χ w := by
  unfold idealVal
  rw [finprod_eq_single _ w, FractionalIdeal.count_self, zpow_one]
  intro v hv
  rw [FractionalIdeal.count_maximal_coprime E v hv.symm, zpow_zero]

theorem idealVal_one (χ : Chr F E) : idealVal χ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 := by
  unfold idealVal
  simp [FractionalIdeal.count_one]

theorem exists_idealVal_eq {ξ : Chr F E} (hξ : IsHecke F E ξ) (hu : ∀ᶠ w in Filter.cofinite, UnrAt ξ w) {n : ℕ} (hn : 0 < n)
    (hv : ∀ w, val ξ w ^ n = 1) (k : (AE F E)ˣ) :
    ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 ∧ idealVal ξ 𝔞 = Circle.toUnits (ξ k) := by
  let H : Subgroup ℂˣ :=
    { carrier := {z | ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 ∧ idealVal ξ 𝔞 = z}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, mul_ne_zero ha hb, GlobalTheory.EulerIdeal.idealVal_mul ξ ha hb⟩
      one_mem' := ⟨1, one_ne_zero, idealVal_one ξ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, inv_ne_zero ha, GlobalTheory.EulerIdeal.idealVal_inv ξ a⟩ }
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : H ≤ rootsOfUnity n ℂ := by
    rintro _ ⟨a, -, rfl⟩
    unfold idealVal
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := (GlobalTheory.SqStepIdeal.mulSupport_finite (val ξ) a).toFinset) (by simp)]
    exact Subgroup.prod_mem _ fun w _ => Subgroup.zpow_mem _ ((mem_rootsOfUnity _ _).2 (hv w)) _
  haveI : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective h1)
  have hc : 0 < Nat.card H := Nat.card_pos
  haveI : NeZero (Nat.card H) := ⟨hc.ne'⟩
  have h2 : H ≤ rootsOfUnity (Nat.card H) ℂ := fun z hz => by
    rw [mem_rootsOfUnity]
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : H)))
    rwa [SubmonoidClass.coe_pow] at this
  have h3 : H = rootsOfUnity (Nat.card H) ℂ := by
    refine Subgroup.eq_of_le_of_card_ge h2 ?_
    exact card_rootsOfUnity ℂ (Nat.card H)
  have h4 : ξ ^ Nat.card H = 1 := by
    refine GlobalTheory.HeckeUnifApprox.eq_one_of_unif_cofinite _ ⟨?_, fun x => ?_⟩ (hu.mono fun w hw ϖ hϖ => ?_)
    · exact hξ.1.pow _
    · rw [MonoidHom.pow_apply, hξ.2 x, one_pow]
    · have e1 : val ξ w ∈ H := ⟨w.asIdeal, FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot, idealVal_prime ξ w⟩
      have e2 := (mem_rootsOfUnity _ _).1 (h2 e1)
      rw [← hw.locChar_eq_val hϖ] at e2
      have e3 : Circle.toUnits (ξ (locIdele F w ϖ) ^ Nat.card H) = Circle.toUnits 1 := by
        rw [map_pow, map_one]; exact e2
      rw [MonoidHom.pow_apply]
      exact Circle.ext (congrArg Units.val e3)
  have h5 : Circle.toUnits (ξ k) ∈ H := by
    rw [h3, mem_rootsOfUnity, ← map_pow, ← MonoidHom.pow_apply, h4, MonoidHom.one_apply, map_one]
  exact h5

theorem nu_good {B : Base F E} {X : Chars F E} {a a' : ℕ} (h : X.IsGood B a a') :
    IsHecke F E X.ν ∧ ∀ᶠ w in Filter.cofinite, UnrAt X.ν w := by
  refine ⟨⟨h.heckeα.1.div' h.heckeβ.1, fun x => by
    simp only [Chars.ν, MonoidHom.div_apply, h.heckeα.2 x, h.heckeβ.2 x, div_one]⟩, ?_⟩
  have hf : (above E (X.T : Set (Pl F))).Finite :=
    (Set.Finite.biUnion X.T.finite_toSet fun v _ => Formalism.L2.Host.finite_aboveF (L := E) F v).subset fun w hw =>
      Set.mem_biUnion hw rfl
  refine Filter.eventually_cofinite.2 (hf.subset fun w hw => ?_)
  by_contra hn
  refine hw ?_
  rw [Chars.ν, div_eq_mul_inv]
  exact (h.unrα w hn).mul (h.unrβ w hn).inv

theorem exists_stepFac_twist (B : Base F E) {X Y : Chars F E} (hξ : IsHecke F E (X.ν / Y.ν))
    (hu : ∀ᶠ w in Filter.cofinite, UnrAt (X.ν / Y.ν) w) {n : ℕ} (hn : 0 < n) (hv : ∀ w, val (X.ν / Y.ν) w ^ n = 1)
    (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (z : ℤ) (k : (AE F E)ˣ) :
    ∃ (𝔟' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (r : ℂ), r ≠ 0 ∧
      stepFac B X e₁ e₂ s 𝔟' 𝔠 z = ((X.ν k / Y.ν k : Circle) : ℂ) * r * stepFac B X e₁ e₂ s 𝔟 𝔠 z ∧
      stepFac B Y e₁ e₂ s 𝔟' 𝔠 z = r * stepFac B Y e₁ e₂ s 𝔟 𝔠 z := by
  obtain ⟨𝔟₀, h0, e0⟩ : ∃ 𝔟₀ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔟₀ ≠ 0 ∧
      ∀ χ : Chr F E, idealVal χ 𝔟₀ = idealVal χ 𝔟 := by
    by_cases h : 𝔟 = 0
    · refine ⟨1, one_ne_zero, fun χ => ?_⟩
      rw [idealVal_one, h]
      unfold idealVal
      simp [FractionalIdeal.count_zero]
    · exact ⟨𝔟, h, fun _ => rfl⟩
  obtain ⟨𝔞, ha, e⟩ := exists_idealVal_eq hξ hu hn hv (k ^ (e₁ : ℤ))
  have e1 : idealVal X.ν 𝔞 ^ (e₁ : ℤ) = Circle.toUnits (X.ν k / Y.ν k) * idealVal Y.ν 𝔞 ^ (e₁ : ℤ) := by
    have : idealVal X.ν 𝔞 = idealVal (X.ν / Y.ν) 𝔞 * idealVal Y.ν 𝔞 := by
      rw [← idealVal_mul_chr, div_mul_cancel]
    rw [this, e, mul_zpow, map_zpow, map_zpow, ← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one,
      MonoidHom.div_apply]
  refine ⟨𝔞 * 𝔟₀, (idealVal Y.ν 𝔞 ^ (e₁ : ℤ) : ℂˣ), Units.ne_zero _, ?_, ?_⟩
  · unfold stepFac
    rw [GlobalTheory.EulerIdeal.idealVal_mul _ ha h0, e0, mul_zpow, e1]
    simp only [Units.val_mul, mul_assoc]
    rfl
  · unfold stepFac
    rw [GlobalTheory.EulerIdeal.idealVal_mul _ ha h0, e0, mul_zpow]
    simp only [Units.val_mul, mul_assoc]

end Values

theorem val_quot_pow {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T) :
    ∃ n : ℕ, 0 < n ∧ ∀ w, GlobalTheory.LFun.val ((GlobalTheory.SqStep.chs G i j t).ν / (GlobalTheory.SqStep.chs G i j μ₀).ν) w ^ n = 1 := by
  have e : ∀ s, (GlobalTheory.SqStep.chs G i j s).ν = G.nu s i (j + 1) := fun s => by
    show (Lc.mu s (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  have hν : (GlobalTheory.SqStep.chs G i j t).ν / (GlobalTheory.SqStep.chs G i j μ₀).ν = Lc.xi t * (Lc.xi μ₀)⁻¹ := by
    rw [e, e]
    refine MonoidHom.ext fun x => ?_
    show Lc.mu0 (j + 1) x * Lc.xi t x / G.ch.chi (D.R.m - i) x / (Lc.mu0 (j + 1) x * Lc.xi μ₀ x / G.ch.chi (D.R.m - i) x) =
      Lc.xi t x * (Lc.xi μ₀ x)⁻¹
    rw [div_div_div_cancel_right, mul_div_mul_left_eq_div, div_eq_mul_inv]
  obtain ⟨n, hn, hfin⟩ := hL.xi_fin t
  refine ⟨n, hn, fun w => ?_⟩
  rw [hν, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, GlobalTheory.LFun.val_eq_of_chrEq (hL.xi t) w, GlobalTheory.LFun.val_eq_of_chrEq (hL.xi μ₀) w,
    hL.xi_base, show (1 : HChar D.host.E).val w = 1 from rfl, inv_one, mul_one]
  exact (GlobalTheory.SqStepIdeal.val_mem hfin (hN.chars.xi t) w).1

theorem gbig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

theorem gbig_three_is {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ hL ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

theorem step_first : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  intro hP hK hM
  obtain ⟨e₁, e₂, s, hSB⟩ := hK.2.1
  refine gbig_three_is (GlobalTheory.T.tower_stage_extension_exists hP hK hM) (GlobalTheory.T.tower_stage_successor_coefficients hP hK hM) (GlobalTheory.T.exists_factor_of_stage_triangle hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hL hy hd hf W S hψ hN i j p q A A' WW X lam e hX hF he
  obtain ⟨B', WW₁, Y, hY, hst⟩ := hy W S hψ hN i j p q A A' WW X hX
  obtain ⟨c, hc⟩ := hf W S hψ hN i j p q A B' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨A, B', WW₁, Y, c, hY, hc.isConst, hc.1, fun t => ?_⟩
  obtain ⟨Bs, bb, Γ, Γ₁, H, H', R, R₁, d, d₁, k, k₁, hfit, hb, hV, hp, hq, hH, hH', hd0, hd10, hk⟩ :=
    hd W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY hst hF hc he t
  obtain ⟨C₀, hC₀, hstep⟩ := hSB D.host.F D.host.E D.sp.cm.sig Bs A.rank bb Γ Γ₁ H H' R R₁ hV hp hq hH hH'
  have hE : (A.rank - (bb + 2)) / 2 = e := by omega
  have key : ∀ t' ∈ ({t, μ₀} : Set T),
      d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t' *
      GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t').ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
      (C₀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t') e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ))) =
      d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t' := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, hκ⟩, ⟨om₁, om₁', Rf₁, hm₁, hκ₁⟩⟩ := hk t' ht'
    obtain ⟨u, hu1, hu2⟩ := hstep _ om om' Rf om₁ om₁' Rf₁ hm hm₁ _ _ hκ hκ₁
    rw [hE] at hu1 hu2
    have e1 : (((e : ℕ) : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e1] at hu2
    change _ * GlobalTheory.LFun.charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ = _ at hu2
    rw [hu2, mul_right_comm, hu1, one_mul]
  have good : ∀ t' ∈ ({t, μ₀} : Set T), GlobalTheory.LFun.IsHecke D.host.F D.host.E (GlobalTheory.SqStep.chs G i j t').ν ∧
      ∀ᶠ w in Filter.cofinite, GlobalTheory.LFun.UnrAt (GlobalTheory.SqStep.chs G i j t').ν w := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, -⟩, -⟩ := hk t' ht'
    exact nu_good hm.triple.chars
  obtain ⟨gt, ut⟩ := good t (by simp)
  obtain ⟨gμ, uμ⟩ := good μ₀ (by simp)
  obtain ⟨n, hn, hv⟩ := val_quot_pow G hL W S hN i j t
  obtain ⟨𝔟, r, hr, st, sμ⟩ := exists_stepFac_twist Bs (X := GlobalTheory.SqStep.chs G i j t) (Y := GlobalTheory.SqStep.chs G i j μ₀)
    ⟨gt.1.div' gμ.1, fun y => by simp only [MonoidHom.div_apply, gt.2 y, gμ.2 y, div_one]⟩
    ((ut.and uμ).mono fun w hw => by rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv) hn hv e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ)) (k / k₁)
  have kt := key t (by simp)
  have kμ := key μ₀ (by simp)
  rw [div_self', div_self', Circle.coe_one, mul_one, mul_one] at kμ
  have ek : (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) =
      (((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁) : Circle) : ℂ) *
        (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) := by
    rw [← Circle.coe_mul, div_mul_div_comm, ← map_mul, ← map_mul, div_mul_cancel]
  rw [ek] at kt
  have z₀ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁))
  have z₁ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁)
  have nt := mul_ne_zero (mul_ne_zero hd10 z₁) (hc.1 t)
  have nμ : d₁ * c μ₀ ≠ 0 := mul_ne_zero hd10 (hc.1 μ₀)
  rw [← kt] at nt
  rw [← kμ] at nμ
  refine ⟨Bs, e₁, e₂, s, 𝔟, H'.𝔟, hfit, ?_, ?_, right_ne_zero_of_mul (left_ne_zero_of_mul nt),
    right_ne_zero_of_mul (left_ne_zero_of_mul nμ), ?_⟩
  · rw [st]
    exact mul_ne_zero (mul_ne_zero z₀ hr) (right_ne_zero_of_mul (right_ne_zero_of_mul nt))
  · rw [sμ]
    exact mul_ne_zero hr (right_ne_zero_of_mul (right_ne_zero_of_mul nμ))
  · rw [st, sμ]
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd0 hC₀) z₁) ?_
    linear_combination (r * c μ₀) * kt -
      (r * c t * (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ)) * kμ

end GlobalTheory.SqStepK

end
end
