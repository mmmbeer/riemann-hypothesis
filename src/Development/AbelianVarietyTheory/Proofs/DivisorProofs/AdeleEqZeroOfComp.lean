import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRangeOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
import Development.AbelianVarietyTheory.Definitions.Divisors.SecSpaceBotNeBot

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWMidF

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end Defs

end GlobalTheory.SWMidF

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWOpCase

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF

end GlobalTheory.SWOpCase

end
end

section
noncomputable section

namespace GlobalTheory.MajFrameCartan

open scoped TensorProduct Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

theorem isCartanInv_transpose {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (h : IsCartan M θ) :
    Formalism.IndefR.Datum.IsCartanInv Mᵀ θ := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : θᴴ * Mᵀ * θ = Mᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map] at this
    show θᵀ.map star * Mᵀ * θ = Mᵀ
    rw [Matrix.mul_assoc]
    exact this
  have hMt : (Mᵀ)ᴴ = Mᵀ := by
    ext i j
    have := congrFun (congrFun hM j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hH : (Mᵀ * θ)ᴴ = Mᵀ * θ := by
    rw [Matrix.conjTranspose_mul, hMt]
    calc θᴴ * Mᵀ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = (θᴴ * Mᵀ * θ) * θ := by simp only [Matrix.mul_assoc]
      _ = Mᵀ * θ := by rw [h2']
  refine ⟨h1, h2', Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩⟩
  have e : star x ⬝ᵥ ((Mᵀ * θ) *ᵥ x) = (θ *ᵥ x) ⬝ᵥ (M *ᵥ star x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have him := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := Mᵀ * θ) hH x
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · rw [e]; exact h3 x hx
  · simpa using him.symm

theorem exists_majorantFrame_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ X.Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ X.Jᵀ w),
      k ∈ stabArch σ X.Jᵀ w (bc (compInf F E w) a) →
        Commute ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w))) (X.θ w) := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hM : ∀ w : InfinitePlace F, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hX.herm]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (X.Jᵀ.map (B.emb w).1) (X.θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact isCartanInv_transpose (hM w) (hX.cartan w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k hk => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 *
        (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1 :=
      (archEquiv X.Jᵀ hcm (B.emb w) k).2
    have hbc : (b w).1 * ((b w)⁻¹).1 = 1 := Units.mul_inv _
    have key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 →
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x hx => by
      have hx' : cT (sigR w.Completion σ) x.1 * 1 * x.1 = 1 := hx
      have := congrArg (fun y => y.map (infEmb (B.emb w))) hx'
      simpa only [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
        using this
    rw [mem_stabArch, ha w] at hk
    have hu := key _ hk
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc'] at hu
    have := (GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK).1 hu
    rwa [h2 w] at this

end GlobalTheory.MajFrameCartan
end
end

section
noncomputable section

namespace GlobalTheory.KBridgeConv

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.KBridge GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finT_ofFinT (a : Af F ⊗[F] E) : finT F E (ofFinT F E a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e => rfl

theorem infT_ofFinT (a : Af F ⊗[F] E) : infT F E (ofFinT F E a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e => exact TensorProduct.zero_tmul _ _

theorem ofFinT_mem_latHat {n : ℕ} (X : Spc F E n) {y : Fin n → Af F ⊗[F] E}
    (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E))) : (fun i => ofFinT F E (y i)) ∈ latHat X := by
  rw [KBridge.mem_latHat_iff]
  refine ⟨fun i => infT_ofFinT _, ?_⟩
  have e : (fun i => finT F E (ofFinT F E (y i))) = y := funext fun i => finT_ofFinT _
  rw [e]; exact hy

theorem local_of_ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E →
    ∀ g : GAd σ X.Jᵀ, GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X →
      (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) ∧
      ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v := by
  intro F E _ _ _ _ _ σ B n X hL g hK
  obtain ⟨h1, h2⟩ := hK
  refine ⟨fun w => h1 w, ?_⟩
  have hfg : X.L.FG := hL.fg
  have hMM : (matHom (AF F) σ X.Jᵀ g⁻¹).1 * (matHom (AF F) σ X.Jᵀ g).1 = 1 := by
    rw [map_inv]; exact Units.inv_mul _
  have hfin : ∀ z : Fin n → AE F E, (fun i => finT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i)) = Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ g *ᵥ fun i => finT F E (z i) :=
    fun z => funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
  have hinf : ∀ z : Fin n → AE F E, (∀ i, infT F E (z i) = 0) → ∀ i, infT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i) = 0 := by
    intro z hz i
    have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hz j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ g).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := by
    refine (mem_levelOpen_iff_latHat σ X.Jᵀ hfg g).2 fun y => ?_
    let z : Fin n → AE F E := fun i => ofFinT F E (y i)
    have hzy : (fun i => finT F E (z i)) = y := funext fun i => finT_ofFinT _
    constructor
    · intro hy
      have hzL : z ∈ latHat X := ofFinT_mem_latHat X hy
      have := (h2 z hzL).1
      rw [GlobalTheory.IwLine.mat_ofGAd] at this
      have h := ((KBridge.mem_latHat_iff X _).1 this).2
      rw [hfin, hzy] at h
      exact h
    · intro hy
      have hw : (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X := by
        rw [KBridge.mem_latHat_iff]
        refine ⟨hinf z (fun i => infT_ofFinT _), ?_⟩
        rw [hfin, hzy]; exact hy
      have := (h2 _ hw).2
      rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec] at this
      have h := ((KBridge.mem_latHat_iff X _).1 this).2
      rw [hzy] at h
      exact h
  exact mem_levelOpen.1 hg

end GlobalTheory.KBridgeConv
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_commutes_majorant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E →
    ∀ g : GAd σ X.Jᵀ, GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X →
      (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) ∧
      ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v := by
  first | exact @GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK | exact GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK | (intros; apply GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.DblIwasawa

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem transpose_dblGram {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (dblGram finSumFinEquiv J)ᵀ = dblGram finSumFinEquiv Jᵀ := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [dblGram, blkMat, Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply]

theorem hasIwasawa_fin (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ} (X : Spc F E n)
    (hX : IsHermND σ X.J) (hL : X.L.IsLattice E)
    (hd : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv X.Jᵀ) (v : HeightOneSpectrum (𝓞 F)) :
    HasIwasawa σ Q (KFin σ Q X.L v) := by
  haveI : Submodule.IsLattice E X.L := hL
  have hJt : IsHermND σ X.Jᵀ := ⟨fun i j => hX.1 j i, by rw [Matrix.det_transpose]; exact hX.2⟩
  have hSD : IsSelfDualAt σ X.Jᵀ X.L v := by
    refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJt.2 hL).2 (fun y => ?_) v
    rw [hd y]
    simp only [GlobalTheory.HermSelfDualLoc.hE_transpose, GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]
  have hQ' : IsHermND σ Q := hQ ▸ GlobalTheory.GraphIwSplit.isHermND_dblGram σ hJt
  haveI := hun
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨w, hw⟩
  · obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom hcm hQ hJt hQ'
      (GlobalTheory.AdelicU.existsUnique_splitPrime_eq hcm hne h1 h2).exists.choose X.L hSD
  · exact GlobalTheory.InertIwasawaGen.hasIwasawa_of_inertAt hcm hJt hQ hw hSD

section Arch

open Formalism.UG (bc UJ cT)

theorem arch (hcm : IsCMExt F E σ) (B : Base F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (θ : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (hJ : ∀ i j, σ (J j i) = J i j)
    (hθ : ∀ w, IsCartan (J.map (B.emb w).1) (θ w)) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv Jᵀ) :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ Q w),
      k ∈ KArch σ Q w (Formalism.UG.bc (compInf F E w) a) ↔
        Commute ((matHom w.Completion σ Q k).1.map (infEmb (B.emb w))) (blkMat finSumFinEquiv (θ w) (-θ w)) := by
  have hM : ∀ w : InfinitePlace F, (J.map (B.emb w).1)ᴴ = J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hJ]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (Jᵀ.map (B.emb w).1) (θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact GlobalTheory.MajFrameCartan.isCartanInv_transpose (hM w) (hθ w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ Q k).1.map (infEmb (B.emb w)))ᴴ * Q.map (B.emb w).1 *
        (matHom w.Completion σ Q k).1.map (infEmb (B.emb w)) = Q.map (B.emb w).1 :=
      (archEquiv Q hcm (B.emb w) k).2
    have key : ∀ x : GL (Fin (n + n)) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 ↔
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x => by
      change cT _ x.1 * 1 * x.1 = 1 ↔ _
      rw [← (Matrix.map_injective (infEmb_bijective hcm (B.emb w)).1).eq_iff]
      beta_reduce
      rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
    have hcT : ∀ x y : Matrix (Fin n) (Fin n) ℂ,
        (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := fun x y => by
      simp [blkMat, Matrix.fromBlocks_conjTranspose]
    have hbc : blkMat finSumFinEquiv (b w).1 (b w).1 * blkMat finSumFinEquiv ((b w)⁻¹).1 ((b w)⁻¹).1 = 1 := by
      rw [blkMat_mul, Units.mul_inv, blkMat_one]
    have hQw : Q.map (B.emb w).1 =
        blkMat finSumFinEquiv (Jᵀ.map (B.emb w).1) (-(Jᵀ.map (B.emb w).1)) := by
      rw [hQ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
    set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if ε w i then 1 else -1 with hD
    have hd : (blkMat finSumFinEquiv (b w).1 (b w).1)ᴴ * Q.map (B.emb w).1 *
        blkMat finSumFinEquiv (b w).1 (b w).1 = blkMat finSumFinEquiv D (-D) := by
      rw [hcT, hQw, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul, h1 w]
    have hdd : blkMat finSumFinEquiv D (-D) * blkMat finSumFinEquiv D (-D) = 1 := by
      rw [blkMat_mul, neg_mul_neg, hD, GlobalTheory.Doubling.diagonal_sign_mul_self, blkMat_one]
    have hs : blkMat finSumFinEquiv (b w).1 (b w).1 * (blkMat finSumFinEquiv (b w).1 (b w).1)ᴴ *
        Q.map (B.emb w).1 = blkMat finSumFinEquiv (θ w) (-θ w) := by
      rw [hcT, hQw, blkMat_mul, blkMat_mul, Matrix.mul_neg, h2 w]
    rw [← hs, ← GlobalTheory.Doubling.unitary_iff_commute hbc hd hdd hK]
    show _ ∈ stabArch σ Q w (blkGL finSumFinEquiv (_, _)) ↔ _
    rw [mem_stabArch, ha w, key, ← map_inv, Prod.inv_mk, Units.val_mul, Units.val_mul, val_blkGL, val_blkGL,
      Matrix.map_mul, Matrix.map_mul, blkMat_map _ _ (map_zero _), blkMat_map _ _ (map_zero _), hc, hc']

end Arch

theorem isCompact_and_iwasawaOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (B : Base F E) (n : ℕ) (X : Spc F E n),
    IsHermND σ X.J → X.L.IsLattice E → (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) →
    (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) → ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J →
    X₂.L = sumLat finSumFinEquiv X.L X.L → (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
    ∀ K : Subgroup (UA σ X₂.J), IsStab B K → IsCompact (K : Set (UA σ X₂.J)) ∧
      IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K := by
  intro F E _ _ _ _ _ σ hcm hun B n X hX hL hd hθ X₂ hJ₂ hL₂ hθ₂ K hK
  haveI : Submodule.IsLattice E X.L := hL
  have hQ : X₂.Jᵀ = dblGram finSumFinEquiv X.Jᵀ := by rw [hJ₂, transpose_dblGram]
  obtain ⟨a, hmaj, harch⟩ := arch hcm B X.J X.θ hX.1 hθ hQ
  have hI : HasIwasawa σ X₂.Jᵀ (KAd σ X₂.Jᵀ X.L a) := by
    refine HasIwasawa.adelic (fun v => hasIwasawa_fin hcm hun X hX hL hd hQ v) (fun w => ?_)
    obtain ⟨ε, hε⟩ := hmaj w
    exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hcm hQ w _ ε hε
  have hL₂' : X₂.L.IsLattice E := by rw [hL₂]; infer_instance
  have key : ∀ g : GAd σ X₂.Jᵀ, GlobalTheory.IwLine.ofGAd σ X₂.J g ∈ K ↔ g ∈ KAd σ X₂.Jᵀ X.L a := by
    intro g
    rw [(hK _).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X₂ _).symm, mem_KAd]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B (n + n) X₂ hL₂' g h
      refine ⟨fun v => ?_, fun w => ?_⟩
      · have := h2 v; rwa [hL₂] at this
      · rw [harch w, ← hθ₂ w]; exact h1 w
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B (n + n) X₂ hL₂' g (fun w => ?_) (fun v => ?_)
      · rw [hθ₂ w, ← harch w]; exact h1 w
      · rw [hL₂]; exact h2 v
  have hcont : Continuous (GlobalTheory.IwLine.ofGAd σ X₂.J) := Continuous.subtype_mk continuous_subtype_val _
  have hKset : (K : Set (UA σ X₂.J)) =
      GlobalTheory.IwLine.ofGAd σ X₂.J '' (KAd σ X₂.Jᵀ X.L a : Set (GAd σ X₂.Jᵀ)) := by
    ext g
    constructor
    · intro hg
      refine ⟨(GlobalTheory.IwLine.ofGAd σ X₂.J).symm g, (key _).1 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply _ _⟩
    · rintro ⟨g', hg', rfl⟩
      exact (key g').2 hg'
  have hKc : IsCompact (K : Set (UA σ X₂.J)) := by
    rw [hKset]; exact (isCompact_KAd hcm).image hcont
  refine ⟨hKc, ?_⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  refine iwasawaOf_of_isCompact continuous_subtype_val continuous_absE hKc fun g => ?_
  obtain ⟨p, k, hk, e⟩ := hI ((GlobalTheory.IwLine.ofGAd σ X₂.J).symm g)
  have hp : (GlobalTheory.IwLine.ofGAd σ X₂.J p) ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := p.2
  refine ⟨⟨_, hp⟩, GlobalTheory.IwLine.ofGAd σ X₂.J k, (key k).2 hk, ?_⟩
  have := congrArg (GlobalTheory.IwLine.ofGAd σ X₂.J) e
  rw [MulEquiv.apply_symm_apply, map_mul] at this
  exact this

end GlobalTheory.DblIwasawa

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section
namespace GlobalTheory.SkewDblIwasawa

theorem mem_hR_smul_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (c : E) (hc : c ≠ 0) (Q : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)) :
    g ∈ HR R σ (c • Q) ↔ g ∈ HR R σ Q := by
  have hu : IsUnit (inclR (F := F) R c) := (IsUnit.mk0 c hc).map _
  have e : JR (F := F) R (c • Q) = inclR (F := F) R c • JR R Q := by
    ext i j; simp [JR, Matrix.map_apply, Matrix.smul_apply, map_mul]
  change Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR (F := F) R (c • Q) *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R (c • Q) ↔
    Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR (F := F) R Q *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R Q
  rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]

theorem hasIwasawa_of_smul {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (c : E) (hc : c ≠ 0) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (S : Subgroup (GL (Fin (n + n)) (R ⊗[F] E)))
    (h : HasIwasawa σ (c • Q) (S.comap (GlobalTheory.AdelicU.matHom R σ (c • Q)))) :
    HasIwasawa σ Q (S.comap (GlobalTheory.AdelicU.matHom R σ Q)) := by
  intro g
  obtain ⟨p, k, hk, e⟩ := h ⟨g.1, (mem_hR_smul_iff R σ c hc Q g.1).2 g.2⟩
  refine ⟨⟨⟨p.1.1, (mem_hR_smul_iff R σ c hc Q _).1 p.1.2⟩, p.2⟩, ⟨k.1, (mem_hR_smul_iff R σ c hc Q _).1 k.2⟩, hk, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val e
  exact this

theorem dblGram_smul {E : Type} [Field E] {n : ℕ} (c : E) (J : Matrix (Fin n) (Fin n) E) :
    dblGram finSumFinEquiv (c • J) = c • dblGram finSumFinEquiv J := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [dblGram, blkMat, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, smul_neg]

end GlobalTheory.SkewDblIwasawa

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.FlatEisHol

open scoped NNReal

theorem analyticOnNhd_cosetSum_npow {G : Type} [Group G] (P Γ : Subgroup G) (Φ : G → ℂ) (h : G → ℝ≥0)
    (hpos : ∀ x, 0 < h x) (s₀ : ℂ) (σ₀ : ℝ)
    (hc : ∀ s : ℂ, σ₀ < s.re → ∀ g, GlobalTheory.Eis.CosetConv P Γ (fun x => Φ x * GlobalTheory.Doubling.npow (h x) (s - s₀)) g)
    (g : G) :
    AnalyticOnNhd ℂ (fun s => GlobalTheory.Eis.cosetSum P Γ (fun x => Φ x * GlobalTheory.Doubling.npow (h x) (s - s₀)) g)
      {s : ℂ | σ₀ < s.re} :=
  GlobalTheory.Eis.analyticOnNhd_tsum_npow (f := fun q => Φ (((Quot.out q : Γ) : G) * g))
    (a := fun q => h (((Quot.out q : Γ) : G) * g)) (fun _ => hpos _) (fun s hs => hc s hs g)

end GlobalTheory.FlatEisHol

theorem GlobalTheory.FlatEisHol.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (W₂ : Spc F E (n + n)) (K₂ : Subgroup (UA σ W₂.J)) (φ₀ : UA σ W₂.J → ℂ) (s₂ : ℂ) (σ₀ : ℝ),
    (∀ s : ℂ, σ₀ < s.re → ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K₂ φ₀ s₂ s) g) →
    ∀ g, AnalyticOnNhd ℂ (fun s => GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K₂ φ₀ s₂ s) g) {s : ℂ | σ₀ < s.re} := by
  intro F E _ _ _ _ _ σ n W₂ K₂ φ₀ s₂ σ₀ hc g
  exact GlobalTheory.FlatEisHol.analyticOnNhd_cosetSum_npow _ _ φ₀ _ (fun x => GlobalTheory.Doubling.hgtOf_pos x) s₂ σ₀ hc g
end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase

namespace GlobalTheory.SWOpIndef

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

def supAt {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) (v₀ : HeightOneSpectrum (𝓞 F)) : Subgroup (UA σ J₂) where
  carrier := {g | (mat g).det = 1 ∧ (∀ v, v ≠ v₀ → (mat g).map (compFin F E v) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (mat g).map (piInf τ) = 1}
  one_mem' := by
    refine ⟨by simp [show mat (1 : UA σ J₂) = 1 from rfl], fun v _ => ?_, fun w τ => ?_⟩ <;>
      simp [show mat (1 : UA σ J₂) = 1 from rfl]
  mul_mem' := by
    rintro g h ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    have e : mat (g * h) = mat g * mat h := rfl
    refine ⟨by rw [e, Matrix.det_mul, h1, h1', one_mul], fun v hv => ?_, fun w τ => ?_⟩
    · rw [e, Matrix.map_mul, h2 v hv, h2' v hv, one_mul]
    · rw [e, Matrix.map_mul, h3 w τ, h3' w τ, one_mul]
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    have e : mat g⁻¹ * mat g = 1 := by
      change mat (g⁻¹ * g) = 1
      rw [inv_mul_cancel]; rfl
    refine ⟨?_, fun v hv => ?_, fun w τ => ?_⟩
    · have := congrArg Matrix.det e
      rwa [Matrix.det_mul, h1, mul_one, Matrix.det_one] at this
    · have := congrArg (fun M => M.map (compFin F E v)) e
      simp only [Matrix.map_mul, h2 v hv, mul_one] at this
      simpa using this
    · have := congrArg (fun M => M.map (piInf τ)) e
      simp only [Matrix.map_mul, h3 w τ, mul_one] at this
      simpa using this

example {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) (g h : UA σ J₂) : mat (g * h) = mat g * mat h := by rfl
example {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) : mat (1 : UA σ J₂) = 1 := by rfl

end GlobalTheory.SWOpIndef
end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}

variable {σ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase GlobalTheory.SWOpFin

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_eq_zero_of_comp {c : AF F} (hf : ∀ v, evFin F v c = 0) (hi : ∀ w, evInf F w c = 0) : c = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact Subtype.ext (funext fun v => hf v)

theorem tens_eq_zero_of_comp {z : AF F ⊗[F] E} (hf : ∀ v, compFin F E v z = 0) (hi : ∀ w, compInf F E w z = 0) :
    z = 0 := by
  let b := Module.Free.chooseBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have key : ∀ {A : Type} [CommRing A] [Algebra F A] (f : AF F →ₐ[F] A),
      (Algebra.TensorProduct.map f (AlgHom.id F E)) z = 0 → ∀ i, f (B.repr z i) = 0 := by
    intro A _ _ f hz i
    have hs : z = ∑ j, B.repr z j • B j := (B.sum_repr z).symm
    have hz' : ∑ j, f (B.repr z j) • (Algebra.TensorProduct.basis A b) j = 0 := by
      rw [hs] at hz
      simpa [B, Algebra.TensorProduct.basis_apply, Finset.sum_apply, map_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Algebra.TensorProduct.map_tmul] using hz
    exact Fintype.linearIndependent_iff.1 (Algebra.TensorProduct.basis A b).linearIndependent _ hz' i
  have hc : ∀ i, B.repr z i = 0 := fun i =>
    adele_eq_zero_of_comp (fun v => key (evFin F v) (hf v) i) (fun w => key (evInf F w) (hi w) i)
  rw [← B.sum_repr z]
  simp [hc]

variable {σ : E →ₐ[F] E} {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
end
end
