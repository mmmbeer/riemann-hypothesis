import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.SphLocProd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PConjFix
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadingModuleHolds

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PCandSa

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locM_comp {a b : ℕ} {k k' : Type} [Fintype k] [Fintype k'] (w : Pl E) (φ : k ≃ k')
    (N : k' → k' → LF a b w) (Y : k' → H E a b → ℂ) (m : ℕ) :
    (locM w (fun x y => N (φ x) (φ y)))^[m] (Y ∘ φ) = ((locM w N)^[m] Y) ∘ φ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [locM, Function.comp]
    exact Equiv.sum_comp φ (fun y' => actP w (N (φ x) y') (((locM w N)^[m] Y) y'))

theorem isLev_lev {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) : Tail.IsLev (d.lev a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, e⟩ := LocOk.lev_lv d hd ha w
    rw [e]
    exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev_out d (LocOk.out3 d h).1 (LocOk.out3 d h).2)

theorem isLev_lev₂ {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) : Tail.IsLev (d.lev₂ a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, e⟩ := LocOk.lev₂_lv d hd ha w
    rw [e]
    exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev₂_out d (LocOk.out3 d h).2)

theorem betaL_hecke {n a : ℕ} (d : LocData E n) (hd : d.Ok) (ha : a ≤ n) :
    ∀ w ∈ d.P, ∀ x y, IsHecke (d.lev a w) ((d.betaL a ha).m w x y) := by
  intro w hw x y
  show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d w z.1.1) x y
  · have hS : w ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hw
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

def kapX {n : ℕ} (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) : d.kap w ≃ (d.X w) :=
  Equiv.ofBijective (fun x => ⟨x.1.2, LocOk.kap_X d hT hS x⟩) (by
    have e : d.idx w = {∅} ×ˢ d.X w := by unfold LocData.idx; rw [if_neg hT, if_pos hS]
    constructor
    · rintro ⟨⟨s, x⟩, hx⟩ ⟨⟨s', x'⟩, hx'⟩ h
      have h1 := (Finset.mem_product.1 (e ▸ hx)).1
      have h2 := (Finset.mem_product.1 (e ▸ hx')).1
      simp only [Finset.mem_singleton] at h1 h2
      simp only [Subtype.mk.injEq] at h
      subst h1 h2 h
      rfl
    · rintro ⟨x, hx⟩
      exact ⟨⟨(∅, x), by rw [e]; simp [hx]⟩, rfl⟩)

end PCandSa

open PCandSa in
theorem candS_of (h : Tail.ReadS) : CandS := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwS hsplit
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  obtain ⟨hS0, hBad, hμ, hϖ, hK', hX, hL, hfix, hKB⟩ := F.same
  have hw0 : w ∈ F₀.d₀.S₀ := F₀.S_le w hwS hsplit
  have hwd : w ∈ F.d.S₀ := hS0 ▸ hw0
  have hwT : w ∉ F.d.T := fun h => Finset.disjoint_left.1 F.ok.disj.1 h hwd
  have hwP : w ∈ F.d.P := Finset.mem_union_right _ hwd
  have hwSec : w ∈ F₀.Sec := (F₀.S₀ w hw0).1
  have hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h1 | h1
    · exact (F.T_in u h1).1
    · exact (F₀.S₀ u (hS0 ▸ h1)).1
  have hpow := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _)
    F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d F.ok ha) (isLev_lev₂ F.d F.ok ha)
    ((BlockFiniteConvolution.locOk₀ E n F.d F.ok _ ha).2.1) (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => ((betaL_hecke F.d F.ok ha u hu x y).2 k hk g)) hl hne ⟨w, hwP⟩
  obtain ⟨α, x₀, hx₀⟩ := hpow
  have hGy : ∀ j, G j ∈ pairSpace s₁.space s₂.space ∧ G j ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun j => ⟨hG j, ((hl j).2 w hwSec).1⟩
  set G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ :=
    fun y => G (α, (Equiv.refl _).symm (Function.update x₀ ⟨w, hwP⟩ y)) with hG'def
  have hG'p : ∀ y, G' y ∈ pairSpace s₁.space s₂.space ∧ G' y ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun y => hGy _
  change (locM w ((F.d.betaL _ ha).m w))^[F.m] G' ≠ 0 at hx₀
  clear_value G'
  set φ := kapX F.d hwT hwd with hφ
  let N : (F.d.X w) → (F.d.X w) → LF (F₀.C.a i) (n - F₀.C.a i) w :=
    fun x y => phiMu (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) x y
  have hm : (F.d.betaL _ ha).m w = fun x y => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • N (φ x) (φ y) := by
    funext x y g
    simp only [LocData.betaL, if_neg hwT, LocData.mac, Pi.smul_apply, smul_eq_mul, N, hμ, F₀.μloc]
    rfl
  rw [hm] at hx₀
  have hopen : IsOpen (F.d.lev (F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) :=
    ((isLev_lev F.d F.ok ha).1 w).1
  have h1 := (Tail.locPow_holds E _ _ w (F.d.kap w) (F.d.lev _ w) G' F.m hopen (fun y => (hG'p y).2)).1 _
    (fun x y => N (φ x) (φ y)) hx₀
  have h2 : (matS (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) (F.d.X w))^[F.m] (G' ∘ φ.symm) ≠ 0 := by
    intro h0
    apply h1
    have e1 := locM_comp w φ N (G' ∘ φ.symm) F.m
    rw [show (G' ∘ φ.symm) ∘ φ = G' from by funext y; simp] at e1
    rw [e1]
    change ((matS (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) (F.d.X w))^[F.m] (G' ∘ φ.symm)) ∘ φ = 0
    rw [h0]
    rfl
  obtain ⟨P, hPc, hkill⟩ := F.choiceS w hw0
  have hOk := F.ok.K' w hwd
  rw [hK'] at hOk
  obtain ⟨hO, hle, hN, hXK, hU, hHk⟩ := hOk
  exact ⟨P, h E n (F₀.C.a i) (n - F₀.C.a i) (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F₀.d₀.K' w) (F.d.X w)
    (F.d.lev _ w) (F.d.e w) P F.m (G' ∘ φ.symm) hO hle hN hXK hU hopen hHk (hkill i s₁ s₂ Pa Pb D hc)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).1 w hw0) (fun x => hG'p _) h2, hPc⟩

end PositivityTheory.Rg.BcB.F

end
end

section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail


theorem satSph : SatSph := by
  intro E _ _ _ n D w B hB
  obtain ⟨b, hb, -⟩ := hB
  exact GlobalTheory.Rigid.isSpherical_locProd D.h w (D.σ · w) fun i => (hb i).1

end PositivityTheory.Rg.BcB.F.Tail

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.B

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  apply Units.ext
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply,
    reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  have e : (m'.1.val) * (m'.1⁻¹).val = 1 := Units.mul_inv _
  have key : m.1.val * (m'.1.val * X') + m.1.val * X * m'.2.val =
      (m * m').1.val * (X' + (m'.1⁻¹).val * X * m'.2.val) := by
    rw [Prod.fst_mul, Units.val_mul]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc m'.1.val (m'.1⁻¹).val, e, Matrix.one_mul]
  rw [key]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Prod.fst_mul, Prod.snd_mul, Units.val_mul]

theorem blk_entries {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = m.1.val i j) ∧
      ∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = m.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] <;> rfl

theorem blocks_of_blk_mem {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (hk : blk h w m X ∈ GlobalTheory.LFun.KGL w n) :
    m.1 ∈ GlobalTheory.LFun.KGL w a ∧ m.2 ∈ GlobalTheory.LFun.KGL w b := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [CtLevel.blk_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w m X).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w _ _).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w m X).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w _ _).2] at this

end PositivityTheory.Rg.BcB.F.Tail.B

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.PCandLh

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem unrAt_pow {μ : HChar E} {w : Pl E} (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := fun x hx => by
  have h1 : (μ ^ k).loc w x = μ.loc w x ^ k := by
    induction k with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl
  rw [h1, h x hx, one_pow]

theorem actP_zero {a b : ℕ} (w : Pl E) (G : H E a b → ℂ) : actP w (fun _ => 0) G = 0 := by
  funext z
  simp only [actP, zero_mul, hint, finsum_zero, mul_zero, Pi.zero_apply]

theorem gap_restr {n m : ℕ} {x : Fin n → ℤ} (hx : x ∈ coneGL n 2) (S : Finset (Fin n)) (h : S.card = m) : Gap (PositivityTheory.Rg.Bc.ArchbcB.B.restr x S h) :=
  fun i j hij => by
    have := hx _ _ ((S.orderEmbOfFin h).strictMono hij)
    simp only [PositivityTheory.Rg.Bc.ArchbcB.B.restr]
    omega

set_option maxHeartbeats 1600000 in
open PCandSa in
theorem inert_d (h1 : Tail.ReadT) (h2 : Tail.ExpRead) (h3 : RS.JoinSat) (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (hE : GlobalTheory.BCT.Unr E) (n : ℕ)
    (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (Pl E)) (F₀ : Frame0 hR π S) (F : RunFrame F₀ T) (i : F₀.C.ι)
    (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i)) (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) (A : Type)
    (G : A × F.κ → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ) (hc : F₀.Cand F.d i s₁ s₂ Pa Pb D)
    (hG : ∀ j, G j ∈ pairSpace s₁.space s₂.space)
    (hl : ∀ j, OfLev F₀.Sec (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (G j))
    (hne : (convF (F.B i).ν (F.ψ i (F.d.betaL _ (F₀.C.le i))))^[F.m] G ≠ 0)
    (w : Pl E) (hwd : w ∈ F.d.T) : InertAt π D w := by
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  obtain ⟨hS0, hBad, hμ, hϖ, hK', hX, hL, hfix, hKB⟩ := F.same
  have hs : ¬ IsSplitAt w := (F.T_in w hwd).2.1
  have hu : IsUnramU π w := (F.T_in w hwd).2.2.1
  have hwP : w ∈ F.d.P := Finset.mem_union_left _ hwd
  have hwSec : w ∈ F₀.Sec := (F.T_in w hwd).1
  have hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h1 | h1
    · exact (F.T_in u h1).1
    · exact (F₀.S₀ u (hS0 ▸ h1)).1
  obtain ⟨α, x₀, hx₀⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _)
    F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d F.ok ha) (isLev_lev₂ F.d F.ok ha)
    ((BlockFiniteConvolution.locOk₀ E n F.d F.ok _ ha).2.1) (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => ((betaL_hecke F.d F.ok ha u hu x y).2 k hk g)) hl hne ⟨w, hwP⟩
  have hGy : ∀ j, G j ∈ pairSpace s₁.space s₂.space ∧ G j ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun j => ⟨hG j, ((hl j).2 w hwSec).1⟩
  set G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ :=
    fun y => G (α, (Equiv.refl _).symm (Function.update x₀ ⟨w, hwP⟩ y)) with hG'def
  have hG'p : ∀ y, G' y ∈ pairSpace s₁.space s₂.space ∧ G' y ∈ fixed (pairRt _ _ w) (F.d.lev (F₀.C.a i) w) :=
    fun y => hGy _
  change (locM w ((F.d.betaL _ ha).m w))^[F.m] G' ≠ 0 at hx₀
  clear_value G'
  have hm : (F.d.betaL _ ha).m w = fun x y => @ite _ (x = y) (Classical.propDecidable _) (F.d.qT (F₀.C.a i) w x.1.1) 0 := by
    funext x y
    simp only [LocData.betaL, if_pos hwd, LocData.diag]
    congr
  rw [hm] at hx₀
  obtain ⟨x, hx⟩ := (Tail.locPow_holds E _ _ w (F.d.kap w) (F.d.lev _ w) G' F.m ((isLev_lev F.d F.ok ha).1 w).1
    (fun y => (hG'p y).2)).2 (fun x => F.d.qT (F₀.C.a i) w x.1.1) hx₀
  generalize x.1.1 = s at hx
  have hfixI : G' x ∈ fixed (pairRt _ _ w) (I2 (F₀.C.a i) (n - F₀.C.a i) w) := LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd ▸ (hG'p x).2
  by_cases h : LocData.admitted n (F₀.C.a i) s
  swap
  · exfalso
    have e : F.d.qT (F₀.C.a i) w s = fun _ => 0 := by funext y; simp only [LocData.qT, dif_neg h]
    obtain ⟨k, hk⟩ : ∃ k, F.m = k + 1 := ⟨F.m - 1, by have := F.m_pos; omega⟩
    rw [e, hk, Function.iterate_succ_apply', actP_zero] at hx
    exact hx rfl
  set V : ℂ := (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ) with hV
  have e : F.d.qT (F₀.C.a i) w s = fun g => ∑ j : (F.d.c w).support,
      (F.d.c w j * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf j.1) s) * V) *
        dc2 w (F₀.d₀.ϖ w) (PositivityTheory.Rg.Bc.ArchbcB.B.restr j.1 _ h.2.1) (PositivityTheory.Rg.Bc.ArchbcB.B.restr j.1 _ h.2.2) g := by
    funext g
    simp only [LocData.qT, dif_pos h, Finsupp.sum, hϖ]
    exact (Finset.sum_coe_sort _ _).symm
  rw [e] at hx
  obtain ⟨ξa, ξb, hJ, hsum⟩ := h1 E n _ _ F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F₀.d₀.ϖ w) (F.d.c w).support _ _ _ F.m (G' x)
    (F₀.ok₀.unif w) (fun j => ⟨gap_restr (F.ok.cone w hwd j.2) _ _, gap_restr (F.ok.cone w hwd j.2) _ _⟩)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).2 w hwd) (hG'p x).1 hfixI hx
  have hsum' : ((F.d.c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s) *
      ev2 w ξa ξb (PositivityTheory.Rg.Bc.ArchbcB.B.restr x _ h.2.1) (PositivityTheory.Rg.Bc.ArchbcB.B.restr x _ h.2.2)) ≠ 0 := by
    intro h0
    apply hsum
    rw [Finsupp.sum, ← Finset.sum_coe_sort] at h0
    calc _ = V * ∑ j : (F.d.c w).support, F.d.c w j * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf j.1) s) *
          ev2 w ξa ξb (PositivityTheory.Rg.Bc.ArchbcB.B.restr j.1 _ h.2.1) (PositivityTheory.Rg.Bc.ArchbcB.B.restr j.1 _ h.2.2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  obtain ⟨m1, m2, hb⟩ := F.choiceT i s₁ s₂ Pa Pb D hc w hwd s h ξa ξb hJ hsum'
  obtain ⟨sa, sb⟩ := h2 E _ _ Pa Pb w (F₀.d₀.ϖ w) ξa ξb (F₀.ok₀.unif w) m1 m2 hJ
  have hun : F₀.μ.UnrAt w := (F₀.good w hwSec (fun a => hs (F₀.S₀ w a).2) fun a => (F₀.bad w a).2 hs hu).2
  refine ⟨_, h3 E n _ _ _ _ Pa Pb D w _ _ hc.ctx.join (unrAt_pow hun _) (unrAt_pow hun _) sa sb, fun s' ϖ q a1 a2 β hβ => ?_⟩
  obtain rfl : s' = cj w := ((GlobalTheory.T.placeConjugation_properties_cmField E hE w).2.2.2.1 hs).2.2.2 s' a2.2.1 a1
  exact hb ϖ q a2 β hβ

def stab {a b : ℕ} (w : Pl E) (G : H E a b → ℂ) : Subgroup (GLw a w × GLw b w) where
  carrier := {m | pairRt a b w m G = G}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem stab_open {a b : ℕ} (w : Pl E) {G : H E a b → ℂ} (h : HasLev G) : IsOpen (stab w G : Set (GLw a w × GLw b w)) := by
  obtain ⟨U, hU, hG⟩ := h
  have c1 : Continuous (locGL E a w) := by apply GlobalTheory.EulerTw.continuous_locGL_spl
  have c2 : Continuous (locGL E b w) := by apply GlobalTheory.EulerTw.continuous_locGL_spl
  have hc : Continuous ((locGL E a w).prodMap (locGL E b w)) := c1.prodMap c2
  refine Subgroup.isOpen_mono (H₁ := U.comap ((locGL E a w).prodMap (locGL E b w))) (fun m hm => ?_) (hU.preimage hc)
  exact funext fun x => hG _ hm x

omit [IsCMField E] in
theorem mu_one {a b : ℕ} {μ : HChar E} {w : Pl E} (h : μ.UnrAt w) (m : GLw a w × GLw b w) (h1 : m.1 ∈ GlobalTheory.LFun.KGL w a)
    (h2 : m.2 ∈ GlobalTheory.LFun.KGL w b) (k l : ℕ) : μ.loc w (GeneralLinearGroup.det m.1 ^ k * GeneralLinearGroup.det m.2 ^ l) = 1 := by
  rw [map_mul, map_pow, map_pow, h _ (GlobalTheory.SphGal.isUnitAt_det_of_mem h1), h _ (GlobalTheory.SphGal.isUnitAt_det_of_mem h2), one_pow,
    one_pow, one_mul]

set_option maxHeartbeats 1600000 in
theorem candLev_of (h0 : Tail.ReadLev) (h1 : Tail.ReadT) (h2 : Tail.ExpRead) (h3 : RS.JoinSat) : CandLev := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  obtain ⟨hS0, hBad, hμ, hϖ, hK', hX, hL, hfix, hKB⟩ := F.same
  have hRS : ∀ u ∈ F₀.d₀.S₀ ∪ F₀.d₀.Bad, u ∈ F₀.Sec := fun u hu =>
    (Finset.mem_union.1 hu).elim (fun a => (F₀.S₀ u a).1) fun a => (F₀.bad u a).1
  have hgoodK : ∀ u ∈ F₀.Sec, u ∉ F₀.d₀.S₀ ∪ F₀.d₀.Bad → ∀ v : Pl E,
      v.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) → F₀.K v = GlobalTheory.LFun.KGL v n := by
    intro u hu hu' v hv
    refine F₀.K_good v fun t ht e => hu' ?_
    have : t = u := (F₀.hSec u).unique ⟨hRS t ht, e.trans hv⟩ ⟨hu, rfl⟩
    exact this ▸ ht
  have hTR : ∀ u ∈ F.d.T, u ∉ F₀.d₀.S₀ ∪ F₀.d₀.Bad := fun u hu h => by
    rw [← hS0, ← hBad] at h
    exact (Finset.mem_union.1 h).elim (Finset.disjoint_left.1 F.ok.disj.1 hu) (Finset.disjoint_left.1 F.ok.disj.2.1 hu)
  by_cases hT : w ∈ F.d.T
  · obtain ⟨B, hB, -⟩ := inert_d h1 h2 h3 hR E hE n π S T F₀ F i s₁ s₂ Pa Pb D A G hc hG hl hne w hT
    rw [hgoodK w (F.T_in w hT).1 (hTR w hT) w rfl]
    exact satSph E n D w B hB
  obtain ⟨j, hj⟩ : ∃ j, G j ≠ 0 := by
    by_contra h
    have e : G = 0 := funext fun j => by_contra fun h' => h ⟨j, h'⟩
    refine hne ?_
    rw [e]
    refine Function.iterate_fixed ?_ _
    funext p x
    simp [convF]
  refine h0 E n _ _ (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F₀.K w) (stab w (G j)) (G j) (F₀.hK.1 w) (F₀.Kc w)
    (stab_open w (hl j).1) (fun m X hm => ?_) (hG j) hj (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hk)
  by_cases hw : w ∈ F₀.Sec
  · have hf := GlobalTheory.LGrp.mem_fixed.1 ((hl j).2 w hw).1
    by_cases hR' : w ∈ F₀.d₀.S₀ ∪ F₀.d₀.Bad
    · obtain ⟨a1, a2⟩ := F₀.K_bad _ ha w hR' m X hm
      refine ⟨hf m ?_, a2⟩
      rw [LocOk.lev_S F.d hT (by rw [hS0, hBad]; exact hR'), hL]
      exact a1
    · rw [hgoodK w hw hR' w rfl] at hm
      obtain ⟨b1, b2⟩ := Tail.B.blocks_of_blk_mem _ w m X hm
      rw [Finset.mem_union, not_or] at hR'
      refine ⟨hf m ?_, mu_one (F₀.good w hw hR'.1 hR'.2).2 m b1 b2 _ _⟩
      rw [LocOk.lev_out F.d hT (by rw [hS0, hBad, Finset.mem_union, not_or]; exact hR')]
      exact ⟨b1, b2⟩
  · obtain ⟨u, ⟨hu, hu'⟩, -⟩ := F₀.hSec w
    have hne' : w ≠ u := fun e => hw (e ▸ hu)
    have hus : IsSplitAt u := ⟨w, hne', hu'.symm⟩
    have hcj : ConjPl u w := ⟨hu'.symm, Or.inl hne'⟩
    have hf := ((hl j).2 u hu).2 hus
    by_cases hR' : u ∈ F₀.d₀.S₀ ∪ F₀.d₀.Bad
    · obtain ⟨a1, m', a2, a3, a4⟩ := F₀.K_conj _ ha u hR' hus w hcj m X hm
      refine ⟨?_, a1⟩
      have hm' : m' ∈ F.d.lev₂ (F₀.C.a i) u := by
        rw [LocData.lev₂, if_pos (by rw [hS0, hBad]; exact hR'), hL]
        exact a2
      have e := GlobalTheory.LGrp.mem_fixed.1 hf m' hm'
      show (rightReg ℂ _ ℂ) (embW _ w m.1, embW _ w m.2) (G j) = G j
      rw [a3, a4]
      exact e
    · rw [hgoodK u hu hR' w hu'.symm] at hm
      obtain ⟨b1, b2⟩ := Tail.B.blocks_of_blk_mem _ w m X hm
      rw [LocOk.lev₂_out F.d (by rw [hS0, hBad]; exact hR')] at hf
      rw [Finset.mem_union, not_or] at hR'
      have hun := ((RS.muLoc_holds' E hE F₀.μ F₀.e u F₀.hμ (F₀.good u hu hR'.1 hR'.2).2).2.2 w hus hcj).1
      exact ⟨GlobalTheory.LGrp.mem_fixed.1 ((FG.conjFix_holds E _ _).1 u w (G j) hus hcj hf) m ⟨b1, b2⟩, mu_one hun m b1 b2 _ _⟩

end PositivityTheory.Rg.BcB.F.PCandLh

end
end
