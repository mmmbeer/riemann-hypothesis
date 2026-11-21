import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Transfer

theorem af_ext'' {D : D7} {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

theorem latO_signs : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, ∃ ε : ℂ, ε * ε = 1 ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → heisO ψ S T x f = ε • f := by
  intro D r k _ _ _ _ p P hinj hmem ψ hψ S T LS LT hS hT x hx
  have hΛ : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
      ∀ u' ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
        ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P u (GlobalTheory.FinPl.LatMem.latO_mxAt hu)).1 hu u' hu'
  let G := GlobalTheory.LatVac.signGroup ψ _ hΛ
    (IsLatVac (heisO ψ S T) (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P))
  have half : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, IsHalf e u → u ∈ G :=
    fun e he u hu hh => ⟨hu, 1, one_mul _, fun f hf => by rw [hf.2 e he u hu hh, one_smul]⟩
  have splitC : ∀ e, IsSplitIdem D e → IsSplitIdem D (cA D e) := by
    rintro e ⟨he1, he2, v, ε, hpl, he3⟩
    exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
      by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩
  have hsub : ∀ i, latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
    intro i
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hs, rest⟩
    exact ⟨α, hα, fun v hv => hs v fun h => hv ((hmem v).2 ⟨i, h.symm⟩), rest⟩
  have piece : ∀ i, ∀ w ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v),
      w ∈ G := by
    intro i w hw
    obtain ⟨h1, h2⟩ := GlobalTheory.SplitVac.idem_latO D (k i) (p i) S T LS LT w hw
    have he := (p i).split
    have hee : (p i).e * (p i).e = (p i).e := he.1
    have hz : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) = w - Matrix.of fun a b => (p i).e * w a b := by
      ext a b
      rw [Matrix.of_apply, Matrix.sub_apply, Matrix.of_apply, eq_sub_iff_add_eq', ← add_mul, h2]
    have hyG : (Matrix.of fun a b => (p i).e * w a b : WO S T) ∈ G :=
      half _ he _ (hsub i h1) fun a b => by rw [Matrix.of_apply, ← mul_assoc, hee]
    have hzG : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) ∈ G := by
      refine half _ (splitC _ he) _ ?_ fun a b => ?_
      · rw [hz]; exact sub_mem (hsub i hw) (hsub i h1)
      · rw [Matrix.of_apply, ← mul_assoc, ← RingHom.map_mul, hee]
    rw [hz] at hzG
    simpa using add_mem hyG hzG
  have hxG : x ∈ G := by
    induction hx using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have hdec : α = ∑ i : Fin r, GlobalTheory.FinPl.LatMem.indP D.host.F (· = (p i).v) * α := by
        apply af_ext''
        intro v
        rw [map_sum]
        simp only [map_mul, GlobalTheory.FinPl.LatMem.evalV_indP]
        by_cases hv : P v
        · obtain ⟨i, rfl⟩ := (hmem v).1 hv
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            rw [if_neg (fun h => hj (hinj h).symm), zero_mul]
          · intro h
            exact absurd (Finset.mem_univ i) h
        · rw [hsupp v hv]
          simp
      rw [hdec]
      refine Finset.sum_induction _ (fun β : Af D.host.F => (Matrix.of fun i j =>
          (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) ∈ G)
        (fun β γ hβ hγ => ?_) ?_ (fun i _ => ?_)
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (β + γ)) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
            WO S T) = (Matrix.of fun i j => (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) +
            Matrix.of fun i j => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
          ext i j
          rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, GlobalTheory.LatVac.pair_add,
            TensorProduct.add_tmul]
        rw [e]
        exact add_mem hβ hγ
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (0 : Af D.host.F)) ⊗ₜ[D.host.F]
            (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) = 0 := by
          ext i j
          rw [Matrix.of_apply, Matrix.zero_apply]
          exact TensorProduct.zero_tmul _ _
        rw [e]
        exact zero_mem _
      · refine piece i _ (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf
          (GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' D.host.F _) hα, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩)
        rw [map_mul, GlobalTheory.FinPl.LatMem.indicatorAdele_supported D.host.F _ v hv, zero_mul]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  obtain ⟨-, ε, hε, h⟩ := hxG
  exact ⟨ε, hε, fun f hf => h f hf.2⟩

def heisLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T x
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply]
    ring
  map_smul' c f := GlobalTheory.LatVac.heisO_smul ψ x c f

def suppGrp {D : D7} (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) : AddSubgroup (WO S T) where
  carrier := {x | GlobalTheory.FinPl.MxAt P x}
  zero_mem' := fun _ _ => zero_mem (GlobalTheory.FinPl.idAt D P)
  add_mem' := fun hx hy i j => add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => neg_mem (hx i j)

theorem heis_comm {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x γ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T γ (heisO ψ S T x f) = ψ (symplO S T γ x) • heisO ψ S T x (heisO ψ S T γ f) := by
  rw [GlobalTheory.LatVac.heisO_heisO, GlobalTheory.LatVac.heisO_heisO, smul_smul, add_comm x γ, ← AddChar.map_add_eq_mul,
    ← GlobalTheory.ZeroOrInv.symplOH_two S T γ x]
  have h : symplOH S T γ x + symplOH S T x γ = 0 := by
    have h1 := GlobalTheory.ZeroOrInv.symplO_skew' S T γ x
    unfold symplOH
    rw [h1, mul_neg, add_neg_cancel]
  rw [add_assoc, h, add_zero]

theorem comb_sub {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c₁ c₂ : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    ∑ x ∈ (c₁ - c₂).support, (c₁ - c₂) x • heisLin ψ S T x f = comb ψ S T c₁ f - comb ψ S T c₂ f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    ← Finsupp.sum_sub_index (fun a b₁ b₂ => sub_smul b₁ b₂ (heisO ψ S T a f))]
  rfl

theorem comb_eq_on_vacua : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ c₁ c₂ : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P c₁ → GlobalTheory.FinPl.CombAt P c₂ → ∀ f₀, GlobalTheory.FinPl.Vac ψ S T LS LT P f₀ → f₀ ≠ 0 → comb ψ S T c₁ f₀ = comb ψ S T c₂ f₀ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → comb ψ S T c₁ f = comb ψ S T c₂ f := by
  intro D r k _ _ _ _ q P hinj hmem ψ hψ S T LS LT hS hT c₁ c₂ h₁ h₂ f₀ hf₀ hne heq f hf
  let Γ : AddSubgroup (WO S T) := latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P
  have hΓG : Γ ≤ suppGrp S T P := fun x hx => GlobalTheory.FinPl.LatMem.latO_mxAt hx
  have hex : ∀ γ : WO S T, ∃ s : ℂ, γ ∈ Γ →
      s ≠ 0 ∧ ∀ g ∈ {g | GlobalTheory.FinPl.Vac ψ S T LS LT P g}, heisLin ψ S T γ g = s • g := by
    intro γ
    by_cases hγ : γ ∈ Γ
    · obtain ⟨ε, hε, h⟩ := latO_signs D r k q P hinj hmem ψ hψ S T LS LT hS hT γ hγ
      exact ⟨ε, fun _ => ⟨left_ne_zero_of_mul_eq_one hε, h⟩⟩
    · exact ⟨1, fun h => absurd h hγ⟩
  choose aF haF using hex
  have hχ : ∀ x : WO S T, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, ψ (symplO S T γ (x + γ')) = ψ (symplO S T γ x) := by
    intro x γ hγ γ' hγ'
    rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul,
      (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P γ (hΓG hγ)).1 hγ γ' hγ', mul_one]
  have hsep : ∀ x ∈ suppGrp S T P, ∀ y ∈ suppGrp S T P, x - y ∉ Γ →
      ∃ γ ∈ Γ, ψ (symplO S T γ x) ≠ ψ (symplO S T γ y) := by
    intro x hx y hy h
    have hd : x - y ∈ suppGrp S T P := sub_mem hx hy
    rw [GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P (x - y) hd] at h
    push_neg at h
    obtain ⟨l, hl, hl'⟩ := h
    refine ⟨l, hl, fun he => hl' ?_⟩
    rw [← sub_add_cancel x y, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul] at he
    have h1 : ψ (symplO S T l (x - y)) = 1 :=
      mul_right_cancel₀ (GlobalTheory.ZeroOrInv.psi_ne_zero ψ _) (he.trans (one_mul _).symm)
    rw [GlobalTheory.ZeroOrInv.symplO_skew'] at h1
    exact GlobalTheory.ZeroOrInv.psi_eq_one_of_neg ψ h1
  have hJ : ∀ x ∈ (c₁ - c₂).support, x ∈ suppGrp S T P := by
    intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_sub hx) with h | h
    · exact h₁ x h
    · exact h₂ x h
  rcases GlobalTheory.isolate_abstract (WO S T) Γ (suppGrp S T P) (WO S T → ℂ) (heisLin ψ S T)
      {g | GlobalTheory.FinPl.Vac ψ S T LS LT P g} (fun x y => ψ (symplOH S T x y)) aF (fun x γ => ψ (symplO S T γ x)) hΓG
      (GlobalTheory.LatVac.heisO_zero ψ) (GlobalTheory.LatVac.heisO_heisO ψ) (fun _ _ => GlobalTheory.ZeroOrInv.psi_ne_zero ψ _)
      (fun γ hγ => haF γ hγ) (fun γ _ x v => heis_comm ψ S T x γ v) hχ hsep
      (c₁ - c₂).support (DFunLike.coe (c₁ - c₂)) hJ with h | ⟨κ, -, hinv⟩
  · have h0 := h f hf
    rwa [comb_sub, sub_eq_zero] at h0
  · have h0 := hinv f₀ hf₀
    rw [comb_sub, heq, sub_self] at h0
    simp only [map_zero, smul_zero, Finset.sum_const_zero] at h0
    exact absurd h0.symm hne

end GlobalTheory.FinPl.Transfer

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_eq_on_vacua_of_eq_one : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ c₁ c₂ : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P c₁ → GlobalTheory.FinPl.CombAt P c₂ → ∀ f₀, GlobalTheory.FinPl.Vac ψ S T LS LT P f₀ → f₀ ≠ 0 → comb ψ S T c₁ f₀ = comb ψ S T c₂ f₀ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → comb ψ S T c₁ f = comb ψ S T c₂ f := by
  atlas_forward_decl GlobalTheory.FinPl.Transfer.comb_eq_on_vacua
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FunObj.Comparison₂ (IsRed Compat IsIx)

namespace GlobalTheory.QTw.LocFn

section Red

variable {S F K : Type} [CommRing S] [CommRing F] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* F} {ψ : S →+* K}

theorem parPhi_eq_of_equiv (h : IsRed φ ψ) {R : Type} [Fintype R] [DecidableEq R] {r t j j' a b : ℕ} (f : Fin r ≃ R)
    {ea : Ix R (Fin t) j ≃ Fin a} {eb : Ix R (Fin t) j' ≃ Fin b}
    (ha : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j × Fin t))).trans ea))
    (hb : IsIx ((Equiv.sumCongr f (Equiv.refl (Fin j' × Fin t))).trans eb))
    {c : Fˣ →* ℂˣ} {δ : Kˣ →* ℂˣ} (hc : Compat φ ψ c δ⁻¹) (N : Matrix (Fin b) (Fin a) S) :
    parPhi δ ((N.map ψ).submatrix eb ea) =
      if H : LowZero r (N.map φ) ∧ IsUnit (topL r (N.map φ)).det then (c H.2.unit : ℂ) else 0 := by
  have e1 : (topL r (N.map φ)).det = ((N.submatrix eb ea).toBlocks₁₁.map φ).det := by
    rw [GlobalTheory.FunObj.Comparison₂.topL_r ha hb, ← det_submatrix_equiv_self f]
    rfl
  have e2 : LowZero r (N.map φ) ↔ MaxM ((N.map ψ).submatrix eb ea).toBlocks₂₁ :=
    (GlobalTheory.FunObj.Comparison₂.lowZero_r h ha hb N).trans
      ⟨fun H i l => by
        obtain ⟨l, rfl⟩ := f.surjective l
        exact H i l, fun H i l => H i (f l)⟩
  split_ifs with H
  · obtain ⟨g, hg, e⟩ := (h.isUnit_det_iff _).1 (e1 ▸ H.2)
    rw [parPhi_of_mem (x := (N.map ψ).submatrix eb ea) _ hg e (e2.1 H.1) (fun _ _ => h.int _) (fun _ _ => h.int _),
      hc.det (k := Matrix.GeneralLinearGroup.det g) _ (H.2.unit_spec.trans e1) (congrArg Matrix.det e),
      MonoidHom.inv_apply]
  · by_contra h0
    obtain ⟨h1, h2, -⟩ := (parPhi_ne_zero_iff _).1 h0
    exact H ⟨e2.2 h2, e1 ▸ (h.isUnit_det_iff _).2 h1⟩

theorem tame_congr {δ : Kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Kˣ} (hx : valuation K (x : K) = 1)
    (h : valuation K ((x : K) - y) < 1) : δ y = δ x := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  refine hδ _ ?_
  rwa [Units.val_mul, Units.val_inv_eq_inv_val, ← mul_inv_cancel₀ x.ne_zero, ← sub_mul, map_mul, map_inv₀, hx, inv_one,
    mul_one, Valuation.map_sub_swap]

end Red

theorem isIx_of_isOrd {κ l r t j a : ℕ} (h : κ + l = r) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) :
    IsIx ((Equiv.sumCongr (finSumFinEquiv.trans (finCongr h)).symm (Equiv.refl (Fin j × Fin t))).trans e) := by
  refine ⟨?_, fun i => ?_, fun c s => ?_⟩
  · simpa [h] using (Fintype.card_congr e).symm
  · obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective i
    rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_apply_apply, he]
    rcases i with i | i <;> rfl
  · refine (he (.inr (c, s))).trans ?_
    change κ + l + c.val * t + s.val = _
    rw [h, mul_comm]; omega

theorem parPhi_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : EAf D →+* k), (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (δ : kˣ →* ℂˣ), IsTame δ → ∀ (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), (∀ (z : 𝓞 D.host.E) (x : kˣ) (u : (Formalism.L2.DIV.kP PP)ˣ), (x : k) = (ofSplit q).pr (z : D.host.E) → (u : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ u)⁻¹) → ∀ (κ l r t j j' a b : ℕ), r = κ + l → ∀ (ea : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) (eb : Ix (Fin κ ⊕ Fin l) (Fin t) j' ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), parPhi δ ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = if H : LowZero r (N.map (Formalism.L2.DIV.resS D.host.F PP)) ∧ IsUnit (topL r (N.map (Formalism.L2.DIV.resS D.host.F PP))).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0 := by
  intro D k _ _ _ _ q PP π' hπ hred δ hδ ξ hξ κ l r t j j' a b hr ea eb ha hb N
  refine parPhi_eq_of_equiv hred _ (isIx_of_isOrd hr.symm ha) (isIx_of_isOrd hr.symm hb) (fun s u x hu hx => ?_) N
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
      (ofSplit q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have h2 : valuation k ((x : k) - (ofSplit q).pr (z : D.host.E)) < 1 := by
    rw [hx, ← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
    exact (hz.trans hu).symm
  have h3 : valuation k (x : k) = 1 := by
    rw [hx]; exact (hred.isUnit_iff s).1 (hu ▸ u.isUnit)
  have h4 : (ofSplit q).pr (z : D.host.E) ≠ 0 := fun h => by
    rw [h, sub_zero, h3] at h2
    exact lt_irrefl _ h2
  rw [MonoidHom.inv_apply, ← tame_congr hδ (y := Units.mk0 _ h4) h3 h2, hξ z (Units.mk0 _ h4) u rfl hz.symm, inv_inv]

end GlobalTheory.QTw.LocFn

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : EAf D →+* k), (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (δ : kˣ →* ℂˣ), IsTame δ → ∀ (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), (∀ (z : 𝓞 D.host.E) (x : kˣ) (u : (Formalism.L2.DIV.kP PP)ˣ), (x : k) = (ofSplit q).pr (z : D.host.E) → (u : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ u)⁻¹) → ∀ (κ l r t j j' a b : ℕ), r = κ + l → ∀ (ea : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) (eb : Ix (Fin κ ⊕ Fin l) (Fin t) j' ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), parPhi δ ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = if H : LowZero r (N.map (Formalism.L2.DIV.resS D.host.F PP)) ∧ IsUnit (topL r (N.map (Formalism.L2.DIV.resS D.host.F PP))).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0 := by
  atlas_forward_decl GlobalTheory.QTw.LocFn.parPhi_component
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FrameBack

theorem idAt_of_place {D : D7} (P : Pl D → Prop) (v : Pl D) (hv : P v) {a : AE D} (h : a ∈ idAt D (· = v)) :
    a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h ⊢
  exact ⟨h.1, fun w => h.2 ⟨w.1, fun hw => w.2 (hw ▸ hv)⟩⟩

theorem mem_latV_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (P : Pl D → Prop)
    (v : Pl D) (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (hw ▸ hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => idAt_of_place P v hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem mul_sec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (a : AE D) (x : k) : a * q.sec x = q.sec (q.pr a * x) := by
  have h : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
  have h2 := q.sec_pr (a * q.sec x)
  rw [map_mul, q.pr_sec, mul_left_comm, h] at h2
  exact h2.symm

theorem frame_back : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) (L N : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop), P q.v → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V g L N P → ∀ (Y : Type) [Fintype Y] (β β' : Matrix (Fin V.rank) Y k), β = (Formalism.L2.Theta.mt V g).map q.pr * β' → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V N (· = q.v)) → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β' *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v) := by
  intro D k _ _ _ _ q V g L N P hP hL hN hM Y _ β β' hβ hb y
  have hmv : Formalism.L2.Theta.mt V g *ᵥ (fun i => q.sec ((β' *ᵥ y) i)) = fun i => q.sec ((β *ᵥ y) i) := by
    funext i
    rw [hβ, ← Matrix.mulVec_mulVec]
    generalize β' *ᵥ y = z
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, mul_sec]
  have hu : ∀ i, (fun i => q.sec ((β' *ᵥ y) i)) i ∈ idAt D (· = q.v) := fun i => q.sec_mem_idAt _
  have hu' : ∀ i, (fun i => q.sec ((β *ᵥ y) i)) i ∈ idAt D (· = q.v) := fun i => q.sec_mem_idAt _
  rw [hb y, ← mem_latV_iff V N hN.1 P q.v hP _ hu', ← mem_latV_iff V L hL.1 P q.v hP _ hu,
    hM _ (fun i => idAt_of_place P q.v hP (hu i)), hmv]

end GlobalTheory.FinPl.FrameBack
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceFrame_movedBack_isLatticeBasis : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) (L N : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop), P q.v → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V g L N P → ∀ (Y : Type) [Fintype Y] (β β' : Matrix (Fin V.rank) Y k), β = (Formalism.L2.Theta.mt V g).map q.pr * β' → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V N (· = q.v)) → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β' *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v) := by
  atlas_forward_decl GlobalTheory.FinPl.FrameBack.frame_back
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacUnion

variable {D : D7}

open Classical in

def idemF (v : Pl D) : Af D.host.F :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    show (if w = v then (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.F w) else 0) ∈ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem evalV_idemF (v w : Pl D) : evalV D.host.F w (idemF v) = if w = v then 1 else 0 := rfl

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [mul_zero]

def idemE (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (pairA _ 0 (idemF v))

theorem idemE_mul_gen (v : Pl D) (α : Af D.host.F) (x : D.host.E) :
    idemE v * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x := by
  rw [idemE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, pairA_mul]

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idemE_smul_gen (v : Pl D) (α : Af D.host.F) (x : Fin T.rank → Fin S.rank → D.host.E) :
    idemE v • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
      Matrix.of fun i j => pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x i j := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.of_apply, idemE_mul_gen]

theorem idemE_smul_mem (v : Pl D) {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    idemE v • u ∈ latO S T LS LT (· = v) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    have hα' : ∀ w, evalV D.host.F w α ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F w := hα
    have hmem : idemF v * α ∈ intAf D.host.F := by
      simp only [intAf, Set.mem_setOf_eq]
      intro w
      rw [map_mul]
      refine mul_mem ?_ (hα' w)
      rw [evalV_idemF]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine ⟨idemF v * α, hmem, fun w hw => ?_, a, ha, s, hs, t, ht, idemE_smul_gen v α _⟩
    rw [map_mul, evalV_idemF, if_neg hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.VacUnion
end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def frameAt {N : ℕ} (π' : EAf D →+* k) (β : GL (Fin N) (EAf D)) : GlobalTheory.LocMod.Frame k N (Fin N) where
  β := β.val.map π'
  γ := (β⁻¹).val.map π'
  βγ := by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  γβ := by rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

variable {S T : HSp D} (q : GlobalTheory.FinPl.SplitPt D k) {π' : EAf D →+* k}
  (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem down_eq (hπ : ∀ a, π' (toEAf D a) = q.pr a) (x : WO S T) :
    (ofSplit q).down (frameAt π' βS) (frameAt π' βT) x = (frMapO S T βS βT x).map π' := by
  have h2 : ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map π' = x.map q.pr := Matrix.ext fun i j => hπ _
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h2]
  rfl

theorem up_down {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = p.e • t := by
  unfold Place.up Place.down
  have : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ = t.map p.π := by
    simp only [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [this]
  exact Matrix.ext fun i j => p.ι_π _

theorem down_up {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  unfold Place.up Place.down
  have : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ :=
    Matrix.ext fun i j => p.π_ι _
  rw [this]
  simp only [← Matrix.mul_assoc, FT.γβ, Matrix.one_mul]
  rw [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem frMapO_smul (a : AE D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) :
    frMapO S T βS βT (a • x) i j = toEAf D a * frMapO S T βS βT x i j := by
  have : (a • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D a • x.map (toEAf D) :=
    Matrix.ext fun i j => (toEAf D).map_mul _ _
  exact (congrArg (fun z => GlobalTheory.FunObj.Comparison₂.fr βT βS z i j) this).trans
    (congrFun (congrFun (GlobalTheory.FunObj.Comparison₂.fr_smul βT βS _ _) i) j)

theorem smul_mem_at {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {x : WO S T}
    (hx : x ∈ latO S T LS LT fun _ => True) : q.e • x ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, hε, h⟩ := q.above
  have h1 : IsPlaceIdem D q.v (pairA _ 0 (GlobalTheory.VacUnion.idemF q.v)) :=
    ⟨_, rfl, by rw [GlobalTheory.VacUnion.evalV_idemF, if_pos rfl], fun w hw => by rw [GlobalTheory.VacUnion.evalV_idemF, if_neg hw]⟩
  have h2 : GlobalTheory.VacUnion.idemE q.v = q.e + cA D q.e := by
    rw [h, GlobalTheory.IdemSupport.placeIdem_unique hε h1]; rfl
  have h3 := GlobalTheory.VacUnion.idemE_smul_mem q.v (GlobalTheory.PlaceModelSum.idem_smul_latO q.split.1 hx)
  have h4 : GlobalTheory.VacUnion.idemE q.v * q.e = q.e := by
    rw [h2]
    linear_combination q.split.1 + q.split.2.1
  rwa [smul_smul, h4] at h3

theorem latO_le_top {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} : latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, k⟩ => ⟨α, hα, fun _ hw => (hw trivial).elim, k⟩

theorem eq_sum {r : ℕ} {a : Fin r → AE D} {pl : Fin r → Formalism.L2.DIV.Pl D.host.E} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D}
    (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i)) (hinj : Function.Injective pl) (hQ : ∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP)
    (he : IsIdemSum e Q) : e = ∑ i, a i := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  refine (Finset.sum_bij (fun i _ => pl i) (fun i _ => (hQ _).2 ⟨i, rfl⟩) (fun i _ j _ h => hinj h)
    (fun PP hPP => by obtain ⟨i, hi⟩ := (hQ PP).1 hPP; exact ⟨i, Finset.mem_univ _, hi⟩) fun i _ => ?_).symm
  exact GlobalTheory.IdemSupport.delta_unique hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (ha i))
    (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (h1 _ ((hQ _).2 ⟨i, rfl⟩)))

theorem isIntM_iff_mem_latO : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) → (∀ i, (q i).UnitAA) → Function.Injective pl → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → IsIdemSum e Q → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), (∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) → (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S LS (· = (q i).v)) ∧ ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T LT (· = (q i).v)) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D r k _ _ _ _ q pl Q e hq hu hinj hQ he S T LS LT hS hT βS βT hβ x hx
  choose π' hπ hrest using fun i => GlobalTheory.FinPl.SplitPt.exists_lift_isRed D (k i) (q i) (pl i) (hq i)
  have hint := fun i => (hrest i).2.1
  have he' : e = ∑ i, (q i).e := eq_sum hq hinj hQ he
  have hxe : e • x = x := Matrix.ext fun i j => hx i j
  constructor
  · intro h
    rw [← hxe, he', Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have h1 := GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
      (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 ((frMapO S T βS βT x).map (π' i)) fun a b => ((hint i _).1 (h a b)).2
    rw [← down_eq (q i) βS βT (hπ i), up_down] at h1
    exact latO_le_top h1
  · intro h a b
    rw [← hxe, frMapO_smul, he', GlobalTheory.FunObj.Comparison₂.hom_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => (hint i _).2 ⟨?_, ?_⟩
    · rw [← mul_assoc, sub_mul, one_mul, ← RingHom.map_mul, (q i).split.1, sub_self, zero_mul]
      exact zero_mem _
    · obtain ⟨y, hy, h1⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
        (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 _ (smul_mem_at (q i) h)
        (fun a b => by
          change (q i).e * ((q i).e * _) = (q i).e * _
          rw [← mul_assoc, (q i).split.1])
      have h2 := down_eq (q i) βS βT (hπ i) ((q i).e • x)
      rw [h1, down_up, ← h1] at h2
      rw [← frMapO_smul]
      have h3 := hy a b
      rw [h2] at h3
      exact h3

end GlobalTheory.HalfInt

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrameMatrix_iff_mem_splitHalfHomLattice : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) → (∀ i, (q i).UnitAA) → Function.Injective pl → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → IsIdemSum e Q → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), (∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) → (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S LS (· = (q i).v)) ∧ ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T LT (· = (q i).v)) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  atlas_forward_decl GlobalTheory.HalfInt.isIntM_iff_mem_latO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ConvDistinct

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ι : Type) (v : ι → GlobalTheory.FinPl.Pl D) (c : ι → WO S T →₀ ℂ), Function.Injective v → (∀ i, GlobalTheory.FinPl.CombAt (· = v i) (c i)) → ∀ L : List ι, L.Nodup → GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) ∧ ∀ f, comb ψ S T (aconv (L.map c)) f = L.foldr (fun i g => comb ψ S T (c i) g) f := by
  intro D ψ S T ι v c hv hc L
  have hsupp : ∀ L : List ι, GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) := by
    intro L
    refine GlobalTheory.QFinLaw.combAt_aconv _ (L.map c) (fun e he => ?_)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun p hp => ⟨b, hb, hp.symm⟩) (hc b u hu)
  intro hL
  refine ⟨hsupp L, fun f => ?_⟩
  induction L with
  | nil => exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    rw [List.map_cons, GlobalTheory.QFinLaw.comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = v a)) (P' := fun p => ∃ b ∈ L, v b = p) ?_ (hc a x hx) (hsupp L y hy)
    rintro _ rfl ⟨b, hb, hab⟩
    exact (List.nodup_cons.1 hL).1 (hv hab ▸ hb)

end GlobalTheory.ConvDistinct
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.listConvolution_distinctPlaces_supported_and_composition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ι : Type) (v : ι → GlobalTheory.FinPl.Pl D) (c : ι → WO S T →₀ ℂ), Function.Injective v → (∀ i, GlobalTheory.FinPl.CombAt (· = v i) (c i)) → ∀ L : List ι, L.Nodup → GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) ∧ ∀ f, comb ψ S T (aconv (L.map c)) f = L.foldr (fun i g => comb ψ S T (c i) g) f := by
  atlas_forward_decl GlobalTheory.ConvDistinct.main
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_baseEq_of_same_idempotentPrime : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → Formalism.L2.NTheta.IsIdemAt q'.e PP → q.v = q'.v := by
  first | exact @GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt | exact GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt | (intros; apply GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QVec
open GlobalTheory.LocMod.StepVec
open Formalism.L2.DIV (kP resS)

variable {D : D7} {S T : HSp D}

def datum (e : AE D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (om : (∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP w)) → ℂ) : WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then om (fun w => redM w (frMapO S T βS βT x)) else 0

section One
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem model (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {w : Formalism.L2.DIV.Pl D.host.E} (hw : w ∈ P) (hq : Formalism.L2.NTheta.IsIdemAt q.e w) {π' : EAf D →+* k}
    (hint : ∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k])
    (hres : ∀ w' : Formalism.L2.DIV.Pl D.host.E, w' ≠ w → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      resS D.host.F w' ⟨(1 - toEAf D q.e) * z, hz'⟩ = resS D.host.F w' ⟨z, hz⟩)
    (W : (∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP w)) → ℂ)
    (hW : ∀ y y', (∀ w' ∈ P.erase w, y w' = y' w') → W y = W y')
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) :
    ∃ T₁, (ofSplit q).IsModel ψ FS FT T₁ ∧ ∀ om (Φ₀ : Matrix (Fin T.rank) (Fin S.rank) k → ℂ),
      (∀ z, Φ₀ z ≠ 0 → ∀ i j, z i j ∈ 𝒪[k]) →
      (∀ N, IsIntM N → om (fun w => redM w N) = Φ₀ (N.map π') * W fun w => redM w N) → ∀ Φ : SB (Matrix Y Y' k),
      (∀ x, Φ.1 ((ofSplit q).down FS FT x) = Φ₀ ((frMapO S T βS βT x).map π')) → Tm (datum e βS βT om) = T₁ Φ := by
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hqe := idem_mul he hw hq
  have hinf' : infPart D (e - q.e) = 0 := by
    rw [← hqe, RingHom.map_sub, RingHom.map_mul, hinf, mul_zero, sub_zero]
  have hΩ := GlobalTheory.PlaceDatum.isSBHalf_of_red (e - q.e) (latO S T ΛS ΛT fun _ => True) (frMapO S T βS βT)
    (GlobalTheory.PlaceDatum.frMapO_add βS βT) (GlobalTheory.PlaceDatum.exists_den_frMapO hS.fg hT.fg βS βT)
    (by
      obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hS hT βS βT
      exact ⟨K, hK, fun t ht => h t (GlobalTheory.PlaceDatum.infPart_of_half hinf' ht)⟩) (P.erase w) W hW
  refine ⟨_, isModel_extend (ofSplit q) FS FT hqe hTm
    (GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hS hT hee he.2 hinf hf₀ Tm hTm) _
    (GlobalTheory.T.isSchwartzBruhatHalf_splitPlace_product D k q Y Y' S T FS FT ΛS ΛT hS hT e hee hqe _ hΩ), fun om Φ₀ h0 h1 Φ hΦ => ?_⟩
  refine congrArg Tm (funext fun x => ?_)
  rw [extend_apply, hΦ]
  have h3 : ∀ i j, frMapO S T βS βT ((1 - q.e) • x) i j = (1 - toEAf D q.e) * frMapO S T βS βT x i j :=
    fun i j => by rw [frMapO_smul, RingHom.map_sub, RingHom.map_one]
  have h4 : IsIntM (frMapO S T βS βT x) → IsIntM (frMapO S T βS βT ((1 - q.e) • x)) := fun hi i j => by
    rw [h3]; exact ((hint _).1 (hi i j)).1
  have h6 : Φ₀ ((frMapO S T βS βT x).map π') ≠ 0 → IsIntM (frMapO S T βS βT ((1 - q.e) • x)) → IsIntM (frMapO S T βS βT x) :=
    fun h5 h6 i j => (hint _).2 ⟨by rw [← h3]; exact h6 i j, h0 _ h5 i j⟩
  have h2 : IsHalf e x → IsHalf (e - q.e) ((1 - q.e) • x) := fun hx i j => idempotent_sub_mul_complement_eq_complement (hx i j) q.split.1 hqe
  exact ite_and_eq_ite_mul_ite_of_implications h4 (h1 _) (fun hi => hW _ _ fun w' hw' => redM_eq hi (h4 hi) h3 (hres w' (Finset.ne_of_mem_erase hw'))) h6 h2

end One

def Puts (ψ : AddChar (AF D.host.F) ℂ) (A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (e : AE D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (w : Formalism.L2.DIV.Pl D.host.E)
    (loc : Matrix (Fin T.rank) (Fin S.rank) (kP w) → ℂ) (c : WO S T →₀ ℂ) : Prop :=
  ∀ W : (∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP w)) → ℂ,
    (∀ y y', (∀ w' ∈ P.erase w, y w' = y' w') → W y = W y') →
    A (datum e βS βT fun y => loc (y w) * W y) = comb ψ S T c (A (datum e βS βT W))

section Two
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem puts (q : GlobalTheory.FinPl.SplitPt D k) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {χS χT} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {w : Formalism.L2.DIV.Pl D.host.E} (hw : w ∈ P) (hq : Formalism.L2.NTheta.IsIdemAt q.e w)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (ea : ι' ≃ Fin S.rank) (eb : ι ≃ Fin T.rank)
    (Φι : Matrix ι ι' k → ℂ) (h0 : ∀ z, Φι z ≠ 0 → ∀ i j, z i j ∈ 𝒪[k]) (loc : Matrix (Fin T.rank) (Fin S.rank) (kP w) → ℂ)
    (h1 : ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) →
      GlobalTheory.FunObj.Comparison₂.IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) →
      ∀ N : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
      Φι ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = loc (N.map (resS D.host.F w)))
    (GS : Frame k S.rank Y') (GT : Frame k T.rank Y) (oS : ι' ≃ Y') (oT : ι ≃ Y) (g : GA D S) (h : GA D T)
    (mS : MovedTo (ofSplit q) S g βS (GS.β.submatrix id fun i => oS (ea.symm i)))
    (mT : MovedTo (ofSplit q) T h βT (GT.β.submatrix id fun i => oT (eb.symm i)))
    {Ξ : Matrix Y Y' k → ℂ} (hΞ : Ξ ∈ SB (Matrix Y Y' k))
    (hΞ' : Ξ = (⟨oT, 1⟩ : LatFrame k ι Y).transport (⟨oS, 1⟩ : LatFrame k ι' Y') Φι)
    {c : WO S T →₀ ℂ} (hc : (ofSplit q).IsCombAt ψ GS GT c Ξ) :
    Puts ψ (om (g, h) ∘ₗ Tm) e βS βT P w loc c := by
  intro W hW
  obtain ⟨π', hπ, hred, hint, hres⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q w hq
  obtain ⟨T₁, hT₁, hT'⟩ := model q (moved (ofSplit q) GS g⁻¹) (moved (ofSplit q) GT h⁻¹) hom.std hS hT βS βT he hw hq hint hres W hW
    hf₀ hTm
  obtain ⟨T₂, hT₂, hT''⟩ := GlobalTheory.T.isLocalModel_creation_weilAction_moved_frames D k (ofSplit q) Y Y' S T _ GS _ GT ψ θ _ _ om hθ hom g h
    (β_eq_moved _ GS g) (β_eq_moved _ GT h) 0 0 0 0 1 T₁ hT₁
  simp only [GlobalTheory.FiniteFock.pureTensorO_one] at hT''
  have hco := coords_down (ofSplit q) (moved (ofSplit q) GS g⁻¹) (moved (ofSplit q) GT h⁻¹) hπ
    (⟨oS, 1⟩ : LatFrame k ι' Y') (⟨oT, 1⟩ : LatFrame k ι Y) ea eb
    (map_eq_of_movedTo _ GS hπ 1 _ (by rw [Matrix.mul_one]; exact mS))
    (map_eq_of_movedTo _ GT hπ 1 _ (by rw [Matrix.mul_one]; exact mT))
  obtain ⟨O, hO⟩ := GlobalTheory.BiComb.exists_isOne (k := k) Y Y'
  have e1 := hT' (fun y => loc (y w) * W y) (fun z => Φι (z.submatrix eb ea))
    (fun z hz i j => by simpa using h0 _ hz (eb.symm i) (ea.symm j))
    (fun N hN => by
      beta_reduce
      rw [redM_eq_map w hN, ← h1 π' hπ hred]
      rfl) ⟨Ξ, hΞ⟩ (fun x => by rw [← hco x]; exact congrFun hΞ' _)
  have e2 := hT' W (fun z => if ∀ i j, z i j ∈ 𝒪[k] then 1 else 0)
    (fun z hz => by_contra fun h => hz (if_neg h))
    (fun N hN => by
      rw [if_pos (show ∀ i j, N.map π' i j ∈ 𝒪[k] from fun i j => ((hint _).1 (hN i j)).2), one_mul]) O (fun x => by
      have h5 := hco x
      simp only [LatFrame.coords, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at h5
      rw [hO, Set.indicator_apply]
      refine if_congr ⟨fun H i j => ?_, fun H i j => ?_⟩ rfl rfl
      · have h6 := congrFun (congrFun h5 (eb.symm i)) (ea.symm j)
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at h6
        rw [← h6]; exact H _ _
      · have h6 := congrFun (congrFun h5 (oT.symm i)) (oS.symm j)
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at h6
        rw [h6]; exact H _ _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, ← hT'', ← hT'']
  exact hc.2 T₂ hT₂ O _ hO rfl

end Two

def locQ {κ : Type} [CommRing κ] {a b : ℕ} (r : ℕ) (ξ : κˣ →* ℂˣ) (y : Matrix (Fin b) (Fin a) κ) : ℂ :=
  if H : LowZero r y ∧ IsUnit (topL r y).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0

theorem iterate {ψ : AddChar (AF D.host.F) ℂ} {A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D} {βS : GL (Fin S.rank) (EAf D)}
    {βT : GL (Fin T.rank) (EAf D)} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {ι : Type} {pl : ι → Formalism.L2.DIV.Pl D.host.E}
    (hpl : Function.Injective pl) (hP : ∀ i, pl i ∈ P) (loc : ∀ i, Matrix (Fin T.rank) (Fin S.rank) (kP (pl i)) → ℂ)
    (c : ι → WO S T →₀ ℂ) (h : ∀ i, Puts ψ A e βS βT P (pl i) (loc i) (c i)) (L : List ι) (hL : L.Nodup) :
    A (datum e βS βT fun y => (L.map fun i => loc i (y (pl i))).prod) =
      L.foldr (fun i g => comb ψ S T (c i) g) (A (datum e βS βT fun _ => 1)) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons, List.foldr_cons]
    rw [← ih hL.2]
    refine h i _ fun y y' hy => congrArg List.prod (List.map_congr_left fun i' hi' => ?_)
    rw [hy (pl i') (Finset.mem_erase.2 ⟨fun H => hL.1 (hpl H ▸ hi'), hP i'⟩)]

theorem omegaG_of_empty {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (hL : L.Pg = ∅) (χj)
    (y : ∀ w : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (kP w)) : omegaG L χj y = 1 := by
  haveI : IsEmpty L.Pg := ⟨fun w => Finset.notMem_empty w.1 (hL ▸ w.2)⟩
  rw [omegaG, dif_pos ⟨fun w hw => isEmptyElim (⟨w, hw⟩ : L.Pg), fun w => isEmptyElim w, fun w => isEmptyElim w,
    fun w => isEmptyElim w, by convert L.P.H.one_mem using 1⟩]
  rw [Fintype.prod_empty, Fintype.prod_empty, mul_one, mul_one, Subsingleton.elim (⟨_, _⟩ : L.P.H) 1, map_one, Units.val_one]

theorem om_comb {ψ : AddChar (AF D.host.F) ℂ} {χS χT} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) (g : GA D S) (h : GA D T)
    (c : WO S T →₀ ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (comb ψ S T (c.mapDomain (actO S T g⁻¹ h⁻¹)) f) = comb ψ S T c (om (g, h) f) := by
  change om (g, h) ((c.mapDomain _).sum fun u a => a • heisO ψ S T u f) = c.sum fun u a => a • heisO ψ S T u (om (g, h) f)
  rw [Finsupp.sum_mapDomain_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _), Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, hom.om_heis g h _ f hf, GlobalTheory.LocModMove.actO_actO_inv'']

theorem combAt_mapDomain {P : GlobalTheory.FinPl.Pl D → Prop} {c : WO S T →₀ ℂ} (hc : GlobalTheory.FinPl.CombAt P c) (g : GA D S) (h : GA D T) :
    GlobalTheory.FinPl.CombAt P (c.mapDomain (actO S T g h)) := by
  intro u hu i j
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  rw [actO, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hc x hx b a)

theorem gen {r : ℕ} {k : Fin r → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (hq : ∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) (hU : ∀ i, (q i).UnitAA)
    (hv : Function.Injective fun i => (q i).v) {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hQ : ∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ∀ p, P p ↔ ∃ i, (q i).v = p) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT}
    {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) {ΛS : GlobalTheory.FinPl.Lat S} {ΛT : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} (g : GA D S) (h : GA D T)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank} (hL : L.Pg = ∅) {sS sT χj ξ vac} {d : WO S T →₀ ℂ} (h0 : vac ≠ 0)
    (hd : GlobalTheory.FinPl.CombAt P d)
    (hst : IsStepVecOf ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) βS βT L χj Q ξ vac (comb ψ S T d vac))
    (c : Fin r → WO S T →₀ ℂ) (hc : ∀ i, ∀ u ∈ (c i).support, IsHalf ((q i).e + cA D (q i).e) u)
    (hlat : ∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) →
      (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔
        (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S ΛS (· = (q i).v)) ∧
      ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔
        (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T ΛT (· = (q i).v))
    (hput : ∀ e, IsIdemSum e Q → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 vac Tm →
      ∀ i, Puts ψ (om (g, h) ∘ₗ Tm) e βS βT Q (pl i) (locQ L.r (ξ (pl i))) (c i))
    (f : WO S T → ℂ) (hf : GlobalTheory.FinPl.Vac ψ S T ΛS ΛT P f) :
    om (g, h) (comb ψ S T d f) = comb ψ S T (aconv (List.ofFn c)) (om (g, h) f) := by
  obtain ⟨hvac, e, he, ⟨Tm, hTm⟩, hall⟩ := hst
  rw [hL, Finset.empty_union] at he
  have hpl : Function.Injective pl := fun i i' H => hv (GlobalTheory.T.splitPlace_baseEq_of_same_idempotentPrime D _ _ (q i) (q i') _ (hq i) (H ▸ hq i'))
  have hcv := GlobalTheory.T.listConvolution_distinctPlaces_supported_and_composition D ψ S T (Fin r) (fun i => (q i).v) c hv
    (fun i u hu => GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D _ (q i) _ _ u (hc i u hu)) (List.finRange r) (List.nodup_finRange r)
  rw [← List.ofFn_eq_map] at hcv
  have hcP : GlobalTheory.FinPl.CombAt P (aconv (List.ofFn c)) := by
    have : P = fun p => ∃ i ∈ List.finRange r, (q i).v = p := funext fun p => propext (by simpa using hP p)
    rw [this]; exact hcv.1
  have e0 : Tm (datum e βS βT fun _ => 1) = vac := by
    rw [← hTm.vac, one_smul]
    refine congrArg Tm (funext fun x => if_congr ?_ rfl rfl)
    rw [and_comm]
    exact and_congr_left fun hx => GlobalTheory.T.integralFrameMatrix_iff_mem_splitHalfHomLattice D r k q pl Q e hq hU hpl hQ he S T ΛS ΛT hS hT βS βT hlat x hx
  have e1 : comb ψ S T d vac = Tm (datum e βS βT fun y => ((List.finRange r).map fun i => locQ L.r (ξ (pl i)) (y (pl i))).prod) := by
    refine (hall Tm hTm).trans (congrArg Tm (funext fun x => if_congr Iff.rfl ?_ rfl))
    have hQ' : Q = Finset.univ.image pl := Finset.ext fun w => by simpa using hQ w
    rw [omegaG_of_empty L hL, one_mul, GlobalTheory.FunObj.Comparison₂.omegaQ_eq_prod, hQ', Finset.prod_image fun _ _ _ _ H => hpl H,
      Fin.prod_univ_def]
    rfl
  have e2 := iterate hpl (fun i => (hQ _).2 ⟨i, rfl⟩) _ c (hput e he Tm hTm) (List.finRange r) (List.nodup_finRange r)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e1, e0, ← hcv.2, ← om_comb hom g h _ hvac.2.theta] at e2
  have e3 := congrArg (om (g, h)⁻¹) e2
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    Module.End.one_apply] at e3
  have hle : latO S T (ΛS : Set _) (ΛT : Set _) P ≤ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  rw [GlobalTheory.T.heisenbergCombination_eq_on_vacua_of_eq_one D r k q P hv hP ψ hom.std S T ΛS ΛT hS hT d _ hd (combAt_mapDomain hcP g⁻¹ h⁻¹) vac
    ⟨hvac.2.theta, fun u hu => hvac.2.lat.1 u (hle hu), fun e he u hu hh => hvac.2.lat.2 e he u (hle hu) hh⟩ h0 e3 f hf,
    om_comb hom g h _ hf.1]

theorem lat_of_movedTo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {g : GA D S} {Λ N : GlobalTheory.FinPl.Lat S}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) (hΛ : IsSelfDualC S Λ) (hN : IsSelfDualC S N) (hm : GlobalTheory.FinPl.Moves S g Λ N P)
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (σ : Fin S.rank ≃ Y) {β : GL (Fin S.rank) (EAf D)}
    (hβ : MovedTo (ofSplit q) S g β (F.β.submatrix id σ))
    (hF : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S N (· = q.v))
    (π' : EAf D →+* k) (hπ : ∀ a, π' (toEAf D a) = q.pr a) (y : Fin S.rank → k) :
    (∀ a, y a ∈ 𝒪[k]) ↔ (fun a => q.sec ((β.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S Λ (· = q.v) := by
  have h1 := map_eq_of_movedTo (ofSplit q) F hπ 1 σ (by rw [Matrix.mul_one]; exact hβ)
  have h2 := GlobalTheory.T.splitPlaceFrame_movedBack_isLatticeBasis D k q S g Λ N P hP hΛ hN hm Y _ _ (β_eq_moved (ofSplit q) F g) hF (y ∘ σ.symm)
  rw [h1, Matrix.mul_one, Matrix.submatrix_mulVec_equiv]
  refine Iff.trans ⟨fun H i => H _, fun H a => ?_⟩ h2
  simpa using H (σ a)

theorem int_of_parPhi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a s s' : Type} [Fintype a] [DecidableEq a] [Fintype s'] [DecidableEq s']
    (δ : kˣ →* ℂˣ) (z : Matrix (a ⊕ s) (a ⊕ s') k) (hz : parPhi δ z ≠ 0) (i j) : z i j ∈ 𝒪[k] := by
  obtain ⟨⟨g, hg, e⟩, h1, h2, h3⟩ := (parPhi_ne_zero_iff δ).1 hz
  rcases i with i | i <;> rcases j with j | j
  · have := intM_of_mem_KO hg i j
    rw [e] at this
    exact this
  · exact h2 i j
  · exact h1.intM i j
  · exact h3 i j

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j, j + 1 < D.R.m → GlobalTheory.FinPl.Moves (c.V j) (B.b j) (B.Λ j) (v.N j) S → GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → B.b j ∈ GfC (c.V j) → B.b (j + 1) ∈ GfC (c.V (j + 1)) → IsSelfDualC _ (B.Λ j) → IsSelfDualC _ (B.Λ (j + 1)) → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V j).rank) χj vac (d : WO (c.V j) (c.V (j + 1)) →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V j) (c.V (j + 1)) sS sT (B.Λ j : Set _) (B.Λ (j + 1) : Set _) (B.β j) (B.β (j + 1)) LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ j) (B.Λ (j + 1)) S g → om (B.b j, B.b (j + 1)) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).eL j)) (om (B.b j, B.b (j + 1)) g) := by
  intro D c v B χ hc hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  have hn : ∀ i, ∃ n, j + n = (G i).s := fun i => ⟨(G i).s - j, by have := (G i).hs; omega⟩
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).eL j) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain ⟨n, hn⟩ := hn i
    exact ((E i).eL_at j n hn).1
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, -, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, -, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd j (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ j (n + 1) (by omega))) mS
        ((G i).latY j (n + 1) _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' (hv.sd (j + 1) hj) hmv' _ (eb.symm.trans (stdOrd _ _ (j + 1) n (by omega))) mT
        ((G i).latY (j + 1) n _) π' hπ⟩
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, ha, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, hb, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ _ _ _ mS mT ((E i).reg.1 j n hn) rfl ((E i).eL_at j n hn)

end GlobalTheory.QVec
end
end

section
noncomputable section

section General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QVecJoin
open GlobalTheory.QVec GlobalTheory.LocMod.StepVec

theorem step_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j, j + 1 < D.R.m → GlobalTheory.FinPl.Moves (c.V j) (B.b j) (B.Λ j) (v.N j) S → GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → B.b j ∈ GfC (c.V j) → B.b (j + 1) ∈ GfC (c.V (j + 1)) → IsSelfDualC _ (B.Λ j) → IsSelfDualC _ (B.Λ (j + 1)) → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V j).rank) χj vac (d : WO (c.V j) (c.V (j + 1)) →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V j) (c.V (j + 1)) sS sT (B.Λ j : Set _) (B.Λ (j + 1) : Set _) (B.β j) (B.β (j + 1)) LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ j) (B.Λ (j + 1)) S g → om (B.b j, B.b (j + 1)) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).eL j)) (om (B.b j, B.b (j + 1)) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  have hn : ∀ i, ∃ n, j + n = (G i).s := fun i => ⟨(G i).s - j, by have := (G i).hs; omega⟩
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).eL j) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain ⟨n, hn⟩ := hn i
    exact ((E i).eL_at j n hn).1
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, -, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, -, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd j (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ j (n + 1) (by omega))) mS
        ((G i).latY j (n + 1) _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' (hv.sd (j + 1) hj) hmv' _ (eb.symm.trans (stdOrd _ _ (j + 1) n (by omega))) mT
        ((G i).latY (j + 1) n _) π' hπ⟩
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, ha, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, hb, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ _ _ _ mS mT ((E i).reg.1 j n hn) rfl ((E i).eL_at j n hn)

theorem step_top : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j (h : j + 2 * 0 + 2 = D.R.m), GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → GlobalTheory.FinPl.Moves c.T B.bT B.ΛT v.NT S → B.b (j + 1) ∈ GfC (c.V (j + 1)) → B.bT ∈ GfC c.T → IsSelfDualC _ (B.Λ (j + 1)) → IsSelfDualC _ B.ΛT → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V (j + 1)).rank) χj vac (d : WO (c.V (j + 1)) c.T →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V (j + 1)) c.T sS sT (B.Λ (j + 1) : Set _) (B.ΛT : Set _) (B.β (j + 1)) B.βT LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V (j + 1)) c.T χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ (j + 1)) B.ΛT S g → om (B.b (j + 1), B.bT) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).toAt.eT j h)) (om (B.b (j + 1), B.bT) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).toAt.eT j hj) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    exact (E i).eLT_at.1
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, -, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, -, mT⟩ := (G i).frameTop
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd _ (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ _ 0 rfl)) mS
        ((G i).latY _ 0 _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' hv.sdT hmv' _ eb.symm mT (G i).latT π' hπ⟩
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, ha, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, hb, mT⟩ := (G i).frameTop
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ (Equiv.refl _) _ _ mS mT (E i).reg.2.1 rfl (E i).eLT_at

end GlobalTheory.QVecJoin
end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QVecJoin

theorem natCast_mem_under {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem false_of_coprime_mem {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

theorem isWeilDatum_cast {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

theorem qVec_pinTup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    QVec (a.fam row col) ((famOf a J row col hCh t).pinTup sc cT) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat J hJ row col hCh sc cT t
  have hC3 := hW.pk.bot.hyp.2.2.2.1
  have hL := hC3.lev
  obtain ⟨hinj, hund⟩ := GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t (J t) (hJ t)
  have hV := (ha.tie row col).1

  have hQS : ∀ p, p ∈ ((famOf a J row col hCh t).pinTup sc cT).Q ↔ ∃ i, ((J t).G i).q.v = p := by
    intro p
    simp only [QFam.pinTup, famOf, Finset.mem_image]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
  have hSQ : ∀ p, (∃ i, ((J t).G i).q.v = p) ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, hund i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, rfl⟩ := (hJ t).surj PP hPP
      exact ⟨i, hund i⟩
  have hQiff : ∀ PP, PP ∈ (pk W).Q t ↔ ∃ i, (J t).pl i = PP := fun PP =>
    ⟨fun h => (hJ t).surj PP h, by rintro ⟨i, rfl⟩; exact (J t).mem i⟩
  have hrk : ∀ i, (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (((J t).G i).s + 1) := by
    intro i
    have e1 : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m - 1 := rfl
    have e2 := ((J t).G i).hs
    omega

  have gIn : ∀ PP ∈ (pk W).Pg, ∃ k, (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    refine ⟨k, ?_⟩
    have hmemK : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ (PP.under (𝓞 (I.rec7 l Z).host.K)).asIdeal := by
      have hk' : PP.under (𝓞 (I.rec7 l Z).host.K) = (pk W).C.P.pb k := hk
      rw [hk']
      exact (pk W).C.P.pb_over k
    have h2 : algebraMap (𝓞 (I.rec7 l Z).host.K) (𝓞 (I.rec7 l Z).host.E) (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hoff : ∀ p, (∃ i, ((J t).G i).q.v = p) → p ∉ a.v.gP := by
    intro p hp hxg
    obtain ⟨PP, hPP, rfl⟩ := (hSQ p).1 hp
    obtain ⟨PP', hPP', e⟩ := (hV.gP _).1 hxg
    obtain ⟨k, hk⟩ := gIn PP' hPP'
    have hg : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal :=
      (natCast_mem_under PP _).1 (e ▸ (natCast_mem_under PP' _).2 hk)
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hPP
    haveI : PP.asIdeal.IsPrime := PP.isPrime
    haveI : Finite (Formalism.L2.DIV.kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    haveI : Fintype (Formalism.L2.DIV.kP PP) := Fintype.ofFinite _
    have hq0 : ((q : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
      have h0q : ((q : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
        rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP PP)
      exact (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).1 (by simpa using h0q)
    exact false_of_coprime_mem PP ((Nat.coprime_primes hq ((I.rec7 l Z).host.g_prime k)).2 (hne k)) hq0 hg
  have hS : (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) = (fun p => ∃ i, ((J t).G i).q.v = p) :=
    funext fun p => propext (hQS p)
  have hmv : ∀ j, j < (I.rec7 l Z).R.m → GlobalTheory.FinPl.Moves _ (a.g.b j) ((pk W).ΛY j) (a.v.N j) (fun p => ∃ i, ((J t).G i).q.v = p) :=
    fun j hj => hV.moves j hj _ hoff
  have hb : ∀ j, a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := fun j => (hV.b j) ▸ ha.vis.b j
  have hS' : (fun p => ∃ i, ((J t).G i).q.v = p) = fun p => ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) :=
    funext fun p => propext (hSQ p)
  have sdY : ∀ j, j < (I.rec7 l Z).R.m → IsSelfDualC (Yc (I.rec7 l Z) j) ((pk W).ΛY j) := fun j hj =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY j hj)
  have sdX : IsSelfDualC (I.rec7 l Z).sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX
  refine ⟨?_, ?_⟩
  · intro j hj d hd g hg
    have hmid : ((famOf a J row col hCh t).pinTup sc cT).eQ j = aconv (List.ofFn fun i => ((J t).E i).eL j) := if_pos hj
    rw [hmid]
    rw [hS] at hg
    exact step_mid (I.rec7 l Z) (commOf (pk W) u a.g) a.v (baseOf (pk W) (lvP W) u a.g) (chrK W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((pk W).xiR t) ((pk W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv j (by omega)) (hmv (j + 1) hj) (hb j) (hb (j + 1)) (sdY j (by omega)) (sdY (j + 1) hj) _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _ (hC3.chain.ωY t j hj) g hg
  · intro j hj d hd g hg
    rw [hS] at hg
    have hmT : GlobalTheory.FinPl.Moves _ a.g.bT (pk W).ΛX a.v.NT (fun p => ∃ i, ((J t).G i).q.v = p) := by
      rw [hV.bT.2]; exact hV.movesT _
    have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
      have h1 := ha.vis.bT
      rwa [hV.bT.1] at h1
    exact step_top (I.rec7 l Z) (commOf (pk W) u a.g) a.v (baseOf (pk W) (lvP W) u a.g) (chrK W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((pk W).xiR t) ((pk W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv (j + 1) (by omega)) hmT (hb (j + 1)) hbT (sdY (j + 1) (by omega)) sdX _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _
      (isWeilDatum_cast ((pk W).ωX t) (hC3.chain.ωX t) (j + 1) (idx_top hj)) g hg

end GlobalTheory.QVecJoin

end
end
