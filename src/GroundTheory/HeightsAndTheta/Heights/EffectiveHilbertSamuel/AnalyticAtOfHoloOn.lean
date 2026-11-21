import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HolLineBundleToAltTransition
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.JetOfMonomialSumStatement

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def TopFormNormEqIntegral.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (A : FinHolAtlas D X) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (ψ : Fin A.n → X → ℝ) (F : Fin A.n → X → ℂ),
    IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight B ψ → F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    topNormSq A ψ F = IndefiniteRowSideFullHecke.EffectiveHS.topFormWeightedL2 ψ F

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel

def NatSpaceEqVnat.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.HSData A Y) (j : ℕ),
    ((d.natSpace j : Submodule ℂ (Fin A.n → X → ℂ)) : Set (Fin A.n → X → ℂ)) =
      Vnat A (HolLineBundle.split_model_to_place_model d.L₂) (HolLineBundle.split_model_to_place_model d.L) d.φA
        (IndefiniteRowSideFullHecke.EffectiveHS.fsPhi d.W) j

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def FLBoundOfGoodS.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (s : Fin D → Fin d.W.n → ℂ),
    d.IsGoodS s → FLBound A d.W.e (fun i => d.W.sec (s i))

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def HasSymbolIffSymEq.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas D X)
    (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (s : Fin D → Fin d.W.n → ℂ) (a : ℕ) (F : Fin A.n → X → ℂ) (g : (Fin D → ℕ) → X → ℂ),
    F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    (d.HasSymbol s a F g ↔ d.InFil s a F ∧ SymEq A (fun i => d.W.sec (s i)) F a g)

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS (topForms topFormWeightedL2 twist wAdd fsPhi HermSpace FSData HSData
  secMul l2n tuples jacDet)
open scoped ENNReal

noncomputable section

namespace TranslateEq

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem jac_eq_jacDet (j k : Fin A.n) (x : X) : jac A j k x = jacDet A j k x := rfl

theorem twist_g (L₂ L : HolLineBundle A) (m : ℕ) (j k : Fin A.n) (x : X) :
    (twist L₂.toIndefiniteRowSideFullHecke L.toIndefiniteRowSideFullHecke m).g j k x = L₂.g j k x * L.g j k x ^ m := rfl

theorem topSections_eq_topForms (L₂ L : HolLineBundle A) (m : ℕ) :
    topSections A L₂ L m = topForms (twist L₂.toIndefiniteRowSideFullHecke L.toIndefiniteRowSideFullHecke m) := by
  ext u
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h3, fun j k x hx => ?_⟩
    rw [h2 j k x hx, twist_g, jac_eq_jacDet]; ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j k x hx => ?_, h2⟩
    rw [h3 j k x hx, twist_g, jac_eq_jacDet]; ring

theorem log_normSq_mul_pow {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℕ) :
    Real.log (‖a * b ^ m‖ ^ 2) = Real.log (‖a‖ ^ 2) + m * Real.log (‖b‖ ^ 2) := by
  have h : ‖a * b ^ m‖ ^ 2 = ‖a‖ ^ 2 * (‖b‖ ^ 2) ^ m := by rw [norm_mul, norm_pow]; ring
  rw [h, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ha))
    (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 hb))), Real.log_pow (‖b‖ ^ 2) m]

theorem isWeight_wAdd {L₂ L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A}
    {ψ φ : Fin A.n → X → ℝ} (hψ : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L₂ ψ)
    (hφ : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L φ) (m : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight (twist L₂ L m) (wAdd ψ φ m) := by
  refine ⟨fun j l => (hψ.1 j l).add (contDiffOn_const.mul (hφ.1 j l)), fun j k x hx => ?_⟩
  show ψ j x + m * φ j x = ψ k x + m * φ k x + Real.log (‖L₂.g j k x * L.g j k x ^ m‖ ^ 2)
  rw [log_normSq_mul_pow (L₂.ne_zero j k x hx) (L.ne_zero j k x hx), hψ.2 j k x hx, hφ.2 j k x hx]
  ring

theorem noCommonZero_iff {N : ℕ} (L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (e : Fin N → Fin A.n → X → ℂ) (he : ∀ i, e i ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L 1) :
    NoCommonZero A e ↔ ∀ j, ∀ x ∈ (A.chart j).source, ∃ i, e i j x ≠ 0 := by
  constructor
  · intro h j x hx
    obtain ⟨i, hi⟩ := h x
    refine ⟨i, fun h0 => hi ?_⟩
    obtain ⟨-, -, hc⟩ := he i
    rw [hc (chartIdx A x) j x ⟨Classical.choose_spec (A.cover x), hx⟩, h0, mul_zero]
  · intro h x
    exact h _ x (Classical.choose_spec (A.cover x))

theorem mem_sections_of_holLineBundle_equiv (L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    {f : Fin A.n → X → ℂ} (hf : f ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L 1) :
    f ∈ (HolLineBundle.split_model_to_place_model L).sections 1 := by
  rw [HolLineBundle.sections_eq_sectionSpace]; exact hf

section FS

variable {Y : Type} [TopologicalSpace Y] (d : FSData A Y)

theorem sPow_eq_monoSec (s : Fin D → Fin d.W.n → ℂ) (α : Fin D → ℕ) :
    sPow (fun i => d.W.sec (s i)) α = d.monoSec s α := by
  funext j x
  simp [sPow, IndefiniteRowSideFullHecke.EffectiveHS.FSData.monoSec, Finset.prod_apply]

end FS

section Translate

variable {Y : Type} [TopologicalSpace Y]

def toEmbDatum [T2Space X] (d : FSData A Y) (hA : IsAlgCover A) : EmbDatum D where
  U := X
  A := A
  cover := hA
  L := HolLineBundle.split_model_to_place_model d.L
  L₂ := HolLineBundle.split_model_to_place_model d.L₂
  N := d.W.n
  N₂ := d.W₂.n
  e := d.W.e
  e₂ := d.W₂.e
  e_mem i := mem_sections_of_holLineBundle_equiv d.L (d.W.mem i)
  e₂_mem i := mem_sections_of_holLineBundle_equiv d.L₂ (d.W₂.mem i)
  gen := (noCommonZero_iff d.L d.W.e d.W.mem).2 d.gen
  gen₂ := (noCommonZero_iff d.L₂ d.W₂.e d.W₂.mem).2 d.gen₂

theorem sec_single {B : Submodule ℂ (Fin A.n → X → ℂ)} (H : HermSpace B) (i : Fin H.n) :
    H.sec (Pi.single i 1) = H.e i := by
  unfold IndefiniteRowSideFullHecke.EffectiveHS.HermSpace.sec
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

def toZeroDatum [T2Space X] (d : FSData A Y) (hA : IsAlgCover A) (s : Fin D → Fin d.W.n → ℂ)
    (hs : d.IsGoodS s) (hfl : FLBound A d.W.e fun i => d.W.sec (s i)) :
    ZeroDatum (toEmbDatum d hA) where
  c := s
  finite := hs.finite
  nondeg := hs.etale
  fl := hfl

def toTwistWeight (d : HSData A Y) :
    TwistWeight A (HolLineBundle.split_model_to_place_model d.L₂) (HolLineBundle.split_model_to_place_model d.L) D where
  φ := d.φA
  smooth := d.isWeightA.1
  compat j k x hx := by
    show d.φA j x = d.φA k x + Real.log (‖d.L₂.g j k x‖ ^ 2) + D * Real.log (‖d.L.g j k x‖ ^ 2)
    rw [d.isWeightA.2 j k x hx]
    show d.φA k x + Real.log (‖d.L₂.g j k x * d.L.g j k x ^ D‖ ^ 2) = _
    rw [log_normSq_mul_pow (d.L₂.ne_zero j k x hx) (d.L.ne_zero j k x hx)]; ring
  psh j y hy w := (d.pshA j j).2 y ⟨hy, (A.chart j).map_target hy⟩ w

theorem space_le_topForms (d : HSData A Y) (j : ℕ) :
    (d.V j).space ≤ topForms (twist d.L₂ d.L (D + j)) :=
  Submodule.span_le.2 (Set.range_subset_iff.2 (d.V j).mem)

def toSpaceDatum [T2Space X] [SecondCountableTopology X] (hN : TopFormNormEqIntegral.Statement)
    (hV : NatSpaceEqVnat.Statement) (d : HSData A Y) (hA : IsAlgCover A) (h0 : d.H0')
    (h1 : d.H1) (h2 : d.H2') : SpaceDatum (toEmbDatum d.toFSData hA) d.T where
  β := d.β
  one_le_β := d.one_le_β
  φA := toTwistWeight d
  φA_le := d.boundA
  V j := (d.V j).space
  V_le j := by
    rw [topSections_eq_topForms]
    exact space_le_topForms d j
  normT := (d.V d.T).hnorm
  sections_zero_mem_natural F hF := (Set.ext_iff.1 (hV D X Y A d 0) F).1 (h0.1 hF)
  sections_top_mem_natural F hF := h0.2 ((Set.ext_iff.1 (hV D X Y A d D) F).2 hF)
  H1 j hj i F hF := by
    have h := (h1 j hj (Pi.single (show Fin d.W.n from i) 1) F hF).1
    rw [sec_single] at h
    exact h
  H2 F hF := by
    have e := hN D X A _ _ F (isWeight_wAdd d.isWeight₂ d.isWeight (D + d.T))
      (space_le_topForms d d.T hF)
    exact (h2 F hF).trans_eq (congrArg _ e.symm)

theorem pspace_eq_Pσ (d : HSData A Y) (s : Fin D → Fin d.W.n → ℂ) :
    Pspace (fun i => d.W.sec (s i)) (d.V D).space d.T = d.Pσ s := by
  unfold Pspace IndefiniteRowSideFullHecke.EffectiveHS.HSData.Pσ
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq, sPow_eq_monoSec]
  rfl

end Translate

end TranslateEq

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

noncomputable section

namespace EffectiveHilbertSamuelJetLemmas

variable {D : ℕ} {U : Type} [TopologicalSpace U]

theorem chart_sum_eq (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (a : ℕ)
    (h : (Fin D → ℕ) → Fin A.n → U → ℂ) (c : Fin A.n) :
    (∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s α * h α) c ∘ (A.chart c).symm =
      fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (s i c ∘ (A.chart c).symm) z ^ α i) * (h α c ∘ (A.chart c).symm) z := by
  funext z
  simp [sPow, Finset.sum_apply, Finset.prod_apply]

theorem analyticAt_of_holoOn (A : FinHolAtlas D U) {f : U → ℂ} {c : Fin A.n}
    (hf : A.HoloOn (A.chart c).source f) {x : U} (hx : x ∈ (A.chart c).source) :
    AnalyticAt ℂ (f ∘ (A.chart c).symm) (A.chart c x) :=
  hf c _ ⟨(A.chart c).map_source hx, by rw [Set.mem_preimage, (A.chart c).left_inv hx]; exact hx⟩

theorem exists_unit {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (he : NoCommonZero A e) {S : Set U} (hS : S.Finite) :
    ∃ c : Fin N → ℂ, ∀ x ∈ S, lin e c (chartIdx A x) x ≠ 0 := by
  classical
  let φ : U → (Fin N → ℂ) →ₗ[ℂ] ℂ := fun x =>
    ∑ k, e k (chartIdx A x) x • (LinearMap.proj k : (Fin N → ℂ) →ₗ[ℂ] ℂ)
  have hφ : ∀ x c, φ x c = lin e c (chartIdx A x) x := by
    intro x c
    simp [φ, lin, Finset.sum_apply, mul_comm]
  have hne : ∀ x, LinearMap.ker (φ x) ≠ ⊤ := by
    intro x htop
    obtain ⟨k, hk⟩ := he x
    have h0 : Pi.single k 1 ∈ LinearMap.ker (φ x) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at h0
    have hl : lin e (Pi.single k 1) = e k := by simp [lin, Pi.single_apply]
    rw [hl] at h0
    exact hk h0
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt hS.toFinset
    (fun x => LinearMap.ker (φ x)) hne (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)
  obtain ⟨c, -, hc⟩ := Set.exists_of_ssubset hss
  refine ⟨c, fun x hx h0 => hc ?_⟩
  rw [Set.mem_iUnion₂]
  exact ⟨x, hS.mem_toFinset.2 hx, by rw [SetLike.mem_coe, LinearMap.mem_ker, hφ]; exact h0⟩

theorem _root_.GroundTheory.Heights₂.Heights.EffectiveHS.SymOnto.proof
    (hJ : JetOfMonomialSum.Statement) : SymOnto.Statement := by
  classical
  intro D T X Z Y hD hT hRes a ha g
  obtain ⟨c₀, hc₀⟩ := exists_unit X.A X.e X.gen Z.finite
  set w : Fin X.A.n → X.U → ℂ := lin X.e c₀ with hw
  set j := T - a with hj
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ i, α i = a := fun α hα =>
    Finset.Nat.mem_antidiagonalTuple.1 hα
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / w (chartIdx X.A y) y ^ j)
  have hwj : w ^ j = ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • ∏ l, X.e (ι l) := by
    rw [← Fin.prod_const j w, hw, lin, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    funext k x
    simp [Finset.prod_apply, Finset.prod_mul_distrib]
  have pt : ∀ x ∈ zeroSet X.A Z.s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
        (X.A.chart (chartIdx X.A x) x) = 0) ∧
      ∀ v : Fin D → ℂ, iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
          (X.A.chart (chartIdx X.A x) x) (fun _ => v) / (a.factorial : ℂ) =
        sJac X.A Z.s (chartIdx X.A x) x * ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
          (∏ i, (sJacMap X.A Z.s (chartIdx X.A x) x v i) ^ α i) * g α x := by
    intro x hx
    set c := chartIdx X.A x with hc
    have hxc : x ∈ (X.A.chart c).source := Classical.choose_spec (X.A.cover x)
    have hlin : ∀ c' : Fin X.N → ℂ, lin X.e c' ∈ X.L.sections 1 := fun c' =>
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)
    have au : ∀ i, AnalyticAt ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) := fun i =>
      analyticAt_of_holoOn X.A ((hlin (Z.c i)).1 c) hxc
    have aw : AnalyticAt ℂ (w c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      analyticAt_of_holoOn X.A ((hlin c₀).1 c) hxc
    have ah : ∀ α, AnalyticAt ℂ ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      fun α => (aw.pow j).mul (analyticAt_of_holoOn X.A ((Y.V_le 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, -, h3⟩ := hJ D D (fun i => Z.s i c ∘ (X.A.chart c).symm)
      (fun α => (w ^ j * m α) c ∘ (X.A.chart c).symm) _ a au hz ah
    have hF := chart_sum_eq X.A Z.s a (fun α => w ^ j * m α) c
    rw [hF]
    refine ⟨h1, fun v => ?_⟩
    rw [h3 v]
    have hJ0 : sJac X.A Z.s c x ≠ 0 := Z.nondeg x hx
    have hcoef : ∀ α, ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) =
        g α x * sJac X.A Z.s c x := by
      intro α
      have hr := hm α x hx
      have hw0 : w c x ≠ 0 := hc₀ x hx
      simp only [res] at hr
      rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc, Pi.mul_apply, Pi.pow_apply]
      linear_combination hr
    have hder : ∀ i, sJacMap X.A Z.s c x v i =
        fderiv ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) v := by
      intro i
      show (fderiv ℂ (fun z i => (Z.s i c ∘ (X.A.chart c).symm) z) (X.A.chart c x)) v i = _
      rw [fderiv_pi (fun i => (au i).differentiableAt)]
      rfl
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hcoef α]
    simp only [hder]
    ring
  refine ⟨∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow Z.s α * (w ^ j * m α), ?_,
    fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩
  refine Submodule.sum_mem _ fun α hα => ?_
  have hexp : sPow Z.s α * (w ^ j * m α) =
      ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • (sPow Z.s α * (∏ l, X.e (ι l)) * m α) := by
    rw [hwj, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [hexp]
  exact Submodule.sum_mem _ fun ι _ => Submodule.smul_mem _ _ (Submodule.mem_sup_left
    (Submodule.subset_span ⟨α, j, ι, m α, hmV α, by rw [hsum α hα]; omega,
      by rw [hsum α hα]; exact ha, rfl⟩))

theorem _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.proof
    (hJ : JetOfMonomialSum.Statement) : IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.Statement := by
  classical
  intro D hD X Y _ _ _ _ _ _ A d s hGood hRes hUnit a ha g
  obtain ⟨c₀, hc₀⟩ := hUnit
  set j := d.T - a with hj
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / d.W.sec c₀ (chartIdx A y) y ^ j)
  let s' : Fin D → Fin A.n → X → ℂ := fun i => d.W.sec (s i)
  let hh : (Fin D → ℕ) → Fin A.n → X → ℂ := fun α =>
    IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.wProd fun _ : Fin j => c₀) (m α)
  have hF : (∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a,
      IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α)) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [TranslateEq.sPow_eq_monoSec]
    rfl
  refine ⟨∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α),
    Submodule.sum_mem _ fun α hα => Submodule.mem_sup_left (Submodule.subset_span
      ⟨j, α, fun _ => c₀, m α, hmV α, ?_, ?_, rfl⟩), ?_⟩
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; omega
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; exact ha
  have hsec : ∀ c' : Fin d.W.n → ℂ,
      d.W.sec c' ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace d.L 1 := fun c' =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (d.W.mem k)
  have pt : ∀ x ∈ d.zeroU s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) = 0) ∧
      iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) =
        ∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, (g α x * d.sJac s (chartIdx A x) x) •
          iteratedFDeriv ℂ a (fun z => ∏ i, d.sLoc s (chartIdx A x) z i ^ α i)
            (A.chart (chartIdx A x) x) := by
    intro x hx
    set c := chartIdx A x with hc
    have hxc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
    have au : ∀ i, AnalyticAt ℂ (s' i c ∘ (A.chart c).symm) (A.chart c x) := fun i =>
      analyticAt_of_holoOn A ((hsec (s i)).1 c) hxc
    have aw : AnalyticAt ℂ (d.W.sec c₀ c ∘ (A.chart c).symm) (A.chart c x) :=
      analyticAt_of_holoOn A ((hsec c₀).1 c) hxc
    have hhc : ∀ α, hh α c ∘ (A.chart c).symm = fun z =>
        (d.W.sec c₀ c ∘ (A.chart c).symm) z ^ j * (m α c ∘ (A.chart c).symm) z := by
      intro α
      funext z
      simp [hh, IndefiniteRowSideFullHecke.EffectiveHS.secMul, IndefiniteRowSideFullHecke.EffectiveHS.FSData.wProd]
    have ah : ∀ α, AnalyticAt ℂ (hh α c ∘ (A.chart c).symm) (A.chart c x) := by
      intro α
      rw [hhc α]
      exact (aw.pow j).mul
        (analyticAt_of_holoOn A ((TranslateEq.space_le_topForms d 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (s' i c ∘ (A.chart c).symm) (A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, h2, -⟩ := hJ D D (fun i => s' i c ∘ (A.chart c).symm)
      (fun α => hh α c ∘ (A.chart c).symm) _ a au hz ah
    rw [chart_sum_eq A s' a hh c]
    refine ⟨h1, ?_⟩
    rw [h2]
    have hJ0 : d.sJac s c x ≠ 0 := hGood.etale x hx
    refine Finset.sum_congr rfl fun α _ => ?_
    have hr := hm α x hx
    have hw0 : d.W.sec c₀ c x ≠ 0 := hc₀ x hx
    simp only [IndefiniteRowSideFullHecke.EffectiveHS.FSData.res] at hr
    rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
    have hcoef : (hh α c ∘ (A.chart c).symm) (A.chart c x) = g α x * d.sJac s c x := by
      rw [hhc α]
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]
      linear_combination hr
    rw [hcoef]
    rfl
  rw [hF]
  exact ⟨fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩

end EffectiveHilbertSamuelJetLemmas

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end
