import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

section
noncomputable section

namespace PositivityTheory.ThKG.Fub

open MeasureTheory Topology Filter
open scoped NNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

structure Split (S A B : Subgroup G) (p q : G →* G) : Prop where
  cp : Continuous p
  cq : Continuous q
  cA : IsClosed (A : Set G)
  cB : IsClosed (B : Set G)
  cS : IsClosed (S : Set G)
  mA : ∀ g ∈ S, p g ∈ A
  mB : ∀ g ∈ S, q g ∈ B
  mul : ∀ g ∈ S, p g * q g = g
  hA : ∀ a ∈ A, a ∈ S ∧ p a = a ∧ q a = 1
  hB : ∀ b ∈ B, b ∈ S ∧ q b = b ∧ p b = 1

instance scSub (S : Subgroup G) : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _

variable {S A B : Subgroup G} {p q : G →* G}

def Split.e (h : Split S A B p q) : S ≃ₜ* A × B where
  toFun g := (⟨p g, h.mA _ g.2⟩, ⟨q g, h.mB _ g.2⟩)
  invFun x := ⟨x.1 * x.2, S.mul_mem (h.hA _ x.1.2).1 (h.hB _ x.2.2).1⟩
  left_inv g := Subtype.ext (h.mul _ g.2)
  right_inv x := Prod.ext (Subtype.ext (by simp [(h.hA _ x.1.2).2.1, (h.hB _ x.2.2).2.2]))
    (Subtype.ext (by simp [(h.hA _ x.1.2).2.2, (h.hB _ x.2.2).2.1]))
  map_mul' a b := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
  continuous_toFun := ((h.cp.comp continuous_subtype_val).subtype_mk _).prodMk ((h.cq.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem Split.fub (h : Split S A B p q) (μ : Measure S) (α : Measure A) (β : Measure B) [μ.IsHaarMeasure] [α.IsHaarMeasure]
    [β.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧
      (∀ f g : G → ℂ, Integrable (fun a : A => f a) α → Integrable (fun b : B => g b) β →
        Integrable (fun x : S => f (p x) * g (q x)) μ ∧
          ∫ x : S, f (p x) * g (q x) ∂μ = c * ((∫ a : A, f a ∂α) * ∫ b : B, g b ∂β)) ∧
      ∀ U : Set G, MeasurableSet U → (∀ g ∈ S, g ∈ U ↔ p g ∈ U ∧ q g ∈ U) →
        μ {x | x.1 ∈ U} = c * (α {x | x.1 ∈ U} * β {x | x.1 ∈ U}) := by
  haveI : LocallyCompactSpace A := h.cA.locallyCompactSpace
  haveI : LocallyCompactSpace B := h.cB.locallyCompactSpace
  haveI : LocallyCompactSpace S := h.cS.locallyCompactSpace
  have hm : (μ.map h.e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ h.e
  set c := Measure.haarScalarFactor (μ.map h.e) (α.prod β) with hc
  have he : μ.map h.e = c • α.prod β := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hme : MeasurableEmbedding h.e := h.e.toHomeomorph.measurableEmbedding
  refine ⟨c, hc0, fun f g hf hg => ?_, fun U hU hh => ?_⟩
  · have h1 : Integrable (fun x : A × B => f x.1 * g x.2) (μ.map h.e) := by
      rw [he]; exact (hf.mul_prod hg).smul_measure_nnreal
    refine ⟨(hme.integrable_map_iff.1 h1 :), ?_⟩
    have h2 := hme.integral_map (μ := μ) (fun x : A × B => f x.1 * g x.2)
    rw [he, integral_smul_nnreal_measure, integral_prod_mul (fun a : A => f a) (fun b : B => g b)] at h2
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · simp [NNReal.smul_def]
  · have h2 : {x : S | x.1 ∈ U} = h.e ⁻¹' ({x : A | x.1 ∈ U} ×ˢ {x : B | x.1 ∈ U}) := Set.ext fun x => hh _ x.2
    rw [h2, ← hme.map_apply, he, Measure.smul_apply, Measure.prod_prod]
    rfl

theorem exists_haar (S : Subgroup G) (hS : IsClosed (S : Set G)) (U : Set G) (h1 : (1 : G) ∈ U)
    (hc : IsCompact {x : S | x.1 ∈ U}) (ho : IsOpen {x : S | x.1 ∈ U}) :
    ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1 := by
  haveI : LocallyCompactSpace S := hS.locallyCompactSpace
  let K : TopologicalSpace.PositiveCompacts S := ⟨⟨_, hc⟩, ⟨1, by simpa [ho.interior_eq] using h1⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {R : Type} [CommRing R]

structure Sys (P : R → G →* G) (K : Subgroup G) (U : Set G) (good : R → Prop) : Prop where
  cont : ∀ a, good a → Continuous (P a)
  comp : ∀ a b, good a → good b → ∀ g, P a (P b g) = P (a * b) g
  zero : ∀ g, P 0 g = 1
  add : ∀ a b, good a → good b → a * b = 0 → good (a + b) ∧ ∀ g, P (a + b) g = P a g * P b g
  idem : ∀ a, good a → a * a = a
  cK : IsClosed (K : Set G)
  mK : ∀ a, good a → ∀ g ∈ K, P a g ∈ K
  mU : MeasurableSet U
  one : (1 : G) ∈ U
  mul : ∀ g ∈ U, ∀ g' ∈ U, g * g' ∈ U
  pU : ∀ a, good a → ∀ g ∈ U, P a g ∈ U

def part (P : R → G →* G) (K : Subgroup G) (a : R) : Subgroup G := K ⊓ (P a).eqLocus (MonoidHom.id G)

theorem mem_part {P : R → G →* G} {K : Subgroup G} {a : R} {g : G} : g ∈ part P K a ↔ g ∈ K ∧ P a g = g := Iff.rfl

variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}

theorem Sys.closed (s : Sys P K U good) {a : R} (ha : good a) : IsClosed (part P K a : Set G) :=
  s.cK.inter (isClosed_eq (s.cont a ha) continuous_id)

theorem Sys.split (s : Sys P K U good) {a b : R} (ha : good a) (hb : good b) (hab : a * b = 0) :
    Split (part P K (a + b)) (part P K a) (part P K b) (P a) (P b) where
  cp := s.cont a ha
  cq := s.cont b hb
  cA := s.closed ha
  cB := s.closed hb
  cS := s.closed (s.add a b ha hb hab).1
  mA g hg := ⟨s.mK a ha g hg.1, by show P a (P a g) = P a g; rw [s.comp a a ha ha, s.idem a ha]⟩
  mB g hg := ⟨s.mK b hb g hg.1, by show P b (P b g) = P b g; rw [s.comp b b hb hb, s.idem b hb]⟩
  mul g hg := ((s.add a b ha hb hab).2 g).symm.trans hg.2
  hA g hg := by
    have h0 : P a g = g := hg.2
    have h1 : P b g = 1 := by rw [← h0, s.comp b a hb ha, mul_comm, hab, s.zero]
    exact ⟨⟨hg.1, by show P (a + b) g = g; rw [(s.add a b ha hb hab).2, h0, h1, mul_one]⟩, h0, h1⟩
  hB g hg := by
    have h0 : P b g = g := hg.2
    have h1 : P a g = 1 := by rw [← h0, s.comp a b ha hb, hab, s.zero]
    exact ⟨⟨hg.1, by show P (a + b) g = g; rw [(s.add a b ha hb hab).2, h0, h1, one_mul]⟩, h0, h1⟩

def CO (P : R → G →* G) (K : Subgroup G) (U : Set G) (a : R) : Prop :=
  IsCompact {x : part P K a | x.1 ∈ U} ∧ IsOpen {x : part P K a | x.1 ∈ U}

theorem Sys.good_sum (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0) :
    good (∑ i ∈ T, e i + c) := by
  induction T using Finset.induction_on with
  | empty => simpa using hc
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, add_assoc]
    refine (s.add _ _ (he i) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj)) ?_).1
    rw [mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)), hT i (Finset.mem_insert_self _ _),
      add_zero]

theorem Sys.prod (s : Sys P K U good) {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ i, good (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (c : R) (hc : good c) (α : ∀ i, Measure (part P K (e i)))
    (hα : ∀ i, (α i).IsHaarMeasure ∧ α i {x | x.1 ∈ U} = 1) (β : Measure (part P K c))
    (hβ : β.IsHaarMeasure ∧ β {x | x.1 ∈ U} = 1) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0)
    (hCO : ∀ T' ⊆ T, CO P K U (∑ i ∈ T', e i + c)) (b : R) (hb : b = ∑ i ∈ T, e i + c)
    (μ : Measure (part P K b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ U} = 1) (f : ι → G → ℂ) (g : G → ℂ)
    (hf : ∀ i ∈ T, Integrable (fun x : part P K (e i) => f i x) (α i)) (hg : Integrable (fun x : part P K c => g x) β) :
    Integrable (fun x : part P K b => (∏ i ∈ T, f i (P (e i) x)) * g (P c x)) μ ∧
      ∫ x : part P K b, (∏ i ∈ T, f i (P (e i) x)) * g (P c x) ∂μ =
        (∏ i ∈ T, ∫ x : part P K (e i), f i x ∂(α i)) * ∫ x : part P K c, g x ∂β := by
  induction T using Finset.induction_on generalizing b with
  | empty =>
    obtain rfl : b = c := by simpa using hb
    haveI := hμ.1; haveI := hβ.1
    haveI : LocallyCompactSpace (part P K b) := (s.closed hc).locallyCompactSpace
    have h1 := Measure.isMulLeftInvariant_eq_smul μ β
    have h2 : Measure.haarScalarFactor μ β = 1 := by
      have := hμ.2
      rw [h1, Measure.smul_apply, hβ.2] at this
      simpa using this
    rw [h2, one_smul] at h1
    have h3 : (fun x : part P K b => (∏ i ∈ (∅ : Finset ι), f i (P (e i) x)) * g (P b x)) = fun x : part P K b => g x := by
      funext x; rw [show P b x = x from x.2.2]; simp
    rw [h3, h1]; exact ⟨hg, by simp⟩
  | insert i T hi ih =>
    have hT' : ∀ j ∈ T, e j * c = 0 := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    have hg' := s.good_sum e he ho c hc T hT'
    set b' := ∑ j ∈ T, e j + c with hb'
    have h0 : e i * b' = 0 := by
      rw [hb', mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)),
        hT i (Finset.mem_insert_self _ _), add_zero]
    obtain rfl : b = e i + b' := by rw [hb, Finset.sum_insert hi, add_assoc]
    obtain ⟨μ', hμ'⟩ := exists_haar _ (s.closed hg') U s.one (hCO T (Finset.subset_insert _ _)).1 (hCO T (Finset.subset_insert _ _)).2
    obtain ⟨i1, i2⟩ := ih hT' (fun T' h => hCO T' (h.trans (Finset.subset_insert _ _))) b' rfl μ' hμ'
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    haveI := hμ.1; haveI := hμ'.1; haveI := (hα i).1
    obtain ⟨k, -, k1, k2⟩ := (s.split (he i) hg' h0).fub μ (α i) μ'
    have hk : k = 1 := by
      have := k2 U s.mU fun x hx => ⟨fun h => ⟨s.pU _ (he i) _ h, s.pU _ hg' _ h⟩, fun h => by
        rw [← (s.split (he i) hg' h0).mul x hx]; exact s.mul _ h.1 _ h.2⟩
      rw [hμ.2, (hα i).2, hμ'.2] at this
      simpa using this.symm
    obtain ⟨j1, j2⟩ := k1 (f i) (fun y => (∏ j ∈ T, f j (P (e j) y)) * g (P c y)) (hf i (Finset.mem_insert_self _ _)) i1
    have h3 : (fun x : part P K (e i + b') => (∏ j ∈ insert i T, f j (P (e j) x)) * g (P c x)) =
        fun x : part P K (e i + b') => f i (P (e i) x) * ((∏ j ∈ T, f j (P (e j) (P b' x))) * g (P c (P b' x))) := by
      funext x
      rw [Finset.prod_insert hi, mul_assoc, s.comp c b' hc hg']
      have e1 : c * b' = c := by
        rw [hb', mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => by rw [mul_comm]; exact hT' j hj, zero_add, s.idem c hc]
      rw [e1]
      congr 2
      refine Finset.prod_congr rfl fun j hj => ?_
      have e2 : e j * b' = e j := by
        rw [hb', mul_add, hT' j hj, add_zero, Finset.mul_sum,
          Finset.sum_eq_single_of_mem j hj fun l _ hl => ho j l hl.symm, s.idem _ (he j)]
      rw [s.comp _ b' (he j) hg', e2]
    rw [h3]
    refine ⟨j1, ?_⟩
    rw [j2, i2, hk, Finset.prod_insert hi]; simp [mul_assoc]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] in

theorem transport {S S' : Subgroup G} (h : S = S') (mS : MeasurableSpace S) (hm : mS = borel S) (x : @Measure S mS) :
    ∃ x' : Measure S', (@Measure.IsHaarMeasure _ _ _ mS x → x'.IsHaarMeasure) ∧
      (∀ U : Set G, x' {y | y.1 ∈ U} = x {y | y.1 ∈ U}) ∧ ∀ f : G → ℂ,
        (Integrable (fun y : S' => f y) x' ↔ @Integrable _ _ _ _ mS (fun y : S => f y) x) ∧
          ∫ y : S', f y ∂x' = @integral _ _ _ _ mS x fun y : S => f y := by
  subst h
  have : mS = Subtype.instMeasurableSpace := hm.trans (@BorelSpace.measurable_eq S _ Subtype.instMeasurableSpace (Subtype.borelSpace _)).symm
  subst this
  exact ⟨x, id, fun _ => rfl, fun _ => ⟨Iff.rfl, rfl⟩⟩

def unitP {A : Type} [Ring A] [Algebra R A] (a : R) : Aˣ →* Aˣ := by
  classical
  exact if h : a * a = a then Units.map
    { toFun := fun x : A => a • x + (1 - a) • (1 : A)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun x y => by
        have h1 : a * (1 - a) = 0 := by rw [mul_sub, h]; simp
        have h2 : (1 - a) * a = 0 := by rw [mul_comm, h1]
        have h3 : (1 - a) * (1 - a) = 1 - a := by rw [mul_sub, h2]; simp
        simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, zero_smul, mul_one, add_zero, zero_add] } else 1

theorem coe_unitP {A : Type} [Ring A] [Algebra R A] {a : R} (h : a * a = a) (x : Aˣ) :
    (unitP a x : A) = a • (x : A) + (1 - a) • (1 : A) := by
  unfold unitP; rw [dif_pos h]; rfl

theorem unitInvariant_continuous {A : Type} [Ring A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [ContinuousConstSMul R A] {a : R}
    (h : a * a = a) : Continuous (unitP (A := A) a) := by
  unfold unitP; rw [dif_pos h]
  exact Continuous.units_map _ (by show Continuous fun x : A => a • x + (1 - a) • (1 : A); fun_prop)

theorem unitInvariant_comp {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (x : Aˣ) :
    unitP a (unitP b x) = unitP (a * b) x := by
  have : a * b * (a * b) = a * b := by rw [mul_mul_mul_comm, ha, hb]
  ext; rw [coe_unitP ha, coe_unitP hb, coe_unitP this]; module

theorem unitInvariant_zero {A : Type} [Ring A] [Algebra R A] (x : Aˣ) : unitP (0 : R) x = 1 := by
  ext; rw [coe_unitP (by simp)]; simp

theorem unitInvariant_one {A : Type} [Ring A] [Algebra R A] (x : Aˣ) : unitP (1 : R) x = x := by
  ext; rw [coe_unitP (by simp)]; simp

theorem idem_add {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) : (a + b) * (a + b) = a + b := by
  linear_combination ha + hb + 2 * h

theorem unitInvariant_add {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) (x : Aˣ) :
    unitP (a + b) x = unitP a x * unitP b x := by
  ext
  rw [Units.val_mul, coe_unitP ha, coe_unitP hb, coe_unitP (idem_add ha hb h)]
  have h1 : a * (1 - b) = a := by linear_combination -h
  have h2 : (1 - a) * b = b := by linear_combination -h
  have h3 : (1 - a) * (1 - b) = 1 - (a + b) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, zero_smul, mul_one, one_mul, zero_add, add_smul]
  abel

end PositivityTheory.ThKG.Fub

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub

theorem ae_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
theorem ae_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
theorem ae_top : T2Space (AE F E) ∧ LocallyCompactSpace (AE F E) ∧ SecondCountableTopology (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨e.isEmbedding.t2Space, e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology⟩
theorem ae_t2 : T2Space (AE F E) := ae_top.1
theorem ae_lc : LocallyCompactSpace (AE F E) := ae_top.2.1
theorem ae_sc : SecondCountableTopology (AE F E) := ae_top.2.2

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc

theorem units_top {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : LocallyCompactSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  haveI : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem ua_top {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  obtain ⟨h1, h2⟩ := units_top (A := Matrix (Fin n) (Fin n) (AE F E))
  have hc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  exact ⟨this.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _⟩

theorem af_ext_k {a b : AF F} (h1 : a.1 = b.1) (h2 : ∀ v, evFin F v a = evFin F v b) : a = b :=
  Prod.ext h1 (FiniteAdeleRing.ext _ h2)

theorem evFin_idem_self_k (v : Pl F) : evFin F v (idem F v) = 1 := evalV_singleFin_self v 1
theorem evFin_idem_ne_k {v u : Pl F} (h : u ≠ v) : evFin F u (idem F v) = 0 := evalV_singleFin_ne h 1
theorem real_fst : (realAd F 1).1 = 1 := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ (1 : ℝ)) = 1
  rw [map_one, map_one]
theorem evFin_real_k (v : Pl F) : evFin F v (realAd F 1) = 0 := map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem mul_idem_zero {v : Pl F} {u : AF F} (h : evFin F v u = 0) : u * idem F v = 0 :=
  af_ext_k (mul_zero u.1) fun w => by
    rw [map_mul, map_zero]
    by_cases e : w = v
    · subst e; rw [h, zero_mul]
    · rw [evFin_idem_ne_k e, mul_zero]

theorem mul_real_zero {u : AF F} (h : u.1 = 0) : u * realAd F 1 = 0 :=
  af_ext_k (show u.1 * (realAd F 1).1 = 0 by rw [h, zero_mul]) fun w => by rw [map_mul, evFin_real_k, mul_zero, map_zero]

theorem idem_idem (v : Pl F) : idem F v * idem F v = idem F v := by
  have := mul_idem_zero (v := v) (u := 1 - idem F v) (by rw [map_sub, map_one, evFin_idem_self_k, sub_self])
  linear_combination -this

theorem real_idem : realAd F 1 * realAd F 1 = realAd F 1 := by
  have := mul_real_zero (u := 1 - realAd F 1) (show (1 : Ainf F) - (realAd F 1).1 = 0 by rw [real_fst, sub_self])
  linear_combination -this

theorem idem_orth {v u : Pl F} (h : v ≠ u) : idem F v * idem F u = 0 := mul_idem_zero (evFin_idem_ne_k h.symm)
theorem idem_real (v : Pl F) : idem F v * realAd F 1 = 0 := mul_real_zero rfl

theorem at_fin_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} : At (evFin F v) z ↔ idem F v • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_idem_zero hu, zero_smul]⟩
  have := h (1 - idem F v) (by rw [map_sub, map_one, evFin_idem_self_k, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem evI_zero_k {u : AF F} : evI F u = 0 ↔ u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff

theorem at_inf_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evI F) z ↔ realAd F 1 • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_real_zero (evI_zero_k.1 hu), zero_smul]⟩
  have := h (1 - realAd F 1) (evI_zero_k.2 (show (1 : Ainf F) - (realAd F 1).1 = 0 by rw [real_fst, sub_self]))
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem fix_iff {R A : Type} [CommRing R] [Ring A] [Algebra R A] (a : R) (x : A) :
    a • (x - 1) = x - 1 ↔ a • x + (1 - a) • (1 : A) = x := by
  rw [smul_sub, sub_smul, one_smul]
  constructor <;> intro h
  · rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  · conv_rhs => rw [← h]
    abel

def rest (T : Finset (Pl F)) : AF F := 1 - realAd F 1 - ∑ v ∈ T, idem F v

theorem rest_fst (T : Finset (Pl F)) : (rest T).1 = 0 := by
  have : ∀ a : AF F, a.1 = fstA F a := fun _ => rfl
  rw [this, rest, map_sub, map_sub, map_one, map_sum, ← this, real_fst, sub_self, zero_sub, neg_eq_zero]
  exact Finset.sum_eq_zero fun v _ => rfl

open Classical in
theorem evFin_rest (T : Finset (Pl F)) (v : Pl F) : evFin F v (rest T) = if v ∈ T then 0 else 1 := by
  rw [rest, map_sub, map_sub, map_one, map_sum, evFin_real_k, sub_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem v h fun u _ hu => evFin_idem_ne_k hu.symm, evFin_idem_self_k, sub_self]
  · rw [Finset.sum_eq_zero fun u hu => evFin_idem_ne_k (fun e : v = u => h (by rw [e]; exact hu)), sub_zero]

theorem rest_idem (T : Finset (Pl F)) : rest T * rest T = rest T :=
  af_ext_k (show (rest T).1 * (rest T).1 = (rest T).1 by rw [rest_fst, mul_zero]) fun v => by
    rw [map_mul, evFin_rest]; split_ifs <;> simp

theorem idem_rest {T : Finset (Pl F)} {v : Pl F} (h : v ∈ T) : idem F v * rest T = 0 := by
  rw [mul_comm]; exact mul_idem_zero (by rw [evFin_rest, if_pos h])

theorem real_rest (T : Finset (Pl F)) : realAd F 1 * rest T = 0 := by rw [mul_comm]; exact mul_real_zero (rest_fst T)

theorem sum_rest (T : Finset (Pl F)) : rest (∅ : Finset (Pl F)) = ∑ v ∈ T, idem F v + rest T := by
  simp [rest]

theorem real_add_rest : realAd F 1 + rest (∅ : Finset (Pl F)) = 1 := by simp [rest]

variable {n : ℕ}

variable (σ) in

def PU (J : Matrix (Fin n) (Fin n) E) (a : AF F) : UA σ J →* UA σ J :=
  ((unitP (A := Matrix (Fin n) (Fin n) (AE F E)) a).comp (Subgroup.subtype _)).codRestrict _ fun g => by
    by_cases h : a * a = a
    · show (unitP a g.1 : Matrix _ _ _)ᵀ * incM F J * (unitP a g.1 : Matrix _ _ _).map (cA σ) = incM F J
      have hg : (g.1 : Matrix _ _ _)ᵀ * incM F J * (g.1 : Matrix _ _ _).map (cA σ) = incM F J := g.2
      have e : (a • (g.1 : Matrix (Fin n) (Fin n) (AE F E)) + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) =
          a • (g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply]
        split_ifs <;> simp
      have h1 : a * (1 - a) = 0 := by linear_combination -h
      have h2 : (1 - a) * a = 0 := by linear_combination -h
      have h3 : (1 - a) * (1 - a) = 1 - a := by linear_combination h
      rw [coe_unitP h, e]
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h, h1, h2, h3, zero_smul, Matrix.one_mul, Matrix.mul_one, hg,
        add_zero, zero_add]
      rw [← add_smul]; simp
    · unfold unitP; rw [dif_neg h]; exact Subgroup.one_mem _

theorem mat_PU {J : Matrix (Fin n) (Fin n) E} {a : AF F} (h : a * a = a) (g : UA σ J) :
    mat (PU σ J a g) = a • mat g + (1 - a) • (1 : Matrix _ _ (AE F E)) := coe_unitP h g.1

def Gd (a : AF F) : Prop := a * a = a ∧ (a.1 = 0 ∨ a.1 = 1)

theorem piInf_alg {w : InfinitePlace F} (τ : EmbOver E w) {a b : AF F} (h : a.1 = b.1) (x : AE F E) :
    piInf τ (a • x) = piInf τ (b • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
  congr 1
  show infEmb τ (GlobalTheory.AutFunCompare.evW w a.1 ⊗ₜ[F] (1 : E)) = infEmb τ (GlobalTheory.AutFunCompare.evW w b.1 ⊗ₜ[F] (1 : E))
  rw [h]

theorem smul_latHat (X : Spc F E n) {a : AF F} (h : a * a = a) {z} (hz : z ∈ latHat X) : a • z ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hv, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, evI_zero_k.2 (show a.1 * b.1 = 0 by rw [evI_zero_k.1 hb, mul_zero]), fun v => ?_, x, hx,
      smul_smul _ _ _⟩
    rw [map_mul]
    refine mul_mem ?_ (hv v)
    have : IsIdempotentElem (evFin F v a) := by show _ * _ = _; rw [← map_mul, h]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 this with e | e <;> rw [e]
    exacts [zero_mem _, one_mem _]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem PU_mem {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {a : AF F} (ha : Gd a) {g} (hg : g ∈ K) :
    PU σ X.J a g ∈ K := by
  obtain ⟨h1, h2⟩ := (hK g).1 hg
  have ha' : (1 - a) * (1 - a) = 1 - a := by linear_combination ha.1
  have key : ∀ g : UA σ X.J, ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X → mat (PU σ X.J a g) *ᵥ z ∈ latHat X := fun g z hz h => by
    rw [mat_PU ha.1, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact add_mem (smul_latHat X ha.1 h) (smul_latHat X ha' hz)
  refine (hK _).2 ⟨fun w => ?_, fun z hz => ⟨key g z hz (h2 z hz).1, by rw [← map_inv]; exact key _ z hz (h2 z hz).2⟩⟩
  rcases ha.2 with e | e
  · have : (mat (PU σ X.J a g)).map (piInf (B.emb w)) = 1 := by
      rw [mat_PU ha.1, ← Matrix.map_one (piInf (B.emb w)) (map_zero _) (map_one _)]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add]
      rw [piInf_alg _ (b := 0) e, piInf_alg _ (a := 1 - a) (b := 1) (show (1 : Ainf F) - a.1 = 1 by rw [e, sub_zero])]
      simp
    rw [this]; exact Commute.one_left _
  · have : (mat (PU σ X.J a g)).map (piInf (B.emb w)) = (mat g).map (piInf (B.emb w)) := by
      rw [mat_PU ha.1]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add]
      rw [piInf_alg _ (b := 1) e, piInf_alg _ (a := 1 - a) (b := 0) (show (1 : Ainf F) - a.1 = 0 by rw [e, sub_self])]
      simp
    rw [this]; exact h1 w

theorem Gd.add {a b : AF F} (ha : Gd a) (hb : Gd b) (h : a * b = 0) : Gd (a + b) := by
  refine ⟨idem_add ha.1 hb.1 h, ?_⟩
  have h' : a.1 * b.1 = 0 := congrArg Prod.fst h
  show a.1 + b.1 = 0 ∨ a.1 + b.1 = 1
  rcases ha.2 with e | e
  · rw [e, zero_add]; exact hb.2
  · rw [e, one_mul] at h'; rw [e, h', add_zero]; exact Or.inr rfl

theorem gd_idem (v : Pl F) : Gd (idem F v) := ⟨idem_idem v, Or.inl rfl⟩
theorem gd_real : Gd (realAd F 1) := ⟨real_idem, Or.inr real_fst⟩
theorem gd_rest (T : Finset (Pl F)) : Gd (rest T) := ⟨rest_idem T, Or.inl (rest_fst T)⟩

theorem borelUA (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem sysU {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (hc : IsCompact (K : Set (UA σ X.J))) :
    Sys (PU σ X.J) K Set.univ Gd where
  cont a ha := ((unitInvariant_continuous ha.1).comp continuous_subtype_val).subtype_mk _
  comp a b ha hb g := Subtype.ext (unitInvariant_comp ha.1 hb.1 g.1)
  zero g := Subtype.ext (unitInvariant_zero g.1)
  add a b ha hb h := ⟨ha.add hb h, fun g => Subtype.ext (unitInvariant_add ha.1 hb.1 h g.1)⟩
  idem a ha := ha.1
  cK := hc.isClosed
  mK a ha g hg := PU_mem hK ha hg
  mU := MeasurableSet.univ
  one := trivial
  mul _ _ _ _ := trivial
  pU _ _ _ _ := trivial

theorem kAt_eq {X : Spc F E n} (K : Subgroup (UA σ X.J)) {R : Type} [Zero R] (ev : AF F → R) {a : AF F} (h : a * a = a)
    (hat : ∀ z : Matrix (Fin n) (Fin n) (AE F E), At ev z ↔ a • z = z) : kAt K ev = part (PU σ X.J) K a := by
  have : UAt σ X ev = ((PU σ X.J a).eqLocus (MonoidHom.id _) : Set _) := Set.ext fun g => by
    show At ev (mat g - 1) ↔ PU σ X.J a g = g
    rw [hat, fix_iff, ← mat_PU h]
    exact ⟨fun e => Subtype.ext (Units.ext e), fun e => congrArg mat e⟩
  rw [kAt, this, Subgroup.closure_eq, part]

theorem co_U {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (hc : IsCompact (K : Set (UA σ X.J)))
    {a : AF F} (ha : Gd a) : CO (PU σ X.J) K Set.univ a := by
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  haveI : CompactSpace (part (PU σ X.J) K a) :=
    isCompact_iff_compactSpace.1 (hc.of_isClosed_subset ((sysU hK hc).closed ha) fun _ h => h.1)
  exact ⟨isCompact_univ, isOpen_univ⟩

theorem stab_compact (hS : StabEx) {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) : IsCompact (K : Set (UA σ X.J)) := by
  obtain ⟨K', -, -, h1, h2, -⟩ := hS F E σ B n X r s hB hX
  have : K = K' := Subgroup.ext fun g => (hK g).trans (h1 g).symm
  exact this ▸ h2

def ext0 {G : Type} [Group G] (S : Subgroup G) (f : S → ℂ) : G → ℂ := Function.extend Subtype.val f 0

theorem extendByZeroOnSubset_apply_coe {G : Type} [Group G] {S : Subgroup G} (f : S → ℂ) (x : S) : ext0 S f x = f x :=
  Subtype.val_injective.extend_apply _ _ _

theorem extendByZero_restrict_alt {G : Type} [Group G] {S : Subgroup G} (f : S → ℂ) : (fun x : S => ext0 S f x) = f := funext (extendByZeroOnSubset_apply_coe f)

theorem kFub_of (hS : StabEx) : KFub := by
  classical
  intro F E _ _ _ _ _ σ B n X r s hB hX K m μK hK hm hμ
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  have hc := stab_compact hS hB hX hK
  have sy := sysU hK hc
  have ei := kAt_eq K (evI F) real_idem fun _ => at_inf_iff
  have ef := fun v => kAt_eq K (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have e1 : K = part (PU σ X.J) K (realAd F 1 + rest ∅) := by
    rw [real_add_rest]; exact Subgroup.ext fun g => ⟨fun h => ⟨h, Subtype.ext (unitInvariant_one g.1)⟩, fun h => h.1⟩
  have sp := sy.split gd_real (gd_rest ∅) (real_rest ∅)
  obtain ⟨μ', m1, -, m3⟩ := transport e1 _ BorelSpace.measurable_eq μK
  obtain ⟨α, a1, -, a3⟩ := transport ei _ BorelSpace.measurable_eq m.ki
  choose γ g1 g2 g3 using fun v => transport (ef v) _ BorelSpace.measurable_eq (m.kf v)
  have hex := fun T => exists_haar _ (sy.closed (gd_rest T)) Set.univ trivial (co_U hK hc (gd_rest T)).1 (co_U hK hc (gd_rest T)).2
  choose β hβ using hex
  haveI := m1 hμ; haveI := a1 hm.ki; haveI := (hβ ∅).1
  obtain ⟨c, c0, c1, -⟩ := sp.fub μ' α (β ∅)
  refine ⟨fun k => ⟨PU σ X.J _ k, ei ▸ sp.mA _ (e1 ▸ k.2)⟩, fun v k => ⟨PU σ X.J (idem F v) k, (ef v) ▸
    ⟨sy.mK _ (gd_idem v) _ k.2, by show PU σ X.J _ (PU σ X.J _ _) = _; rw [sy.comp _ _ (gd_idem v) (gd_idem v), idem_idem]; rfl⟩⟩,
    c, by exact_mod_cast c0, fun k => ⟨mat_PU real_idem _, fun v => mat_PU (idem_idem v) _⟩, fun T hi h i1 i2 => ?_⟩
  have hu : β T Set.univ = 1 := (hβ T).2
  haveI : IsFiniteMeasure (β T) := ⟨hu.trans_lt ENNReal.one_lt_top⟩
  obtain ⟨p1, p2⟩ := sy.prod (idem F) gd_idem (fun _ _ => idem_orth) (rest T) (gd_rest T) γ
    (fun v => ⟨g1 v (hm.kf v).1, (g2 v Set.univ).trans (hm.kf v).2⟩) (β T) (hβ T) T (fun v => idem_rest)
    (fun T' h => co_U hK hc (sy.good_sum _ gd_idem (fun _ _ => idem_orth) _ (gd_rest T) T' fun v hv => idem_rest (h hv)))
    _ (sum_rest T) (β ∅) (hβ ∅) (fun v => ext0 _ (h v)) (fun _ => 1)
    (fun v hv => (g3 v _).1.2 (by rw [extendByZero_restrict_alt]; exact i2 v hv)) (integrable_const _)
  obtain ⟨q1, q2⟩ := c1 (ext0 _ hi) (fun y => (∏ v ∈ T, ext0 _ (h v) (PU σ X.J (idem F v) y)) * 1) ((a3 _).1.2 (by rw [extendByZero_restrict_alt]; exact i1)) p1
  have hb : ∫ _ : part (PU σ X.J) K (rest T), (1 : ℂ) ∂(β T) = 1 := by
    rw [integral_const, Measure.real, hu]; simp
  rw [p2, hb, (a3 _).2, extendByZero_restrict_alt] at q2
  simp only [fun v => (g3 v (ext0 _ (h v))).2, extendByZero_restrict_alt] at q2
  have hr : ∀ v, idem F v * rest ∅ = idem F v := fun v => by
    rw [rest, Finset.sum_empty, sub_zero, mul_sub, idem_real, mul_one, sub_zero]
  have := m3 fun x => ext0 _ hi (PU σ X.J (realAd F 1) x) *
    ((∏ v ∈ T, ext0 _ (h v) (PU σ X.J (idem F v) (PU σ X.J (rest ∅) x))) * 1)
  rw [this.1] at q1
  rw [this.2] at q2
  simp only [fun v x => sy.comp _ _ (gd_idem v) (gd_rest ∅) x, hr, mul_one] at q1 q2
  simp only [← extendByZeroOnSubset_apply_coe hi, ← fun v => extendByZeroOnSubset_apply_coe (h v)]
  refine ⟨q1, q2.trans ?_⟩
  simp only [extendByZeroOnSubset_apply_coe]; ring

end PositivityTheory.ThKG.Loc.Cone

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Fub

open MeasureTheory Topology Filter

theorem one_of_compact {G : Type} [Group G] [TopologicalSpace G] (f : G →* NNReal) (hf : Continuous f) {K : Set G} (hK : IsCompact K)
    {x : G} (hx : ∀ n : ℤ, x ^ n ∈ K) : f x = 1 := by
  obtain ⟨C, hC⟩ := (hK.image hf).bddAbove
  have key : ∀ y : G, (∀ n : ℕ, y ^ n ∈ K) → f y ≤ 1 := fun y hy => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hC ⟨_, hy n, map_pow f y n⟩) (not_le.2 hn)
  have h1 := key x fun n => by simpa using hx n
  have h2 := key x⁻¹ fun n => by simpa using hx (-n)
  have h3 : f x * f x⁻¹ = 1 := by rw [← map_mul]; simp
  refine le_antisymm h1 ?_
  calc (1 : NNReal) = f x * f x⁻¹ := h3.symm
    _ ≤ f x * 1 := by gcongr
    _ = f x := mul_one _

theorem circle_one {z : Circle} (h : ∀ n : ℕ, ‖((z ^ n : Circle) : ℂ) - 1‖ < 1) : z = 1 := by
  by_contra hz
  have h0 : (z : ℂ) - 1 ≠ 0 := fun e => hz (Circle.coe_eq_one.1 (sub_eq_zero.1 e))
  have hre : ∀ n : ℕ, 1 / 2 < ((z : ℂ) ^ n).re := fun n => by
    have h1 := h n
    rw [Circle.coe_pow] at h1
    have h2 : ‖(z : ℂ) ^ n‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
    have h3 := Complex.sq_norm ((z : ℂ) ^ n - 1)
    have h4 := Complex.sq_norm ((z : ℂ) ^ n)
    rw [Complex.normSq_apply] at h3 h4
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3
    nlinarith [norm_nonneg ((z : ℂ) ^ n - 1)]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖(z : ℂ) - 1‖)
  have hp : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.2 h0
  have e : (∑ i ∈ Finset.range N, (z : ℂ) ^ i) * (z - 1) = z ^ N - 1 := geom_sum_mul _ _
  have h1 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, (z : ℂ) ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range N) (fun i => ((z : ℂ) ^ i).re) (1 / 2) fun i _ => (hre i).le
    simpa [div_eq_mul_inv] using this
  have h2 : ‖(z : ℂ) ^ N - 1‖ < 1 := by simpa using h N
  rw [← e, norm_mul] at h2
  rw [div_lt_iff₀ hp] at hN
  nlinarith

theorem pow_mem_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {x : G} (hx : ∀ n : ℕ, x ^ n ∈ K) : ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hf : ((QuotientGroup.mk : G → G ⧸ U) '' K).Finite := (hK.image QuotientGroup.continuous_mk).finite_of_discrete
  obtain ⟨i, j, hij, e⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => (QuotientGroup.mk (x ^ n) : G ⧸ U))
    (fun n => Set.mem_image_of_mem _ (hx n)) hf
  refine ⟨j - i, by omega, ?_⟩
  have := QuotientGroup.eq.1 e
  rwa [show x ^ j = x ^ i * x ^ (j - i) by rw [← pow_add]; congr 1; omega, inv_mul_cancel_left] at this

theorem tate {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [γ.IsMulLeftInvariant] (o : H → ℤ) (ho : ∀ x y, o (x * y) = o x + o y) (hU : IsOpen {x | o x = 0})
    (h1 : γ {x | o x = 0} = 1) (ϖ : H) (hϖ : o ϖ = 1) (χ : H →* ℂ) (hχ : ∀ x, o x = 0 → χ x = 1) (ht : ‖χ ϖ‖ < 1) (m : ℤ) :
    Integrable (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) γ ∧
      ∫ x, (if m ≤ o x then (1 : ℂ) else 0) * χ x ∂γ = χ ϖ ^ m * (1 - χ ϖ)⁻¹ := by
  let O : H →* Multiplicative ℤ := MonoidHom.mk' (fun x => Multiplicative.ofAdd (o x)) fun x y => by rw [ho]; rfl
  have oz : ∀ (k : ℤ) x, o (ϖ ^ k * x) = k + o x := fun k x => by
    have := map_zpow O ϖ k
    have h2 : o (ϖ ^ k) = k := by
      have h3 := congrArg Multiplicative.toAdd this
      simpa [O, hϖ] using h3
    rw [ho, h2]
  have h0 : χ ϖ ≠ 0 := fun e => by
    have := map_mul χ ϖ ϖ⁻¹
    rw [mul_inv_cancel, map_one, e, zero_mul] at this
    exact one_ne_zero this
  let A : ℕ → Set H := fun k => {x | o x = m + k}
  have hA : ∀ k, A k = (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0} := fun k => Set.ext fun x => by
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage, oz]; omega
  have mA : ∀ k, MeasurableSet (A k) := fun k => by
    rw [hA]; exact (hU.preimage (continuous_const.mul continuous_id)).measurableSet
  have vA : ∀ k, γ (A k) = 1 := fun k => by rw [hA, measure_preimage_mul, h1]
  have cA : ∀ k, ∀ x ∈ A k, χ x = χ ϖ ^ m * χ ϖ ^ k := fun k x hx => by
    have := hχ _ ((hA k ▸ hx : x ∈ (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0}))
    rw [map_mul, map_zpow, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _ h0)] at this
    rw [← this, zpow_add₀ h0, zpow_natCast]
  have dA : Pairwise (Function.onFun Disjoint A) := fun i j hij => Set.disjoint_left.2 fun x h h' => hij (by
    simp only [A, Set.mem_setOf_eq] at h h'; omega)
  have eU : (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) = (⋃ k, A k).indicator χ := funext fun x => by
    by_cases h : m ≤ o x
    · rw [if_pos h, one_mul, Set.indicator_of_mem (Set.mem_iUnion.2 ⟨(o x - m).toNat, by simp only [A, Set.mem_setOf_eq]; omega⟩)]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem fun h' => by
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h'
        simp only [A, Set.mem_setOf_eq] at hk; omega]
  have iA : ∀ k, IntegrableOn χ (A k) γ := fun k =>
    (integrableOn_const (C := χ ϖ ^ m * χ ϖ ^ k) (by rw [vA]; simp)).congr_fun (fun x hx => (cA k x hx).symm) (mA k)
  have sA : ∀ k, ∫ x in A k, χ x ∂γ = χ ϖ ^ m * χ ϖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (cA k), setIntegral_const, Measure.real, vA]; simp
  have nA : ∀ k, ∫ x in A k, ‖χ x‖ ∂γ = ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (g := fun _ => ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k) fun x hx => by simp only [cA k x hx, norm_mul, norm_pow],
      setIntegral_const, Measure.real, vA]; simp
  have iU : IntegrableOn χ (⋃ k, A k) γ := integrableOn_iUnion_of_summable_integral_norm iA (by
    simp only [nA]; exact (summable_geometric_of_lt_one (norm_nonneg _) ht).mul_left _)
  rw [eU, integrable_indicator_iff (MeasurableSet.iUnion mA), integral_indicator (MeasurableSet.iUnion mA)]
  refine ⟨iU, (hasSum_integral_iUnion mA dA iU).unique ?_⟩
  simp only [sA]
  exact (hasSum_geometric_of_norm_lt_one ht).mul_left _

end PositivityTheory.ThKG.Fub

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub GlobalTheory.Doubling

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc

theorem id_lc : LocallyCompactSpace (AE F E)ˣ := units_top.1
theorem id_sc : SecondCountableTopology (AE F E)ˣ := units_top.2
theorem id_borel : BorelSpace (AE F E)ˣ := ⟨rfl⟩

attribute [local instance] id_lc id_sc id_borel

variable (F E) in

def fc : AE F E →+* FiniteAdeleRing (𝓞 E) E := (finAdEquiv F E).toRingHom.comp (finTens F E)

def cw (w : HeightOneSpectrum (𝓞 E)) : AE F E →+* w.adicCompletion E := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E w).toRingHom.comp (fc F E)

theorem cw_def (w : HeightOneSpectrum (𝓞 E)) (x : AE F E) : cw w x = finAdEquiv F E (finTens F E x) w := rfl

theorem ae_ext {x y : AE F E} (h1 : infTens F E x = infTens F E y) (h2 : ∀ w, cw w x = cw w y) : x = y :=
  tens_ext h1 ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ h2))

theorem cw_eq {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (x : AE F E) : cw w x = toCompl h (compFin F E v x) := by
  rw [cw_def, finAdEquiv_apply h]
  congr 1
  change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
  rw [← Algebra.TensorProduct.map_comp]
  rfl

theorem continuous_fc : Continuous (fc F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : LocallyCompactSpace (Af F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (Af F ⊗[F] E) := e0.isEmbedding.t2Space
  have ho : IsOpenMap (finAdEquiv F E).symm :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (finAdEquiv F E).symm.toAddEquiv.toAddMonoidHom (finAdEquiv F E).symm.surjective
      continuous_finAdEquiv_symm
  have h1 : Continuous (finAdEquiv F E) :=
    ((finAdEquiv F E).symm.toEquiv.toHomeomorphOfContinuousOpen continuous_finAdEquiv_symm ho).symm.continuous
  exact h1.comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (sndA F).toLinearMap (map_mul (sndA F)) continuous_snd)

def io (a : AF F) : AE F E := algebraMap (AF F) (AE F E) a

theorem cw_io (w : HeightOneSpectrum (𝓞 E)) (a : AF F) : cw w (io a : AE F E) = complMap rfl (evFin F (w.under (𝓞 F)) a) :=
  (finAdEquiv_tmul a.2 (1 : E) w).trans (by rw [map_one, mul_one]; rfl)

theorem inf_io {a : AF F} (h : a.1 = 0) : infTens F E (io a) = 0 := by
  show a.1 ⊗ₜ[F] (1 : E) = 0
  rw [h, TensorProduct.zero_tmul]

theorem io_mul (a b : AF F) : (io a * io b : AE F E) = io (a * b) := (map_mul _ _ _).symm
theorem io_idem {a : AF F} (h : a * a = a) : (io a * io a : AE F E) = io a := by rw [io_mul, h]
theorem io_orth {a b : AF F} (h : a * b = 0) : (io a * io b : AE F E) = 0 := by rw [io_mul, h]; exact map_zero _

variable (F) in

def ew (w : HeightOneSpectrum (𝓞 E)) : AE F E := extZero F E ((finAdEquiv F E).symm (1 - Neutral.B1.finiteSingle E w 0))

theorem inf_ew (w : HeightOneSpectrum (𝓞 E)) : infTens F E (ew F w) = 0 := infTens_extZero _

open Classical in
theorem cw_ew (u w : HeightOneSpectrum (𝓞 E)) : cw u (ew F w) = if u = w then 1 else 0 := by
  rw [cw_def, ew, finTens_extZero, RingEquiv.apply_symm_apply]
  show 1 - Neutral.B1.finiteSingle E w 0 u = _
  split_ifs with h
  · subst h; rw [finSingle_self, sub_zero]
  · rw [finSingle_ne h, sub_self]

theorem ew_idem (w : HeightOneSpectrum (𝓞 E)) : ew F w * ew F w = ew F w :=
  ae_ext (by rw [map_mul, inf_ew, mul_zero]) fun u => by rw [map_mul, cw_ew]; split_ifs <;> simp

theorem ew_orth {w w' : HeightOneSpectrum (𝓞 E)} (h : w ≠ w') : ew F w * ew F w' = 0 :=
  ae_ext (by rw [map_mul, inf_ew, zero_mul, map_zero]) fun u => by
    rw [map_mul, cw_ew, cw_ew, map_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    all_goals simp

open Classical in
theorem cw_idem (w : HeightOneSpectrum (𝓞 E)) (v : Pl F) : cw w (io (idem F v) : AE F E) = if w.under (𝓞 F) = v then 1 else 0 := by
  rw [cw_io]
  split_ifs with h
  · subst h; rw [evFin_idem_self_k, map_one]
  · rw [evFin_idem_ne_k h, map_zero]

open Classical in
theorem cw_rest (w : HeightOneSpectrum (𝓞 E)) (T : Finset (Pl F)) :
    cw w (io (rest T) : AE F E) = if w.under (𝓞 F) ∈ T then 0 else 1 := by
  rw [cw_io, evFin_rest]; split_ifs <;> simp

theorem idem_eq_sum (v : Pl F) : (io (idem F v) : AE F E) = ∑ w ∈ Formalism.L2.Host.aboveF (L := E) F v, ew F w + 0 := by
  classical
  refine ae_ext (by rw [inf_io rfl, add_zero, map_sum, Finset.sum_eq_zero fun w _ => inf_ew w]) fun u => ?_
  rw [add_zero, map_sum, cw_idem]
  simp only [cw_ew, Finset.sum_ite_eq, mem_aboveF]

abbrev PI (a : AE F E) : (AE F E)ˣ →* (AE F E)ˣ := unitP (R := AE F E) a

theorem hom_PI {A : Type} [CommRing A] (φ : AE F E →+* A) {a : AE F E} (h : a * a = a) (l : (AE F E)ˣ) :
    φ (PI a l) = φ a * φ l + (1 - φ a) := by
  rw [coe_unitP h]; simp

theorem cw_PI_one {a : AE F E} (h : a * a = a) {w} (h1 : cw w a = 1) (l : (AE F E)ˣ) : cw w (PI a l : AE F E) = cw w (l : AE F E) := by
  rw [hom_PI _ h, h1]; simp

theorem cw_PI_zero {a : AE F E} (h : a * a = a) {w} (h1 : cw w a = 0) (l : (AE F E)ˣ) : cw w (PI a l : AE F E) = 1 := by
  rw [hom_PI _ h, h1]; simp

theorem cw_cases {a : AE F E} (h : a * a = a) (w) : cw w a = 0 ∨ cw w a = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.1 (show _ * _ = _ by rw [← map_mul, h])

def vw (w : HeightOneSpectrum (𝓞 E)) (l : (AE F E)ˣ) : WithZero (Multiplicative ℤ) := Valued.v (cw w (l : AE F E))

theorem vw_mul (w) (l l' : (AE F E)ˣ) : vw w (l * l') = vw w l * vw w l' := by simp [vw]
theorem vw_one (w) : vw w (1 : (AE F E)ˣ) = 1 := by simp [vw]
theorem vw_inv (w) (l : (AE F E)ˣ) : vw w l * vw w l⁻¹ = 1 := by rw [← vw_mul, mul_inv_cancel, vw_one]
theorem vw_ne (w) (l : (AE F E)ˣ) : vw w l ≠ 0 := left_ne_zero_of_mul_eq_one (vw_inv w l)

variable (F E) in

def UI : Subgroup (AE F E)ˣ where
  carrier := {l | ∀ w, vw w l = 1}
  one_mem' := vw_one
  mul_mem' h h' w := by rw [vw_mul, h w, h' w, one_mul]
  inv_mem' {l} h w := by have := vw_inv w l; rwa [h w, one_mul] at this

theorem mem_UI_iff (l : (AE F E)ˣ) : l ∈ UI F E ↔ (∀ w, vw w l ≤ 1) ∧ ∀ w, vw w l⁻¹ ≤ 1 :=
  ⟨fun h => ⟨fun w => (h w).le, fun w => ((UI F E).inv_mem h w).le⟩, fun h w => le_antisymm (h.1 w) (by
    calc 1 = vw w l * vw w l⁻¹ := (vw_inv w l).symm
      _ ≤ vw w l * 1 := mul_le_mul_right (h.2 w) _
      _ = vw w l := mul_one _)⟩

theorem isOpen_UI : IsOpen (UI F E : Set (AE F E)ˣ) := by
  have h : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w} :=
    RestrictedProduct.isOpen_forall_mem fun w => Valued.isOpen_integer _
  have h1 := h.preimage (continuous_fc (F := F))
  have : (UI F E : Set (AE F E)ˣ) = (Units.val ⁻¹' (fc F E ⁻¹' {a | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w})) ∩ ((fun l : (AE F E)ˣ => ((l⁻¹ : (AE F E)ˣ) : AE F E)) ⁻¹'
      (fc F E ⁻¹' {a | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w})) := Set.ext fun l => mem_UI_iff l
  rw [this]
  exact (h1.preimage Units.continuous_val).inter (h1.preimage Units.continuous_coe_inv)

theorem sysI : Sys (PI (F := F) (E := E)) ⊤ (UI F E) fun a => a * a = a where
  cont a ha := unitInvariant_continuous ha
  comp a b ha hb := unitInvariant_comp ha hb
  zero := unitInvariant_zero
  add a b ha hb h := ⟨idem_add ha hb h, unitInvariant_add ha hb h⟩
  idem _ h := h
  cK := isClosed_univ
  mK _ _ _ _ := trivial
  mU := isOpen_UI.measurableSet
  one := (UI F E).one_mem
  mul _ h _ h' := (UI F E).mul_mem h h'
  pU a ha l hl w := by
    rcases cw_cases ha w with e | e
    · rw [vw, cw_PI_zero ha e, map_one]
    · rw [vw, cw_PI_one ha e]; exact hl w

theorem inf_of_part {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) {l : (AE F E)ˣ} (h : l ∈ part PI ⊤ a) :
    infTens F E l = 1 := by
  rw [← show PI a l = l from h.2, hom_PI _ ha, h0]; simp

theorem cpt_I {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) :
    IsCompact ((part PI ⊤ a : Set (AE F E)ˣ) ∩ UI F E) := by
  let j : FiniteAdeleRing (𝓞 E) E → AE F E := fun y => 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm y)
  have hj : Continuous j := continuous_const.add (continuous_extZero.comp continuous_finAdEquiv_symm)
  have hS := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties E).1.image hj
  have hc := hS.prod (hS.image MulOpposite.continuous_op)
  have key : ∀ l ∈ (part PI ⊤ a : Set (AE F E)ˣ) ∩ UI F E, ∃ y, (∀ w, y w ∈ HeightOneSpectrum.adicCompletionIntegers E w) ∧
      j y = (l : AE F E) := fun l hl => ⟨fc F E l, fun w => (hl.2 w).le, tens_ext
        (by rw [inf_of_part ha h0 hl.1, map_add, map_sub, map_one, infTens_extZero, infTens_extZero, sub_zero, add_zero])
        (by rw [map_add, map_sub, map_one, finTens_extZero, finTens_extZero, sub_self, zero_add]
            exact (finAdEquiv F E).symm_apply_apply _)⟩
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage hc).of_isClosed_subset
    ((sysI.closed ha).inter ((UI F E).isClosed_of_isOpen isOpen_UI)) fun l hl => ⟨key l hl, _, key l⁻¹
      ⟨Subgroup.inv_mem _ hl.1, (UI F E).inv_mem hl.2⟩, rfl⟩

theorem co_I {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) : CO PI ⊤ (UI F E : Set (AE F E)ˣ) a := by
  refine ⟨?_, isOpen_UI.preimage continuous_subtype_val⟩
  have := (sysI.closed ha).isClosedEmbedding_subtypeVal.isCompact_preimage (cpt_I ha h0)
  exact this.of_isClosed_subset (((UI F E).isClosed_of_isOpen isOpen_UI).preimage continuous_subtype_val) fun x hx => ⟨x.2, hx⟩

theorem coe_PI_io {a : AF F} (h : a * a = a) (l : (AE F E)ˣ) :
    (PI (io a) l : AE F E) = a • (l : AE F E) + (1 - a) • (1 : AE F E) := by
  rw [coe_unitP (io_idem h), smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_sub, map_one]; rfl

theorem idAt_eq {R : Type} [Zero R] (ev : AF F → R) {a : AF F} (h : a * a = a) (hat : ∀ z : AE F E, At ev z ↔ a • z = z) :
    idAt E ev = part PI ⊤ (io a) := by
  have : {l : (AE F E)ˣ | At ev ((l : AE F E) - 1)} = ((part PI ⊤ (io a) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) := Set.ext fun l => by
    show At ev ((l : AE F E) - 1) ↔ l ∈ part PI ⊤ (io a)
    rw [hat, fix_iff, ← coe_PI_io h, mem_part]
    exact ⟨fun e => ⟨trivial, Units.ext e⟩, fun e => congrArg Units.val e.2⟩
  rw [idAt, this, Subgroup.closure_eq]

theorem units_eq (v : Pl F) : {l : idAt E (evFin F v) | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} =
    {l | l.1 ∈ (UI F E : Set (AE F E)ˣ)} := by
  have h := co_I (E := E) (io_idem (idem_idem v)) (inf_io rfl)
  rw [CO, ← idAt_eq (evFin F v) (idem_idem v) fun _ => at_fin_iff] at h
  refine Set.ext fun l => ⟨fun hl w => ?_, fun hl => h.1.of_isClosed_subset isClosed_closure (closure_minimal ?_ h.1.isClosed)⟩
  · obtain ⟨k, hk, hm⟩ := pow_mem_of_compact ((UI F E).subgroupOf _) h.2 hl fun n =>
      subset_closure (Subgroup.npow_mem_zpowers l n)
    have h1 : vw w (l.1 ^ k) = 1 := hm w
    rw [vw, Units.val_pow_eq_pow_val, map_pow, map_pow] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h1
  · rintro _ ⟨n, rfl⟩
    exact (UI F E).zpow_mem hl n

theorem measEx_of (hS : StabEx) : MeasEx := by
  intro F E _ _ _ _ _ σ B n X r s hB hX K hK
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  have hc := stab_compact hS hB hX hK
  have sy := sysU hK hc
  have ei := kAt_eq K (evI F) real_idem fun _ => at_inf_iff
  have ef := fun v => kAt_eq K (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have di := idAt_eq (E := E) (evI F) real_idem fun _ => at_inf_iff
  have df := fun v => idAt_eq (E := E) (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have h1 : ∀ {a}, Gd a → ∀ S, S = part (PU σ X.J) K a → ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ Set.univ = 1 := by
    rintro a ha S rfl
    exact exists_haar _ (sy.closed ha) Set.univ trivial (co_U hK hc ha).1 (co_U hK hc ha).2
  have h2 : ∀ S : Subgroup (AE F E)ˣ, ∀ P : Set S, (∃ μ : Measure S, μ.IsHaarMeasure ∧ μ P = 1) →
      ∃ μ : @Measure S (borel _), @Measure.IsHaarMeasure _ _ _ (borel _) μ ∧ μ P = 1 := fun S P h => by
    have : borel S = Subtype.instMeasurableSpace := (@BorelSpace.measurable_eq S _ Subtype.instMeasurableSpace (Subtype.borelSpace _)).symm
    rw [this]; exact h
  choose kf hkf using fun v => h1 (gd_idem v) _ (ef v)
  obtain ⟨ki, hki⟩ := h1 gd_real _ ei
  have h3 : ∀ v, ∃ μ : Measure (idAt E (evFin F v)), μ.IsHaarMeasure ∧ μ {l | l.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1 := fun v => by
    have h := co_I (E := E) (io_idem (idem_idem v)) (inf_io rfl)
    have hcl := sysI.closed (io_idem (E := E) (idem_idem v))
    rw [CO, ← df v] at h
    rw [← df v] at hcl
    exact exists_haar _ hcl _ (UI F E).one_mem h.1 h.2
  choose xf hxf using fun v => h2 _ _ (h3 v)
  haveI : LocallyCompactSpace (idAt E (evI F)) := by
    have hcl := sysI.closed (io_idem (E := E) (real_idem (F := F)))
    rw [← di] at hcl; exact hcl.locallyCompactSpace
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  haveI : BorelSpace (idAt E (evI F)) := ⟨rfl⟩
  exact ⟨⟨kf, xf, ki, Measure.haar⟩, hkf, fun v => ⟨(hxf v).1, by rw [units_eq]; exact (hxf v).2⟩, hki.1, inferInstance⟩

end PositivityTheory.ThKG.Loc.Cone

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub
open GlobalTheory.Doubling hiding npow norm_npow npow_ne_zero

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc id_lc id_sc id_borel

theorem mem_part_iff {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) (l : (AE F E)ˣ) :
    l ∈ part PI ⊤ a ↔ infTens F E l = 1 ∧ ∀ w, cw w a = 0 → cw w (l : AE F E) = 1 := by
  refine ⟨fun h => ⟨inf_of_part ha h0 h, fun w hw => by rw [← show PI a l = l from h.2]; exact cw_PI_zero ha hw l⟩,
    fun h => ⟨trivial, Units.ext (ae_ext (show infTens F E (PI a l : AE F E) = infTens F E l by rw [hom_PI _ ha, h0, h.1]; simp) fun w => ?_)⟩⟩
  rcases cw_cases ha w with e | e
  · exact (cw_PI_zero ha e l).trans (h.2 w e).symm
  · exact cw_PI_one ha e l

theorem PI_mem {a : AE F E} (ha : a * a = a) (l : (AE F E)ˣ) : PI a l ∈ part PI ⊤ a :=
  ⟨trivial, by show PI a (PI a l) = PI a l; rw [unitInvariant_comp ha ha, ha]⟩

theorem PI_sum {ι : Type} [DecidableEq ι] (e : ι → AE F E) (he : ∀ i, e i * e i = e i) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (c : AE F E) (hc : c * c = c) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0) (x : (AE F E)ˣ) :
    PI (∑ i ∈ T, e i + c) x = (∏ i ∈ T, PI (e i) x) * PI c x := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have hT' : ∀ j ∈ T, e j * c = 0 := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi, add_assoc, mul_assoc, ← ih hT']
    refine unitInvariant_add (he i) (sysI.good_sum e he ho c hc T hT') ?_ x
    rw [mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)), hT i (Finset.mem_insert_self _ _),
      add_zero]

def wtH (ν : Chr F E) (z : ℕ) : (AE F E)ˣ →* ℂ where
  toFun := wt ν z
  map_one' := by simp [wt]
  map_mul' a b := by simp only [wt, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring

theorem abs_UI {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) {l} (h : l ∈ part PI ⊤ a) (hu : l ∈ UI F E) : absE F E l = 1 :=
  one_of_compact (absE F E) continuous_absE (cpt_I ha h0) fun n => ⟨Subgroup.zpow_mem _ h n, Subgroup.zpow_mem _ hu n⟩

theorem cw_loc (u w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) :
    cw u (locIdele F w y : AE F E) = Neutral.B1.finiteSingle E w y u := by
  rw [cw_def, finTens_locIdele]; rfl

theorem ew_zero {u w : HeightOneSpectrum (𝓞 E)} : cw u (ew F w) = 0 ↔ u ≠ w := by
  rw [cw_ew]; split_ifs with h <;> simp [h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) : locIdele F w y ∈ part PI ⊤ (ew F w) :=
  (mem_part_iff (ew_idem w) (inf_ew w) _).2 ⟨infTens_locIdele w y, fun u hu => by rw [cw_loc, finSingle_ne (ew_zero.1 hu)]⟩

theorem nu_ew {ν : Chr F E} {w} (hν : UnrAt ν w) {l} (h : l ∈ part PI ⊤ (ew F w)) (hu : l ∈ UI F E) : ν l = 1 := by
  obtain ⟨h1, h2⟩ := (mem_part_iff (ew_idem w) (inf_ew w) _).1 h
  have e : l = locIdele F w (Units.map (cw w).toMonoidHom l) := Units.ext (ae_ext (h1.trans (infTens_locIdele _ _).symm) fun u => by
    rw [cw_loc]
    by_cases hu : u = w
    · subst hu; rw [finSingle_self]; rfl
    · rw [finSingle_ne hu, h2 u (ew_zero.2 hu)])
  have := hν (Units.map (cw w).toMonoidHom l) (hu w)
  rw [e]
  exact Circle.coe_eq_one.1 (congrArg Units.val this)

variable (F) in

def pw (w : HeightOneSpectrum (𝓞 E)) : (AE F E)ˣ := locIdele F w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))

theorem vw_pw (w : HeightOneSpectrum (𝓞 E)) : vw w (pw F w) = WithZero.exp (-1 : ℤ) := by
  rw [vw, pw, cw_loc, finSingle_self]; exact Formalism.L2.Host.unif_spec w

theorem abs_pw {B : Base F E} (hB : B.IsGood σ) (w : HeightOneSpectrum (𝓞 E)) :
    (absE F E (pw F w) : ℝ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hne : ∀ u, u ≠ w → cw u (pw F w : AE F E) = 1 := fun u hu => by rw [pw, cw_loc, finSingle_ne hu]
  have e : pw F w = ideleAt F E (w.under (𝓞 F)) (unitFin F E (w.under (𝓞 F)) (pw F w)) := by
    refine Units.ext (ae_ext ((infTens_locIdele _ _).trans (map_extUnit_zero (fstA F) _ _ (fun a => rfl) _).symm) fun u => ?_)
    by_cases hu : u.under (𝓞 F) = w.under (𝓞 F)
    · rw [cw_eq hu, cw_eq hu]
      exact congrArg _ (congrArg Units.val (unitFin_ideleAt_self _ (unitFin F E (w.under (𝓞 F)) (pw F w)))).symm
    · rw [hne u fun e => hu (e ▸ rfl), cw_eq rfl]
      rw [show compFin F E _ _ = 1 from congrArg Units.val (unitFin_ideleAt_ne hu _), map_one]
  have o1 : Formalism.UG.ordL (toCompl (rfl : w.under (𝓞 F) = _) (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = 1 := by
    have h : Valued.v (toCompl (rfl : w.under (𝓞 F) = _) (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = WithZero.exp (-1 : ℤ) := by
      rw [← vw_pw (F := F) w, vw, cw_eq rfl]; rfl
    rw [GlobalTheory.AbsInert.ordL_eq_neg_log (h ▸ WithZero.exp_ne_zero), h]; simp
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rw [e, absE_ideleAt]
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨u, hi⟩
  · obtain ⟨w₁, w₂, hn, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    obtain ⟨w', hw', h'⟩ : ∃ w', w ≠ w' ∧ w'.under (𝓞 F) = w.under (𝓞 F) := by
      by_cases h : w = w₁
      exacts [⟨w₂, h ▸ hn, h2⟩, ⟨w₁, h, h1⟩]
    have o2 : Formalism.UG.ordL (toCompl h' (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = 0 := by
      have h : toCompl h' (unitFin F E (w.under (𝓞 F)) (pw F w)).1 = 1 := (cw_eq h' _).symm.trans (hne w' hw'.symm)
      rw [h, GlobalTheory.AbsInert.ordL_eq_neg_log (by simp)]; simp
    rw [GlobalTheory.Doubling.AbsSplit.absEv_split F E σ hB.cm _ w rfl w' h' hw', o1, o2]
    simp [Formalism.UG.qV]
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hi w).1 rfl
    rw [GlobalTheory.AbsInert.absEv_inert F E σ hB.cm _ w rfl hi, o1, GlobalTheory.LFun.InertChart.absNorm_eq hB.cm.2.2.1 hi]
    simp [Formalism.UG.qV]

theorem wt_pw {B : Base F E} (hB : B.IsGood σ) (ν : Chr F E) (z : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    wt ν z (pw F w) = (val ν w : ℂ) * npow w (-(z : ℂ)) := by
  rw [wt, abs_pw hB, npow, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [inv_pow]; rfl

def tw (ν : Chr F E) (z : ℕ) (m : ℤ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m * (1 - (val ν w : ℂ) * npow w (-(z : ℂ)))⁻¹

theorem norm_t_lt (ν : Chr F E) {z : ℕ} (hz : 1 ≤ z) (w : HeightOneSpectrum (𝓞 E)) : ‖(val ν w : ℂ) * npow w (-(z : ℂ))‖ < 1 := by
  rw [norm_mul, norm_val, one_mul, norm_npow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by simp; omega)

theorem tw_ne (ν : Chr F E) {z : ℕ} (hz : 1 ≤ z) (m : ℤ) (w : HeightOneSpectrum (𝓞 E)) : tw ν z m w ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (npow_ne_zero _ _))) (inv_ne_zero fun h => by
    have := norm_t_lt ν hz w
    rw [← sub_eq_zero.1 h] at this; simp at this)

open Classical in
theorem locW {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) {w} (hν : UnrAt ν w) (m : ℤ)
    (γ : Measure (part (PI (F := F)) ⊤ (ew F w))) (hγ : γ.IsHaarMeasure ∧ γ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ (ew F w) => (if vw w x.1 ≤ WithZero.exp (-m) then (1 : ℂ) else 0) * wt ν z x.1) γ ∧
      ∫ x : part PI ⊤ (ew F w), (if vw w x.1 ≤ WithZero.exp (-m) then (1 : ℂ) else 0) * wt ν z x.1 ∂γ = tw ν z m w := by
  haveI := hγ.1
  have hs : ∀ x : part (PI (F := F)) ⊤ (ew F w), -WithZero.log (vw w x.1) = 0 ↔ x.1 ∈ UI F E := fun x => by
    refine ⟨fun h u => ?_, fun h => by rw [h w]; simp⟩
    by_cases hu : u = w
    · subst hu; rw [← WithZero.exp_log (vw_ne u x.1), neg_eq_zero.1 h]; rfl
    · rw [vw, ((mem_part_iff (ew_idem w) (inf_ew w) _).1 x.2).2 u (ew_zero.2 hu), map_one]
  have hs' : {x : part (PI (F := F)) ⊤ (ew F w) | -WithZero.log (vw w x.1) = 0} = {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} := Set.ext hs
  have := tate γ (fun x => -WithZero.log (vw w x.1)) (fun x y => by
      rw [Subgroup.coe_mul, vw_mul, WithZero.log_mul (vw_ne _ _) (vw_ne _ _)]; ring)
    (by rw [hs']; exact isOpen_UI.preimage continuous_subtype_val) (by rw [hs']; exact hγ.2) ⟨pw F w, loc_mem w _⟩
    (by show -WithZero.log (vw w (pw F w)) = 1; rw [vw_pw]; simp) ((wtH ν z).comp (Subgroup.subtype _))
    (fun x hx => by
      show wt ν z x.1 = 1
      rw [wt, nu_ew hν x.2 ((hs x).1 hx), abs_UI (ew_idem w) (inf_ew w) x.2 ((hs x).1 hx)]; simp)
    (by show ‖wt ν z (pw F w)‖ < 1; rw [wt_pw hB]; exact norm_t_lt ν hz w) m
  have e : ∀ x : part (PI (F := F)) ⊤ (ew F w), m ≤ -WithZero.log (vw w x.1) ↔ vw w x.1 ≤ WithZero.exp (-m) := fun x => by
    rw [← WithZero.log_le_iff_le_exp (vw_ne _ _)]; omega
  simp only [e] at this
  refine ⟨this.1, this.2.trans ?_⟩
  show wt ν z (pw F w) ^ m * (1 - wt ν z (pw F w))⁻¹ = _
  rw [wt_pw hB, tw]

theorem inf_sum (W : Finset (HeightOneSpectrum (𝓞 E))) {c : AE F E} (h0 : infTens F E c = 0) :
    infTens F E (∑ w ∈ W, ew F w + c) = 0 := by
  rw [map_add, h0, add_zero, map_sum, Finset.sum_eq_zero fun w _ => inf_ew w]

open Classical in
theorem prodW {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) (W : Finset (HeightOneSpectrum (𝓞 E)))
    (hν : ∀ w ∈ W, UnrAt ν w) (m : HeightOneSpectrum (𝓞 E) → ℤ) {c : AE F E} (hc : c * c = c) (h0 : infTens F E c = 0)
    (hW : ∀ w ∈ W, ew F w * c = 0) (hνc : ∀ l ∈ part PI ⊤ c, l ∈ UI F E → ν l = 1) (b : AE F E) (hb : b = ∑ w ∈ W, ew F w + c)
    (μ : Measure (part (PI (F := F)) ⊤ b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ b => (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) *
      wt ν z x.1) μ ∧
    ∫ x : part PI ⊤ b, (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) * wt ν z x.1 ∂μ =
      ∏ w ∈ W, tw ν z (m w) w := by
  have hex := fun {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) =>
    exists_haar _ (sysI.closed ha) _ (UI F E).one_mem (co_I ha h0).1 (co_I ha h0).2
  choose γ hγ using fun w => hex (ew_idem w) (inf_ew (F := F) w)
  obtain ⟨β, hβ⟩ := hex hc h0
  have mU : MeasurableSet {x : part (PI (F := F)) ⊤ c | x.1 ∈ (UI F E : Set (AE F E)ˣ)} :=
    (isOpen_UI.preimage continuous_subtype_val).measurableSet
  have eg : (fun x : part (PI (F := F)) ⊤ c => (if x.1 ∈ UI F E then (1 : ℂ) else 0)) =
      Set.indicator {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} fun _ => 1 := funext fun x => by simp [Set.indicator_apply]
  obtain ⟨p1, p2⟩ := sysI.prod (ew F) ew_idem (fun _ _ => ew_orth) c hc γ hγ β hβ W hW
    (fun T' h => co_I (sysI.good_sum _ ew_idem (fun _ _ => ew_orth) c hc T' fun w hw => hW w (h hw)) (inf_sum T' h0)) b hb μ hμ
    (fun w x => (if vw w x ≤ WithZero.exp (-m w) then (1 : ℂ) else 0) * wt ν z x) (fun x => if x ∈ UI F E then 1 else 0)
    (fun w hw => (locW hB hz (hν w hw) (m w) _ (hγ w)).1)
    (by rw [eg, integrable_indicator_iff mU]; exact integrableOn_const (by rw [hβ.2]; simp))
  rw [Finset.prod_congr rfl fun w hw => (locW hB hz (hν w hw) (m w) _ (hγ w)).2, eg, integral_indicator mU, setIntegral_const,
    Measure.real, hβ.2] at p2
  have e : (fun x : part (PI (F := F)) ⊤ b => (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) *
      wt ν z x.1) = fun x : part PI ⊤ b => (∏ w ∈ W, (if vw w (PI (ew F w) x.1) ≤ WithZero.exp (-m w) then (1 : ℂ) else 0) *
        wt ν z (PI (ew F w) x.1)) * (if PI c x.1 ∈ UI F E then 1 else 0) := funext fun x => by
    have hv : ∀ w, vw w (PI (ew F w) x.1) = vw w x.1 := fun w => by
      rw [vw, cw_PI_one (ew_idem w) (by rw [cw_ew, if_pos rfl])]; rfl
    by_cases hu : PI c x.1 ∈ UI F E
    · have hx : x.1 = (∏ w ∈ W, PI (ew F w) x.1) * PI c x.1 := by
        rw [← PI_sum _ ew_idem (fun _ _ => ew_orth) c hc W hW, ← hb]; exact x.2.2.symm
      have hw : wt ν z x.1 = ∏ w ∈ W, wt ν z (PI (ew F w) x.1) := by
        have := congrArg (wtH ν z) hx
        rw [map_mul, map_prod] at this
        refine this.trans ?_
        show _ * wt ν z _ = _
        rw [wt, hνc _ (PI_mem hc _) hu, abs_UI hc h0 (PI_mem hc _) hu]
        simp [wtH]
      simp only [hv, hu, and_true, if_true, mul_one, Finset.prod_mul_distrib, Finset.prod_boole, hw]
    · simp [hu]
  rw [e]
  exact ⟨p1, p2.trans (by simp)⟩

open Classical in

def ab (T : Finset (Pl F)) : Finset (HeightOneSpectrum (𝓞 E)) := T.biUnion (Formalism.L2.Host.aboveF (L := E) F)

theorem mem_ab {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} : w ∈ ab T ↔ w.under (𝓞 F) ∈ T := by
  simp [ab, mem_aboveF]

open Classical in
theorem rest_split {T T' : Finset (Pl F)} (h : T ⊆ T') :
    (io (rest T) : AE F E) = ∑ w ∈ ab (T' \ T), ew F w + io (rest T') := by
  refine ae_ext (by rw [inf_io (rest_fst _), inf_sum _ (inf_io (rest_fst _))]) fun u => ?_
  rw [map_add, map_sum, cw_rest, cw_rest]
  simp only [cw_ew, Finset.sum_ite_eq, mem_ab, Finset.mem_sdiff]
  by_cases h1 : u.under (𝓞 F) ∈ T
  · simp [h1, h h1]
  · by_cases h2 : u.under (𝓞 F) ∈ T' <;> simp [h1, h2]

theorem ew_rest {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) ∈ T) : ew F w * io (rest T) = 0 :=
  ae_ext (by rw [map_mul, inf_ew, zero_mul, map_zero]) fun u => by
    rw [map_mul, cw_ew, cw_rest, map_zero]
    split_ifs with h1 h2
    · simp
    · exact absurd (h1 ▸ h) h2
    all_goals simp

theorem rest_zero {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} : cw w (io (rest T) : AE F E) = 0 ↔ w.under (𝓞 F) ∈ T := by
  rw [cw_rest]; split_ifs with h <;> simp [h]

theorem nu_rest {ν : Chr F E} (hc : Continuous ν) {T : Finset (Pl F)} (hν : UnrOff ν (T : Set (Pl F))) {l}
    (h : l ∈ part PI ⊤ (io (rest T))) (hu : l ∈ UI F E) : ν l = 1 := by
  classical
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  have h0 := fun T : Finset (Pl F) => inf_io (E := E) (rest_fst T)
  have mono : ∀ {A A' : Finset (Pl F)}, A ⊆ A' → ((part PI ⊤ (io (rest A')) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E ⊆
      ((part PI ⊤ (io (rest A)) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E := by
    intro A A' hA x hx
    have h1 := (mem_part_iff (hi A') (h0 A') x).1 hx.1
    exact ⟨(mem_part_iff (hi A) (h0 A) x).2 ⟨h1.1, fun w hw => h1.2 w (rest_zero.2 (hA (rest_zero.1 hw)))⟩, hx.2⟩
  obtain ⟨T₀, hT₀⟩ := exists_subset_nhds_of_isCompact'
    (V := fun A : Finset (Pl F) => ((part PI ⊤ (io (rest A)) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E)
    (fun A A' => ⟨A ∪ A', mono Finset.subset_union_left, mono Finset.subset_union_right⟩) (fun A => cpt_I (hi A) (h0 A))
    (fun A => (cpt_I (hi A) (h0 A)).isClosed) (U := {x | ‖(ν x : ℂ) - 1‖ < 1}) fun x hx => by
      have hx' := Set.mem_iInter.1 hx
      obtain rfl : x = 1 := Units.ext (ae_ext (by rw [((mem_part_iff (hi ∅) (h0 ∅) x).1 (hx' ∅).1).1, Units.val_one, map_one])
        fun w => by
          rw [((mem_part_iff (hi _) (h0 _) x).1 (hx' {w.under (𝓞 F)}).1).2 w (rest_zero.2 (Finset.mem_singleton_self _)),
            Units.val_one, map_one])
      exact (isOpen_lt ((continuous_subtype_val.comp hc).sub continuous_const).norm continuous_const).mem_nhds
        (show ‖((ν 1 : Circle) : ℂ) - 1‖ < 1 by rw [map_one]; simp)
  have hx : l = (∏ w ∈ ab ((T ∪ T₀) \ T), PI (ew F w) l) * PI (io (rest (T ∪ T₀))) l := by
    rw [← PI_sum _ ew_idem (fun _ _ => ew_orth) _ (hi _) _ fun w hw => ew_rest (Finset.mem_sdiff.1 (mem_ab.1 hw)).1,
      ← rest_split Finset.subset_union_left]
    exact h.2.symm
  rw [hx, map_mul, map_prod, Finset.prod_eq_one fun w hw => nu_ew (hν w (Finset.mem_sdiff.1 (mem_ab.1 hw)).2) (PI_mem (ew_idem w) _)
    (sysI.pU _ (ew_idem w) _ hu), one_mul]
  refine circle_one fun n => ?_
  rw [← map_pow]
  exact hT₀ (mono Finset.subset_union_right ⟨Subgroup.pow_mem _ (PI_mem (hi _) _) n, Subgroup.pow_mem _ (sysI.pU _ (hi _) _ hu) n⟩)

end PositivityTheory.ThKG.Loc.Cone

end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub
open GlobalTheory.Doubling hiding npow norm_npow npow_ne_zero

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc id_lc id_sc id_borel

theorem inAt_iff (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (v : Pl F) (l : (AE F E)ˣ) : InAt 𝔞 v (l : AE F E) ↔
    ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → vw w l ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞) := Iff.rfl

open Classical in
theorem uLocP {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) {v : Pl F}
    (hν : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt ν w) (γ : Measure (part (PI (F := F)) ⊤ (io (idem F v))))
    (hγ : γ.IsHaarMeasure ∧ γ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ (io (idem F v)) => (if InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) γ ∧
      ∫ x : part PI ⊤ (io (idem F v)), (if InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂γ =
        ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, tw ν z (FractionalIdeal.count E w 𝔞) w := by
  have := prodW hB hz (Formalism.L2.Host.aboveF (L := E) F v) (fun w hw => hν w (mem_aboveF.1 hw)) (fun w => FractionalIdeal.count E w 𝔞)
    (c := 0) (by simp) (map_zero _) (by simp) (fun l h _ => by rw [← show PI 0 l = l from h.2, unitInvariant_zero, map_one]) _
    (idem_eq_sum v) γ hγ
  simp only [unitInvariant_zero, one_mem, and_true, mem_aboveF] at this
  simp only [inAt_iff]
  convert this

theorem ab_tendsto (T₀ : Finset (Pl F)) [DecidableEq (Pl F)] :
    Tendsto (fun T : Finset (Pl F) => ab (E := E) (T ∪ T₀)) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ h _ hw => mem_ab.2 (Finset.union_subset_union_left h (mem_ab.1 hw)))
    fun w => ⟨{w.under (𝓞 F)}, mem_ab.2 (by simp)⟩

open Classical in
theorem lim_tw {ν : Chr F E} {z : ℕ} (hz : 2 ≤ z) (m : HeightOneSpectrum (𝓞 E) → ℤ) (S T₀ : Finset (Pl F))
    (hν : UnrOff ν (S : Set (Pl F))) (hm : ∀ w, w.under (𝓞 F) ∉ T₀ → m w = 0) :
    Tendsto (fun T : Finset (Pl F) => ∏ w ∈ ab ((T ∪ T₀) \ S), tw ν z (m w) w) atTop
      (𝓝 ((∏ w ∈ ab (T₀ \ S), ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m w) * charL ν (S : Set (Pl F)) (z : ℂ))) := by
  have h1 := ((bounded_charFam (above E (S : Set (Pl F))) ν).converges (s := (z : ℂ)) (by
    simp only [Complex.natCast_re]; have : (2 : ℝ) ≤ z := by exact_mod_cast hz
    linarith)).hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ above E (S : Set (Pl F))})
    (f := fun w => locL (charFam ν) w (z : ℂ))).1 h1
  have h3 := (Tendsto.comp h2 (ab_tendsto T₀)).const_mul (∏ w ∈ ab (T₀ \ S), ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m w)
  refine h3.congr fun T => ?_
  simp only [tw, Finset.prod_mul_distrib, Function.comp]
  congr 1
  · refine Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_
    · rw [mem_ab, Finset.mem_sdiff] at hw ⊢; exact ⟨Finset.mem_union_right _ hw.1, hw.2⟩
    · rw [mem_ab, Finset.mem_sdiff] at hw hw'
      rw [hm w fun h => hw' ⟨h, hw.2⟩, zpow_zero]
  · symm
    refine Finset.prod_subset_one_on_sdiff (fun w hw => ?_) (fun w hw => ?_) fun w hw => ?_
    · rw [mem_ab] at hw ⊢; exact (Finset.mem_sdiff.1 hw).1
    · simp only [Finset.mem_sdiff, mem_ab] at hw
      exact Set.mulIndicator_of_notMem (fun h => hw.2 ⟨hw.1, h⟩) _
    · have h := (Finset.mem_sdiff.1 (mem_ab.1 hw)).2
      rw [Set.mulIndicator_of_mem (show w ∈ {w | w ∉ above E (S : Set (Pl F))} from h), locL, charFam_of_unrAt (hν w h)]
      simp [eulerFac, eulerPoly]

set_option maxHeartbeats 600000 in
open Classical in
theorem tail {B : Base F E} (hB : B.IsGood σ) {z : ℕ} (hz : 2 ≤ z) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (T T₀ : Finset (Pl F))
    (hT : T ⊆ T₀) (hm : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ T₀ → FractionalIdeal.count E w 𝔞 = 0)
    (β : Measure (part (PI (F := F)) ⊤ (io (rest T)))) (hβ : β.IsHaarMeasure ∧ β {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1)
    {ν : Chr F E} (hc : Continuous ν) (hν : UnrOff ν (T : Set (Pl F))) :
    Integrable (fun x : part PI ⊤ (io (rest T)) => (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) β ∧
      Tendsto (fun T' : Finset (Pl F) => ∏ w ∈ ab ((T' ∪ T₀) \ T), tw ν z (FractionalIdeal.count E w 𝔞) w) atTop
        (𝓝 (∫ x : part PI ⊤ (io (rest T)), (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂β)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  let D : Finset (Pl F) → Set (part (PI (F := F) (E := E)) ⊤ (io (rest T))) := fun T' => {x | PI (io (rest (T' ∪ T₀))) x.1 ∈ UI F E}
  have mD : ∀ T', MeasurableSet (D T') := fun T' =>
    (isOpen_UI.preimage ((unitInvariant_continuous (hi _)).comp continuous_subtype_val)).measurableSet
  have hD : ∀ (A : Finset (Pl F)) (x : (AE F E)ˣ), PI (io (rest A)) x ∈ UI F E ↔
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ A → vw w x = 1 := fun A x => by
    have e : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ A → vw w (PI (io (rest A)) x) = vw w x := fun w hw => by
      rw [vw, cw_PI_one (hi A) (by rw [cw_rest, if_neg hw])]; rfl
    refine ⟨fun h w hw => (e w hw).symm.trans (h w), fun h w => ?_⟩
    by_cases hw : w.under (𝓞 F) ∈ A
    · rw [vw, cw_PI_zero (hi A) (rest_zero.2 hw), map_one]
    · exact (e w hw).trans (h w hw)
  have cov : AECover β atTop D := by
    refine ⟨Eventually.of_forall fun x => ?_, mD⟩
    have f1 : ∀ y : (AE F E)ˣ, ∀ᶠ w in cofinite, vw w y ≤ 1 := fun y => (fc F E y).2
    have f2 : {w | ¬ vw w x.1 = 1}.Finite := ((f1 x.1).and (f1 x.1⁻¹)).mono fun w h => le_antisymm h.1 (by
      calc 1 = vw w x.1 * vw w x.1⁻¹ := (vw_inv w _).symm
        _ ≤ vw w x.1 * 1 := mul_le_mul_right h.2 _
        _ = vw w x.1 := mul_one _)
    filter_upwards [eventually_ge_atTop (f2.toFinset.image fun w => w.under (𝓞 F))] with T' h
    refine (hD _ _).2 fun w hw => by_contra fun h' => hw (Finset.mem_union_left _ (h ?_))
    exact Finset.mem_image_of_mem _ (f2.mem_toFinset.2 h')
  have key : ∀ ν : Chr F E, Continuous ν → UnrOff ν (T : Set (Pl F)) → ∀ T',
      IntegrableOn (fun x : part PI ⊤ (io (rest T)) => (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) (D T') β ∧
      ∫ x in D T', (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂β =
        ∏ w ∈ ab ((T' ∪ T₀) \ T), tw ν z (FractionalIdeal.count E w 𝔞) w := fun ν hc hν T' => by
    have hs : T ⊆ T' ∪ T₀ := hT.trans Finset.subset_union_right
    have := prodW hB (z := z) (by omega) (ab ((T' ∪ T₀) \ T)) (fun w hw => hν w (Finset.mem_sdiff.1 (mem_ab.1 hw)).2)
      (fun w => FractionalIdeal.count E w 𝔞) (hi (T' ∪ T₀)) (inf_io (rest_fst _))
      (fun w hw => ew_rest (Finset.mem_sdiff.1 (mem_ab.1 hw)).1)
      (fun l h hu => nu_rest hc (fun w hw => hν w fun h => hw (hs h)) h hu) _ (rest_split hs) β hβ
    rw [← integrable_indicator_iff (mD T'), ← integral_indicator (mD T')]
    have e : (D T').indicator (fun x : part PI ⊤ (io (rest T)) => (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) *
        wt ν z x.1) = fun x : part PI ⊤ (io (rest T)) => (if (∀ w ∈ ab ((T' ∪ T₀) \ T),
          vw w x.1 ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞)) ∧ PI (io (rest (T' ∪ T₀))) x.1 ∈ UI F E then (1 : ℂ) else 0) *
            wt ν z x.1 := by
      funext x
      by_cases hx : PI (io (rest (T' ∪ T₀))) x.1 ∈ UI F E
      · rw [Set.indicator_of_mem (show x ∈ D T' from hx)]
        congr 1
        refine if_congr ⟨fun h => ⟨fun w hw => (inAt_iff _ _ _).1 (h _ (Finset.mem_sdiff.1 (mem_ab.1 hw)).2) w rfl, hx⟩,
          fun h v hv => (inAt_iff _ _ _).2 fun w hw => ?_⟩ rfl rfl
        subst hw
        by_cases h1 : w.under (𝓞 F) ∈ T' ∪ T₀
        · exact h.1 w (mem_ab.2 (Finset.mem_sdiff.2 ⟨h1, hv⟩))
        · rw [(hD _ _).1 hx w h1, hm w fun h2 => h1 (Finset.mem_union_right _ h2)]; simp
      · rw [Set.indicator_of_notMem (show x ∉ D T' from hx), if_neg fun h => hx h.2, zero_mul]
    rw [e]
    convert this
  have u1 : UnrOff (1 : Chr F E) (T : Set (Pl F)) := fun w _ x _ => map_one Circle.toUnits
  obtain ⟨C, hC⟩ := (lim_tw (ν := (1 : Chr F E)) hz (fun w => FractionalIdeal.count E w 𝔞) T T₀ u1 hm).norm.isBoundedUnder_le
  have int : Integrable (fun x : part PI ⊤ (io (rest T)) =>
      (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1) β := by
    refine cov.integrable_of_integral_norm_bounded C (fun T' => (key ν hc hν T').1) (Eventually.mono hC fun T' h => le_trans ?_ h)
    beta_reduce
    rw [← (key 1 continuous_const u1 T').2]
    have e : ∀ x : part (PI (F := F) (E := E)) ⊤ (io (rest T)),
        (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt 1 z x.1 =
        ((‖(if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1‖ : ℝ) : ℂ) := fun x => by
      have hn := Circle.norm_coe (ν x.1)
      split_ifs <;> simp [wt, hn]
    simp only [e]
    rw [integral_complex_ofReal, Complex.norm_real]
    exact le_abs_self _
  refine ⟨int, (cov.integral_tendsto_of_countably_generated int).congr fun T' => (key ν hc hν T').2⟩

open Classical in
theorem euler {ν : Chr F E} {z : ℕ} (hz : 2 ≤ z) (𝔞 : FractionalIdeal (𝓞 E)⁰ E)
    (fin : {w | ¬ FractionalIdeal.count E w 𝔞 = 0}.Finite) {S₀ S T : Finset (Pl F)} (hS : S₀ ⊆ S) (hT : S ⊆ T)
    (hν : UnrOff ν (S : Set (Pl F)))
    (hram : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ S → ¬ UnrAt ν w ∧ FractionalIdeal.count E w 𝔞 = 0) (u : Pl F → ℂ)
    (hu2 : ∀ v ∉ S, u v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, tw ν z (FractionalIdeal.count E w 𝔞) w) (I : ℂ)
    (t2 : Tendsto (fun T' : Finset (Pl F) => ∏ w ∈ ab ((T' ∪ (T ∪ fin.toFinset.image fun w => w.under (𝓞 F))) \ T),
      tw ν z (FractionalIdeal.count E w 𝔞) w) atTop (𝓝 I)) :
    (∏ v ∈ T \ S, u v) * I = (∏ w ∈ fin.toFinset, npow w (-(z : ℂ)) ^ FractionalIdeal.count E w 𝔞) * (idealVal ν 𝔞 : ℂ) *
      charL ν (S₀ : Set (Pl F)) (z : ℂ) := by
  let T₀ := T ∪ fin.toFinset.image fun w => w.under (𝓞 F)
  have hm0 : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ T₀ → FractionalIdeal.count E w 𝔞 = 0 := fun w hw =>
    by_contra fun h => hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (fin.mem_toFinset.2 h)))
  have t3 := lim_tw hz (fun w => FractionalIdeal.count E w 𝔞) S T₀ hν hm0
  have t5 := tendsto_nhds_unique ((t2.const_mul (∏ v ∈ T \ S, u v)).congr fun T' => ?_) t3
  · rw [t5]
    congr 1
    · have hsub : fin.toFinset ⊆ ab (T₀ \ S) := fun w hw => mem_ab.2 (Finset.mem_sdiff.2
        ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw), fun h => fin.mem_toFinset.1 hw (hram w h).2⟩)
      rw [← Finset.prod_subset hsub fun w _ hw => by rw [not_not.1 (mt fin.mem_toFinset.2 hw), zpow_zero], idealVal,
        finprod_eq_prod_of_mulSupport_subset _ (s := fin.toFinset) fun w hw => by
          simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
          intro h; exact hw (by simp only [h, zpow_zero])]
      simp only [mul_zpow, Finset.prod_mul_distrib, Units.coe_prod, Units.val_zpow_eq_zpow_val]
      ring
    · simp only [charL, LS, eulerProd]
      refine (tprod_subtype {w | w ∉ above E (S : Set (Pl F))} fun w => locL (charFam ν) w (z : ℂ)).trans
        (Eq.trans (tprod_congr fun w => ?_) (tprod_subtype {w | w ∉ above E (S₀ : Set (Pl F))} fun w => locL (charFam ν) w (z : ℂ)).symm)
      by_cases h : w.under (𝓞 F) ∈ S
      · have : locL (charFam ν) w (z : ℂ) = 1 := by rw [locL, charFam, if_neg (hram w h).1, eulerFac_zero]
        simp only [Set.mulIndicator_apply, this, ite_self]
      · rw [Set.mulIndicator_of_mem (show w ∈ {w | w ∉ above E (S : Set (Pl F))} from h),
          Set.mulIndicator_of_mem (show w ∈ {w | w ∉ above E (S₀ : Set (Pl F))} from fun h' => h (hS h'))]
  · rw [Finset.prod_congr rfl fun v hv => hu2 v (Finset.mem_sdiff.1 hv).2, ← Finset.prod_biUnion (fun a _ b _ hab =>
      Finset.disjoint_left.2 fun w h h' => hab ((mem_aboveF.1 h).symm.trans (mem_aboveF.1 h'))), ← Finset.prod_union
      (Finset.disjoint_left.2 fun w h h' => (Finset.mem_sdiff.1 (mem_ab.1 h')).2 (by
        simp only [Finset.mem_biUnion, mem_aboveF, exists_eq_right', Finset.mem_sdiff] at h; exact h.1))]
    refine Finset.prod_congr (Finset.ext fun w => ?_) fun _ _ => rfl
    simp only [Finset.mem_union, Finset.mem_biUnion, mem_aboveF, exists_eq_right', Finset.mem_sdiff, mem_ab, T₀]
    have := @hT (w.under (𝓞 F))
    tauto

set_option maxHeartbeats 1000000 in
theorem ideleFub : IdeleFub := by
  classical
  intro F E _ _ _ _ _ σ B n X K m μ hB hm hμ 𝔞 z h𝔞 hz
  have sy := sysI (F := F) (E := E)
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  have hr := io_idem (E := E) (real_idem (F := F))
  have hv := fun v : Pl F => io_idem (E := E) (idem_idem v)
  have di := idAt_eq (E := E) (evI F) real_idem fun _ => at_inf_iff
  have df := fun v => idAt_eq (E := E) (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have e1 : (⊤ : Subgroup (AE F E)ˣ) = part PI ⊤ (io (realAd F 1) + io (rest ∅)) := by
    rw [io, io, ← map_add, real_add_rest, map_one]
    exact Subgroup.ext fun g => ⟨fun h => ⟨h, unitInvariant_one g⟩, fun h => h.1⟩
  have sp := sy.split hr (hi ∅) (io_orth (real_rest ∅))
  let et : (⊤ : Subgroup (AE F E)ˣ) ≃ₜ* (AE F E)ˣ :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  have hme : MeasurableEmbedding et.symm := et.symm.toHomeomorph.measurableEmbedding
  obtain ⟨μ', m1, -, m3⟩ := transport e1 _ BorelSpace.measurable_eq (μ.map et.symm)
  obtain ⟨α, a1, -, a3⟩ := transport di _ rfl m.xi
  choose γ g1 g2 g3 using fun v => transport (df v) _ rfl (m.xf v)
  have hγ : ∀ v, (γ v).IsHaarMeasure ∧ γ v {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1 := fun v =>
    ⟨g1 v (hm.xf v).1, by rw [g2, ← units_eq]; exact (hm.xf v).2⟩
  choose β hβ using fun T : Finset (Pl F) => exists_haar _ (sy.closed (hi T)) _ (UI F E).one_mem
    (co_I (hi T) (inf_io (rest_fst T))).1 (co_I (hi T) (inf_io (rest_fst T))).2
  haveI := m1 (ContinuousMulEquiv.isHaarMeasure_map μ et.symm); haveI := a1 hm.xi; haveI := (hβ ∅).1
  obtain ⟨c, c0, c1, -⟩ := sp.fub μ' α (β ∅)
  have fin : {w | ¬ FractionalIdeal.count E w 𝔞 = 0}.Finite := FractionalIdeal.finite_factors 𝔞
  let κa : ℂ := ∏ w ∈ fin.toFinset, npow w (-(z : ℂ)) ^ FractionalIdeal.count E w 𝔞
  refine ⟨fun l => ⟨PI (io (realAd F 1)) l, di ▸ PI_mem hr l⟩, fun v l => ⟨PI (io (idem F v)) l, (df v) ▸ PI_mem (hv v) l⟩, c * κa,
    mul_ne_zero (by exact_mod_cast c0) (Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (npow_ne_zero _ _)),
    fun l => ⟨coe_PI_io real_idem l, fun v => coe_PI_io (idem_idem v) l⟩, fun ν S₀ S hc hS hν hram => ?_⟩
  have hu := fun v (h : v ∉ S) => uLocP hB (ν := ν) (z := z) (by omega) 𝔞 (v := v) (fun w hw => hν w (by
    show ¬ (w.under (𝓞 F) ∈ (S : Set (Pl F))); rw [hw]; exact h)) (γ v) (hγ v)
  have hu2 : ∀ v ∉ S, uLoc v (m.xf v) 𝔞 ν z = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, tw ν z (FractionalIdeal.count E w 𝔞) w :=
    fun v h => (g3 v fun l => (if InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l).2.symm.trans (hu v h).2
  refine ⟨fun v h => ⟨by rw [hu2 v h]; exact Finset.prod_ne_zero_iff.2 fun w _ => tw_ne ν (by omega) _ _,
    (g3 v fun l => (if InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l).1.1 (hu v h).1⟩, fun T hT gi g i1 i2 => ?_⟩
  let T₀ := T ∪ fin.toFinset.image fun w => w.under (𝓞 F)
  have hm0 : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ T₀ → FractionalIdeal.count E w 𝔞 = 0 := fun w hw =>
    by_contra fun h => hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (fin.mem_toFinset.2 h)))
  obtain ⟨t1, t2⟩ := tail hB hz 𝔞 T T₀ Finset.subset_union_left hm0 (β T) (hβ T) hc fun w hw => hν w fun h => hw (hT h)
  have t4 : (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) * ∫ x : part PI ⊤ (io (rest T)),
      (if ∀ v ∉ T, InAt 𝔞 v (x.1 : AE F E) then (1 : ℂ) else 0) * wt ν z x.1 ∂(β T) =
      κa * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ) :=
    euler hz 𝔞 fin hS hT hν hram _ hu2 _ t2
  have hsum : (io (rest ∅) : AE F E) = ∑ v ∈ T, io (idem F v) + io (rest T) := by
    rw [sum_rest T, io, map_add, map_sum]; rfl
  obtain ⟨p1, p2⟩ := sy.prod (fun v => io (idem F v)) hv (fun _ _ h => io_orth (idem_orth h)) _ (hi T) γ hγ (β T) (hβ T) T
    (fun v h => io_orth (idem_rest h))
    (fun T' h => co_I (sy.good_sum _ hv (fun _ _ h => io_orth (idem_orth h)) _ (hi T) T' fun v h' => io_orth (idem_rest (h h')))
      (by rw [map_add, inf_io (rest_fst T), add_zero, map_sum, Finset.sum_eq_zero fun v _ => inf_io rfl]))
    _ hsum (β ∅) (hβ ∅) (fun v l => ext0 _ (g v) l * wt ν z l)
    (fun l => (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then (1 : ℂ) else 0) * wt ν z l)
    (fun v h => (g3 v fun l => ext0 _ (g v) l * wt ν z l).1.2 (by simp only [extendByZeroOnSubset_apply_coe]; exact i2 v h)) t1
  obtain ⟨q1, q2⟩ := c1 (fun l => ext0 _ gi l * wt ν z l) (fun y => (∏ v ∈ T, ext0 _ (g v) (PI (io (idem F v)) y) *
      wt ν z (PI (io (idem F v)) y)) * ((if ∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) y : AE F E) then (1 : ℂ) else 0) *
        wt ν z (PI (io (rest T)) y)))
    ((a3 fun l => ext0 _ gi l * wt ν z l).1.2 (by simp only [extendByZeroOnSubset_apply_coe]; exact i1)) p1
  rw [p2, (a3 fun l => ext0 _ gi l * wt ν z l).2] at q2
  simp only [fun v => (g3 v fun l => ext0 _ (g v) l * wt ν z l).2, extendByZeroOnSubset_apply_coe] at q2
  have r1 : ∀ v, (io (idem F v) * io (rest ∅) : AE F E) = io (idem F v) := fun v => by
    rw [io_mul, rest, Finset.sum_empty, sub_zero, mul_sub, idem_real, mul_one, sub_zero]
  have r2 : (io (rest T) * io (rest ∅) : AE F E) = io (rest T) := by
    rw [io_mul, rest.eq_1 ∅, Finset.sum_empty, sub_zero, mul_sub, mul_one, mul_comm, real_rest, sub_zero]
  have m4 := m3 fun x => (ext0 _ gi (PI (io (realAd F 1)) x) * wt ν z (PI (io (realAd F 1)) x)) *
    ((∏ v ∈ T, ext0 _ (g v) (PI (io (idem F v)) (PI (io (rest ∅)) x)) * wt ν z (PI (io (idem F v)) (PI (io (rest ∅)) x))) *
      ((if ∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) (PI (io (rest ∅)) x) : AE F E) then (1 : ℂ) else 0) *
        wt ν z (PI (io (rest T)) (PI (io (rest ∅)) x))))
  rw [m4.1, hme.integrable_map_iff] at q1
  rw [m4.2, hme.integral_map] at q2
  have ef : ∀ x : (AE F E)ˣ, (ext0 _ gi (PI (io (realAd F 1)) x) * wt ν z (PI (io (realAd F 1)) x)) *
      ((∏ v ∈ T, ext0 _ (g v) (PI (io (idem F v)) (PI (io (rest ∅)) x)) * wt ν z (PI (io (idem F v)) (PI (io (rest ∅)) x))) *
        ((if ∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) (PI (io (rest ∅)) x) : AE F E) then (1 : ℂ) else 0) *
          wt ν z (PI (io (rest T)) (PI (io (rest ∅)) x)))) =
      gi ⟨PI (io (realAd F 1)) x, di ▸ PI_mem hr x⟩ * (∏ v ∈ T, g v ⟨PI (io (idem F v)) x, (df v) ▸ PI_mem (hv v) x⟩) *
        (if ∀ v ∉ T, InAt 𝔞 v (x : AE F E) then 1 else 0) * wt ν z x := fun x => by
    have hx : wt ν z x = wt ν z (PI (io (realAd F 1)) x) * ((∏ v ∈ T, wt ν z (PI (io (idem F v)) x)) * wt ν z (PI (io (rest T)) x)) := by
      have h1 := sp.mul x (e1 ▸ Subgroup.mem_top x)
      rw [hsum, PI_sum _ hv (fun _ _ h => io_orth (idem_orth h)) _ (hi T) T fun v h => io_orth (idem_rest h)] at h1
      have := congrArg (wtH ν z) h1
      rw [map_mul, map_mul, map_prod] at this
      exact this.symm
    have hin : (∀ v ∉ T, InAt 𝔞 v (PI (io (rest T)) x : AE F E)) ↔ ∀ v ∉ T, InAt 𝔞 v (x : AE F E) :=
      forall₂_congr fun v h => by
        simp only [inAt_iff]
        refine forall₂_congr fun w hw => ?_
        rw [vw, cw_PI_one (hi T) (by rw [cw_rest, hw, if_neg h])]; rfl
    simp only [fun v => unitInvariant_comp (hv v) (hi ∅) x, unitInvariant_comp (hi T) (hi ∅) x, r1, r2, hin, ← extendByZeroOnSubset_apply_coe gi,
      ← fun v => extendByZeroOnSubset_apply_coe (g v), Finset.prod_mul_distrib]
    rw [hx]; ring
  have q3 := q1.congr (Eventually.of_forall ef)
  refine ⟨q3, ?_⟩
  rw [← integral_congr_ae (Eventually.of_forall ef)]
  refine (congrArg _ q2).trans ?_
  linear_combination (c * (@integral _ _ _ _ (borel _) m.xi fun l => gi l * wt ν z l.1) *
    ∏ v ∈ T, @integral _ _ _ _ (borel _) (m.xf v) fun l => g v l * wt ν z l.1) * t4

end PositivityTheory.ThKG.Loc.Cone

end
end
