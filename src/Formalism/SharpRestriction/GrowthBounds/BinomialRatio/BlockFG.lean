import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
import Mathlib

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def SmithData {r s t : ℕ} (form : SegVs O r s t → SegVs O r s t → KK O) (L : Submodule O (SegVs O r s t)) (n : ℕ)
    (al be : Fin n → SegVs O r s t) (β : Fin n → SegBlock s r) : Prop :=
  (∀ i, al i ∈ L ∧ be i ∈ L) ∧ (∀ i b, b ≠ β i → al i b = 0 ∧ be i b = 0) ∧
    (∀ i l, i ≠ l → form (al i) (be l) = 0) ∧ LinearIndependent O al ∧
    Submodule.span O (Set.range al) = L ∧ Submodule.span O (Set.range be) = L

theorem vK_zero (p : ℕ) : vK p (0 : KK O) = ⊤ := by
  unfold vK ordW
  simp

theorem vLE_ne_zero {p : ℕ} {κ : KK O} {D : ℝ} (h : vLE p κ D) : κ ≠ 0 := by
  intro hκ
  subst hκ
  obtain ⟨q, hq, -⟩ := h
  rw [vK_zero] at hq
  exact WithTop.top_ne_coe hq

theorem scale_to_O {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {κ : KK O} {D : ℝ} (hD : 0 ≤ D)
    (h : vLE p κ D) : ∃ c z : O, z ≠ 0 ∧ vLEO p z D ∧ algebraMap O (KK O) c * κ = algebraMap O (KK O) z := by
  have hκ := vLE_ne_zero h
  rcases ValuationRing.isInteger_or_isInteger O κ with ⟨z, hz⟩ | ⟨c, hc⟩
  · refine ⟨1, z, ?_, ?_, by rw [map_one, one_mul, hz]⟩
    · rintro rfl
      exact hκ (by rw [← hz, map_zero])
    · unfold vLEO vO
      rw [hz]
      exact h
  · refine ⟨c, 1, one_ne_zero, ?_, by rw [hc, map_one, inv_mul_cancel₀ hκ]⟩
    rw [vLEO_iff hw h2 one_ne_zero, dvr_order_unit_eq_zero isUnit_one]
    simpa using hD

theorem segForm_smul_right (p r : ℕ) {s : ℕ} (S : SegData s) (c : O) (f g : SegVs O r s S.t) :
    segForm O p r S f (c • g) = algebraMap O (KK O) c * segForm O p r S f g := by
  unfold segForm
  by_cases hc : algebraMap O (KK O) c = 0
  · rw [hc, zero_mul]
    have : ∀ b, ((specConst p S b : ℕ) : KK O) * fock (f b) ((c • g) b) = 0 := fun b => by
      rw [Pi.smul_apply, ← algebraMap_smul (KK O) c (g b), hc, zero_smul]
      unfold fock
      simp
    rw [finsum_congr this, finsum_zero]
  · have := AddMonoidHom.map_finsum_of_injective (AddMonoidHom.mulLeft (algebraMap O (KK O) c))
      (mul_right_injective₀ hc) (fun b => ((specConst p S b : ℕ) : KK O) * fock (f b) (g b))
    simp only [AddMonoidHom.coe_mulLeft] at this
    rw [this]
    refine finsum_congr fun b => ?_
    rw [Pi.smul_apply, ← algebraMap_smul (KK O) c (g b), fock_form_smul_right, smul_eq_mul]
    ring

open Classical in

theorem blockDiag_of_smith {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {r s : ℕ} (S : SegData s)
    (L : Submodule O (SegVs O r s S.t)) {n : ℕ} {al be : Fin n → SegVs O r s S.t} {β : Fin n → SegBlock s r}
    (hS : SmithData (segForm O p r S) L n al be β) {D : ℝ} (hD : 0 ≤ D) (g : ℕ)
    (hg : g ≤ (Finset.univ.filter fun i => vLE p (segForm O p r S (al i) (be i)) D).card) :
    BlockDiag p (segForm O p r S) L g D := by
  obtain ⟨hmem, hsupp, horth, -, -, -⟩ := hS
  set good := Finset.univ.filter fun i => vLE p (segForm O p r S (al i) (be i)) D with hgood
  let e : Fin g → Fin n := fun i => ((good.equivFin).symm (Fin.castLE hg i)).1
  have he : Function.Injective e := fun a b hab => by
    have h1 := Subtype.ext hab
    have h3 := (good.equivFin).symm.injective h1
    exact Fin.castLE_injective hg h3
  have hegood : ∀ i, vLE p (segForm O p r S (al (e i)) (be (e i))) D := fun i =>
    (Finset.mem_filter.1 ((good.equivFin).symm (Fin.castLE hg i)).2).2
  choose c z hz0 hzD hcz using fun i => scale_to_O hw h2 hD (hegood i)
  refine ⟨fun i => al (e i), fun i => c i • be (e i), fun i => β (e i), z,
    fun i => ⟨(hmem _).1, L.smul_mem _ (hmem _).2⟩, fun i b hb => ⟨(hsupp _ b hb).1, ?_⟩, fun i => ⟨hz0 i, hzD i⟩, ?_⟩
  · show c i • be (e i) b = 0
    rw [(hsupp _ b hb).2, smul_zero]
  · intro i l
    show segForm O p r S (al (e i)) (c l • be (e l)) = _
    rw [segForm_smul_right]
    by_cases hil : i = l
    · subst hil
      rw [if_pos rfl, hcz]
    · rw [if_neg hil, horth _ _ (fun h => hil (he h)), mul_zero]

end Gen

def SmithAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ j : Fin (numSeg X.TT), ∃ (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
      (β : Fin n → SegBlock (segS X.TT j) X.m),
      SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β

open Classical in

def CountSmithAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (Dj : ℝ) (L₁ : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)), 0 ≤ Dj →
      GoodSub X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) L₁ Dj →
      ∀ (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
        (β : Fin n → SegBlock (segS X.TT j) X.m),
        SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β →
        Module.finrank O L₁ ≤
          (Finset.univ.filter fun i => vLE X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j) (al i) (be i)) Dj).card

theorem partners_factors_at_of_smith {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ} (hSm : SmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc)
    (hCn : CountSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : PartnersToFactorsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j Dj L₁ hD hG
  obtain ⟨n, al, be, β, hd⟩ := hSm X W Qq O Kf ι σ jO w hS hH hc j
  exact blockDiag_of_smith hS.2.1 hS.1.w_sq _ _ hd hD _
    (hCn X W Qq O Kf ι σ jO w hS hH hc j Dj L₁ hD hG n al be β hd)

def RestSmith : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => SmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc
def RestCountSmith : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => CountSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

theorem partners_factors_of_smith_count (hSm : RestSmith) (hCn : RestCountSmith) : PartnersToFactors :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => partners_factors_at_of_smith h.1 h.2) (TransportedAlt.and hSm hCn)

section Rank

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem rank_le_of_ker {V : Type} [AddCommGroup V] [Module O V] {n : ℕ} (al : Fin n → V) (hli : LinearIndependent O al)
    (L L₁ : Submodule O V) (hspan : Submodule.span O (Set.range al) = L) (hle : L₁ ≤ L) (good : Finset (Fin n))
    (hker : ∀ a : Fin n → O, (∑ i, a i • al i) ∈ L₁ → (∀ i ∈ good, a i = 0) → a = 0) :
    Module.finrank O L₁ ≤ good.card := by
  classical
  have hle' : L₁ ≤ Submodule.span O (Set.range al) := hle.trans hspan.ge
  let π : L₁ →ₗ[O] (good → O) := LinearMap.pi fun i =>
    (Finsupp.lapply (i : Fin n)).comp (hli.repr.comp (Submodule.inclusion hle'))
  have hπ : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hrep := hli.linearCombination_repr (Submodule.inclusion hle' x)
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul O (al i))] at hrep
    have hz : (fun i => hli.repr (Submodule.inclusion hle' x) i) = 0 := by
      refine hker _ ?_ (fun i hi => congr_fun hx ⟨i, hi⟩)
      show (∑ i, hli.repr (Submodule.inclusion hle' x) i • al i) ∈ L₁
      rw [hrep, Submodule.coe_inclusion]
      exact x.2
    have hz' : ∀ i, hli.repr (Submodule.inclusion hle' x) i = 0 := fun i => congr_fun hz i
    apply Subtype.ext
    rw [Submodule.coe_zero, ← Submodule.coe_inclusion hle' x, ← hrep]
    simp [hz']
  calc Module.finrank O L₁ ≤ Module.finrank O (good → O) := LinearMap.finrank_le_finrank_of_injective hπ
    _ = good.card := by simp

end Rank

open Classical in

def KerSmithAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (Dj : ℝ) (L₁ : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)), 0 ≤ Dj →
      GoodSub X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) L₁ Dj →
      ∀ (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
        (β : Fin n → SegBlock (segS X.TT j) X.m),
        SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β →
        ∀ a : Fin n → O, (∑ i, a i • al i) ∈ L₁ →
          (∀ i, vLE X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j) (al i) (be i)) Dj → a i = 0) → a = 0

open Classical in
theorem countSmithAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (h : KerSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : CountSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j Dj L₁ hD hG n al be β hSm
  exact rank_le_of_ker al hSm.2.2.2.1 _ L₁ hSm.2.2.2.2.1 hG.1.1 _
    (fun a ha h0 => h X W Qq O Kf ι σ jO w hS hH hC j Dj L₁ hD hG n al be β hSm a ha
      (fun i hi => h0 i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)))

def RestKerSmith : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => KerSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

theorem partners_factors_of_kernel_smith (hSm : RestSmith) (hK : RestKerSmith) : PartnersToFactors :=
  partners_factors_of_smith_count hSm (TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => countSmithAt_of h) hK)

section Ker

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem bad_zero (p : ℕ) (D : ℝ) : ¬ vLE p (0 : KK O) D := fun h => vLE_ne_zero h rfl

theorem bad_add {p : ℕ} {D : ℝ} {x y : KK O} (hx : ¬ vLE p x D) (hy : ¬ vLE p y D) : ¬ vLE p (x + y) D := by
  rintro ⟨q, hq, hqD⟩
  have h := valuation_add_ge_min p x y
  rw [hq] at h
  rcases min_le_iff.1 h with h1 | h1
  · obtain ⟨q', hq', hle⟩ := WithTop.le_coe_iff.1 h1
    exact hx ⟨q', hq', le_trans (by exact_mod_cast hle) hqD⟩
  · obtain ⟨q', hq', hle⟩ := WithTop.le_coe_iff.1 h1
    exact hy ⟨q', hq', le_trans (by exact_mod_cast hle) hqD⟩

theorem bad_mul {p : ℕ} {D : ℝ} (o : O) {x : KK O} (hx : ¬ vLE p x D) : ¬ vLE p (algebraMap O (KK O) o * x) D := by
  rintro ⟨q, hq, hqD⟩
  rw [valuation_mul_alt] at hq
  have h0 := vK_alg_nonneg p o
  have h1 : vK p x ≤ (q : WithTop ℚ) := by
    rw [← hq]
    exact le_add_of_nonneg_left h0
  obtain ⟨q', hq', hle⟩ := WithTop.le_coe_iff.1 h1
  exact hx ⟨q', hq', le_trans (by exact_mod_cast hle) hqD⟩

theorem bad_sum {p : ℕ} {D : ℝ} {ι : Type} (s : Finset ι) (f : ι → KK O) (h : ∀ i ∈ s, ¬ vLE p (f i) D) :
    ¬ vLE p (∑ i ∈ s, f i) D := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using bad_zero (O := O) p D
  · intro i s hi ih h
    rw [Finset.sum_insert hi]
    exact bad_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

open Classical in

theorem prim_div {w : O} (hw : Irreducible w) {n : ℕ} (a : Fin n → O) (ha : a ≠ 0) :
    ∃ (k : ℕ) (a' : Fin n → O), (∀ i, a i = w ^ k * a' i) ∧ ∃ i0, IsUnit (a' i0) := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact ha (funext hne)
  let S := Finset.univ.filter fun i => a i ≠ 0
  have hS : S.Nonempty := ⟨j, by simp [S, hj]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => dvrOrderNat (a i)) hS
  have hi0 : a i0 ≠ 0 := (Finset.mem_filter.mp hi0S).2
  have hex : ∀ i, ∃ b : O, a i = w ^ dvrOrderNat (a i0) * b ∧ (i = i0 → IsUnit b) := by
    intro i
    by_cases hi : a i = 0
    · refine ⟨0, by rw [hi, mul_zero], fun h => ?_⟩
      subst h
      exact absurd hi hi0
    · obtain ⟨u, hu⟩ := eq_unit_pow hw hi
      have hle : dvrOrderNat (a i0) ≤ dvrOrderNat (a i) := hmin i (by simp [S, hi])
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨(u : O) * w ^ d, ?_, fun h => ?_⟩
      · conv_lhs => rw [hu, hd]
        rw [pow_add]
        ring
      · subst h
        have hd0 : d = 0 := by omega
        rw [hd0, pow_zero, mul_one]
        exact u.isUnit
  choose a' ha' using hex
  exact ⟨dvrOrderNat (a i0), a', fun i => (ha' i).1, i0, (ha' i0).2 rfl⟩

theorem ker_core {p : ℕ} {w : O} (hw : Irreducible w) {V : Type} [AddCommGroup V] [Module O V]
    (form : V → V → KK O) (L L₁ : Submodule O V) {n : ℕ} (al be : Fin n → V) (hli : LinearIndependent O al)
    (hA : Submodule.span O (Set.range al) = L) (hB : Submodule.span O (Set.range be) = L)
    (hbil : ∀ a η : Fin n → O, form (∑ i, a i • al i) (∑ i, η i • be i) =
      ∑ i, algebraMap O (KK O) (a i * η i) * form (al i) (be i))
    {D : ℝ} (hG : GoodSub p form L L₁ D) (a : Fin n → O) (ha : (∑ i, a i • al i) ∈ L₁)
    (h0 : ∀ i, vLE p (form (al i) (be i)) D → a i = 0) : a = 0 := by
  by_contra hne
  obtain ⟨k, a', ha', i0, hu⟩ := prim_div hw a hne
  have hwk : w ^ k ≠ 0 := pow_ne_zero _ hw.ne_zero
  have hL : (∑ i, a' i • al i) ∈ L := by
    rw [← hA]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsm : w ^ k • (∑ i, a' i • al i) = ∑ i, a i • al i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← ha']
  have h1 : (∑ i, a' i • al i) ∈ L₁ := hG.1.2 _ _ hwk hL (by rw [hsm]; exact ha)
  have hprim : PrimIn L₁ (∑ i, a' i • al i) := by
    refine ⟨h1, fun c x hx hcx => ?_⟩
    have hxL : x ∈ Submodule.span O (Set.range al) := by rw [hA]; exact hG.1.1 hx
    obtain ⟨ξ, hξ⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hxL
    have hz : ∑ i, (a' i - c * ξ i) • al i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [← Finset.smul_sum, hξ, ← hcx, sub_self]
    have := Fintype.linearIndependent_iff.1 hli _ hz i0
    have h2 : a' i0 = c * ξ i0 := sub_eq_zero.1 this
    rw [h2] at hu
    exact isUnit_of_mul_isUnit_left hu
  obtain ⟨y, hyL, hy⟩ := hG.2 _ hprim
  have hyS : y ∈ Submodule.span O (Set.range be) := by rw [hB]; exact hyL
  obtain ⟨η, hη⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hyS
  rw [← hη, hbil] at hy
  refine bad_sum _ _ (fun i _ => ?_) hy
  by_cases hi : vLE p (form (al i) (be i)) D
  · have : a' i = 0 := by
      have h3 := h0 i hi
      rw [ha'] at h3
      exact (mul_eq_zero.1 h3).resolve_left hwk
    rw [this, zero_mul, map_zero, zero_mul]
    exact bad_zero p D
  · exact bad_mul _ hi

end Ker

def BilinAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
        (β : Fin n → SegBlock (segS X.TT j) X.m),
        SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β →
        ∀ a η : Fin n → O, segForm O X.p X.m (X.seg C0 CE1 CE2 j) (∑ i, a i • al i) (∑ i, η i • be i) =
          ∑ i, algebraMap O (KK O) (a i * η i) * segForm O X.p X.m (X.seg C0 CE1 CE2 j) (al i) (be i)

theorem kerSmithAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (h : BilinAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : KerSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j Dj L₁ hD hG n al be β hSm a ha h0
  exact ker_core hS.2.1 _ _ L₁ al be hSm.2.2.2.1 hSm.2.2.2.2.1 hSm.2.2.2.2.2
    (h X W Qq O Kf ι σ jO w hS hH hC j n al be β hSm) hG a ha h0

section Bilin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fock_zero_left {σ : Type} (G : MvPolynomial σ (KK O)) : fock (0 : MvPolynomial σ (KK O)) G = 0 := by
  unfold fock
  simp

theorem segForm_eq_sum (p r : ℕ) {s : ℕ} (S : SegData s) (T : Finset (SegBlock s r)) (f g : SegVs O r s S.t)
    (hT : ∀ b, b ∉ T → f b = 0) :
    segForm O p r S f g = ∑ b ∈ T, ((specConst p S b : ℕ) : KK O) * fock (f b) (g b) := by
  unfold segForm
  apply finsum_eq_sum_of_support_subset
  intro b hb
  by_contra hn
  apply hb
  show ((specConst p S b : ℕ) : KK O) * fock (f b) (g b) = 0
  rw [hT b (by simpa using hn), fock_zero_left, mul_zero]

theorem fock_bilin {σ : Type} {n : ℕ} (F G : Fin n → MvPolynomial σ (KK O)) (a η : Fin n → O) :
    fock (∑ i, a i • F i) (∑ l, η l • G l) = ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) * fock (F i) (G l) := by
  rw [← fockBilinear_apply, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul (KK O) (a i) (F i), ← algebraMap_smul (KK O) (η l) (G l), map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, fockBilinear_apply, map_mul]
  ring

theorem segForm_bilin (p r : ℕ) {s : ℕ} (S : SegData s) (T : Finset (SegBlock s r)) {n : ℕ}
    (al be : Fin n → SegVs O r s S.t) (hT : ∀ i b, b ∉ T → al i b = 0) (a η : Fin n → O) :
    segForm O p r S (∑ i, a i • al i) (∑ i, η i • be i) =
      ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) * segForm O p r S (al i) (be l) := by
  have h0 : ∀ b, b ∉ T → (∑ i, a i • al i) b = 0 := fun b hb => by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [Pi.smul_apply, hT i b hb, smul_zero]
  rw [segForm_eq_sum p r S T _ _ h0]
  have e1 : ∀ i l, segForm O p r S (al i) (be l) =
      ∑ b ∈ T, ((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b) := fun i l =>
    segForm_eq_sum p r S T _ _ (hT i)
  simp only [e1]
  have key : ∀ b, fock ((∑ i, a i • al i) b) ((∑ i, η i • be i) b) =
      ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) * fock (al i b) (be l b) := fun b => by
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply]
    exact fock_bilin (fun i => al i b) (fun l => be l b) a η
  calc ∑ b ∈ T, ((specConst p S b : ℕ) : KK O) * fock ((∑ i, a i • al i) b) ((∑ i, η i • be i) b)
      = ∑ b ∈ T, ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) *
          (((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [key b, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ i, ∑ b ∈ T, ∑ l, algebraMap O (KK O) (a i * η l) *
          (((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b)) := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ b ∈ T, algebraMap O (KK O) (a i * η l) *
          (((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Bilin

theorem bilinAt_all (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : BilinAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j n al be β hSm a η
  classical
  have hT : ∀ i b, b ∉ Finset.univ.image β → al i b = 0 := by
    intro i b hb
    refine (hSm.2.1 i b fun hbi => hb ?_).1
    rw [hbi]
    exact Finset.mem_image_of_mem β (Finset.mem_univ i)
  rw [segForm_bilin X.p X.m (X.seg C0 CE1 CE2 j) (Finset.univ.image β) al be hT a η]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · intro l _ hl
    rw [hSm.2.2.1 i l (Ne.symm hl), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem partners_factors_of_smith_bases (hSm : RestSmith) : PartnersToFactors :=
  partners_factors_of_kernel_smith hSm (TransportedAlt.of_all fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc =>
    kerSmithAt_of (bilinAt_all C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc))

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
namespace Formalism.InvariantFactorPaths.KP

open Module

private theorem smithMatrix_lemma {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (n : ℕ)
    (φ : (Fin n → O) →ₗ[O] (Fin n → O)) :
    ∃ b c : Module.Basis (Fin n) O (Fin n → O), ∀ i j, i ≠ j → c.repr (φ (b j)) i = 0 := by
  classical
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin n)) (LinearMap.range φ)
  have hx : ∀ i, ∃ x, φ x = (snf.bN i : Fin n → O) := fun i => LinearMap.mem_range.1 (snf.bN i).2
  choose x hx using hx
  let s : LinearMap.range φ →ₗ[O] (Fin n → O) := snf.bN.constr O x
  have hs : ∀ y : LinearMap.range φ, φ (s y) = y := by
    have : φ ∘ₗ s = (LinearMap.range φ).subtype :=
      snf.bN.ext fun i => by simp [s, Module.Basis.constr_basis, hx]
    intro y
    exact LinearMap.congr_fun this y
  have hsi : Function.Injective s := fun y y' h => Subtype.ext (by rw [← hs y, ← hs y', h])
  let f : (Fin n → O) →ₗ[O] LinearMap.range s := s.rangeRestrict ∘ₗ φ.rangeRestrict
  have hf : ∀ v : LinearMap.range s, f v = v := by
    rintro ⟨v, y, rfl⟩
    apply Subtype.ext
    have : φ.rangeRestrict (s y) = y := Subtype.ext (hs y)
    simp only [f, LinearMap.comp_apply, this]
    rfl
  have hc : IsCompl (LinearMap.range s) (LinearMap.ker f) := LinearMap.isCompl_of_proj hf
  have hK : ∀ v ∈ LinearMap.ker f, φ v = 0 := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have h1 : s (φ.rangeRestrict v) = 0 := by
      have := congrArg Subtype.val hv
      simpa [f] using this
    have h2 : φ.rangeRestrict v = 0 := hsi (by rw [h1, map_zero])
    simpa using congrArg Subtype.val h2
  obtain ⟨k, bK⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) (LinearMap.ker f)
  let bS : Module.Basis (Fin m) O (LinearMap.range s) := snf.bN.map (LinearEquiv.ofInjective s hsi)
  let B : Module.Basis (Fin m ⊕ Fin k) O (Fin n → O) :=
    (bS.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hB1 : ∀ i, B (Sum.inl i) = x i := by
    intro i
    simp [B, bS, Module.Basis.constr_basis, s]
  have hB2 : ∀ l, B (Sum.inr l) ∈ LinearMap.ker f := by
    intro l
    simp [B]
  have hcard : n = m + k := by
    have := Fintype.card_congr ((Pi.basisFun O (Fin n)).indexEquiv B)
    simpa using this
  let e1 : Fin m ≃ Set.range snf.f := Equiv.ofInjective snf.f snf.f.injective
  have hc2 : Fintype.card (Fin k) = Fintype.card {j // j ∉ Set.range snf.f} := by
    have h1 := Fintype.card_congr e1
    rw [Fintype.card_subtype_compl, ← h1]
    simp only [Fintype.card_fin]
    omega
  let e2 : Fin k ≃ {j // j ∉ Set.range snf.f} := Fintype.equivOfCardEq hc2
  let E : Fin m ⊕ Fin k ≃ Fin n :=
    (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ Set.range snf.f))
  refine ⟨B.reindex E, snf.bM, fun i j hij => ?_⟩
  obtain ⟨z, rfl⟩ := E.surjective j
  rw [Module.Basis.reindex_apply, E.symm_apply_apply]
  rcases z with a | l
  · have hEa : E (Sum.inl a) = snf.f a := rfl
    rw [hEa] at hij
    rw [hB1, hx, snf.snf a, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, if_neg hij.symm, smul_zero]
  · rw [hK _ (hB2 l), map_zero, Finsupp.zero_apply]

theorem smithMatrix {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) O) :
    ∃ P Q : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ i j, i ≠ j → (P * A * Q) i j = 0 := by
  classical
  obtain ⟨b, c, hbc⟩ := smithMatrix_lemma n (Matrix.toLin' A)
  refine ⟨c.toMatrix (Pi.basisFun O (Fin n)), (Pi.basisFun O (Fin n)).toMatrix b, ?_, ?_, fun i j hij => ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b (Pi.basisFun O (Fin n))
      c (Pi.basisFun O (Fin n)) (Matrix.toLin' A)
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h
    rw [h, LinearMap.toMatrix_apply]
    exact hbc i j hij

theorem smithPairing (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) :
    ∃ P Q : Matrix (Fin n) (Fin n) O, IsUnit P.det ∧ IsUnit Q.det ∧
      ∀ i j, i ≠ j → (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) i j = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => G p.1 p.2)
  have hA : ∀ i j, ∃ a : O, algebraMap O K a = (d : O) • G i j := fun i j => by
    obtain ⟨a, ha⟩ := hd (i, j) (Finset.mem_univ _)
    exact ⟨a, ha⟩
  choose A hA using hA
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := smithMatrix n (Matrix.of A)
  refine ⟨P, Q, hP, hQ, fun i j hij => ?_⟩
  have hd0 : algebraMap O K (d : O) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O K), (IsFractionRing.injective O K).eq_iff]
    exact nonZeroDivisors.coe_ne_zero d
  have key : (Matrix.of A).map (algebraMap O K) = algebraMap O K (d : O) • G := by
    ext i j
    simp [hA, Algebra.smul_def]
  have h2 : (P * Matrix.of A * Q).map (algebraMap O K) =
      algebraMap O K (d : O) • (P.map (algebraMap O K) * G * Q.map (algebraMap O K)) := by
    rw [Matrix.map_mul, Matrix.map_mul, key, Matrix.mul_smul, Matrix.smul_mul]
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.map_apply, hPQ i j hij, map_zero, Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left hd0

end Formalism.InvariantFactorPaths.KP
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_coe_basis {E : Type} [AddCommGroup E] [Module O E] (Λ : Submodule O E) {n : ℕ}
    (B : Module.Basis (Fin n) O Λ) : Submodule.span O (Set.range fun i => (B i : E)) = Λ := by
  have h : (Set.range fun i => (B i : E)) = Λ.subtype '' Set.range B := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem fock_zero_right {σ : Type} (F : MvPolynomial σ (KK O)) : fock F (0 : MvPolynomial σ (KK O)) = 0 := by
  simp [fock]

theorem smith_block {σ : Type} (Λ : Submodule O (MvPolynomial σ (KK O))) (hfg : Module.Finite O Λ) :
    ∃ (n : ℕ) (al be : Fin n → MvPolynomial σ (KK O)), (∀ i, al i ∈ Λ ∧ be i ∈ Λ) ∧
      (∀ i l, i ≠ l → fock (al i) (be l) = 0) ∧ LinearIndependent O al ∧
      Submodule.span O (Set.range al) = Λ ∧ Submodule.span O (Set.range be) = Λ := by
  classical
  haveI : Module.Free O Λ := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O Λ
  obtain ⟨P, Q, hP, hQ, hd⟩ := Formalism.InvariantFactorPaths.KP.smithPairing O (KK O) (Module.finrank O Λ)
    (Matrix.of fun a c => fock (e a : MvPolynomial σ (KK O)) (e c : MvPolynomial σ (KK O)))
  have hPt : IsUnit P.transpose.det := by rw [Matrix.det_transpose]; exact hP
  let alB := e.map (Matrix.toLinearEquiv e P.transpose hPt)
  let beB := e.map (Matrix.toLinearEquiv e Q hQ)
  have hal : ∀ i, (alB i : MvPolynomial σ (KK O)) = ∑ a, P i a • (e a : MvPolynomial σ (KK O)) := fun i => by
    show ((Matrix.toLin e e P.transpose (e i) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp [Matrix.transpose_apply]
  have hbe : ∀ l, (beB l : MvPolynomial σ (KK O)) = ∑ c, Q c l • (e c : MvPolynomial σ (KK O)) := fun l => by
    show ((Matrix.toLin e e Q (e l) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp
  refine ⟨_, fun i => (alB i : MvPolynomial σ (KK O)), fun i => (beB i : MvPolynomial σ (KK O)),
    fun i => ⟨(alB i).2, (beB i).2⟩, fun i l hil => ?_, ?_, span_coe_basis Λ alB, span_coe_basis Λ beB⟩
  · have h := hd i l hil
    show fock (alB i : MvPolynomial σ (KK O)) (beB l : MvPolynomial σ (KK O)) = 0
    rw [hal, hbe, fock_bilin]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  · exact alB.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)

theorem span_single {β E : Type} [DecidableEq β] [AddCommGroup E] [Module O E] (M : β → Submodule O E) (T : Finset β)
    (hM : ∀ b, b ∉ T → M b = ⊥) (n : β → ℕ) (al : ∀ b, Fin (n b) → E)
    (hspan : ∀ b, Submodule.span O (Set.range (al b)) = M b) :
    Submodule.span O (Set.range fun x : (Σ b : {b // b ∈ T}, Fin (n b.1)) =>
      (Pi.single x.1.1 (al x.1.1 x.2) : β → E)) = Submodule.pi Set.univ M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    beta_reduce
    by_cases h : i = x.1.1
    · subst h
      rw [Pi.single_eq_same, ← hspan]
      exact Submodule.subset_span ⟨x.2, rfl⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  · intro f hf
    rw [Submodule.mem_pi] at hf
    have hfT : f = ∑ b ∈ T, Pi.single b (f b) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_pi_single]
      split_ifs with hi
      · rfl
      · have h0 := hf i (Set.mem_univ i)
        rw [hM i hi, Submodule.mem_bot] at h0
        exact h0
    rw [hfT]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hfb : f b ∈ Submodule.span O (Set.range (al b)) := by
      rw [hspan]
      exact hf b (Set.mem_univ b)
    have e : (Pi.single b (f b) : β → E) = LinearMap.single O (fun _ : β => E) b (f b) := rfl
    rw [e]
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : β => E) b) hfb
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨⟨b, hb⟩, i⟩, rfl⟩

end Gen

open Classical in

theorem smithData_seg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] {s : ℕ}
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (hFG : ∀ b, Module.Finite O (blockLat O p r S aTop aPlus m b)) :
    ∃ (n : ℕ) (al be : Fin n → SegVs O r s S.t) (β : Fin n → SegBlock s r),
      SmithData (segForm O p r S) (segLat O p r S aTop aPlus m) n al be β := by
  have hfin := kf_kept_finite p r S aTop
  set T := hfin.toFinset with hT
  have hmemT : ∀ b, b ∈ T ↔ Kept p r S aTop b := fun b => by rw [hT, Set.Finite.mem_toFinset]; rfl
  let M : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥
  have hMfg : ∀ b, Module.Finite O (M b) := fun b => by
    by_cases hb : Kept p r S aTop b
    · have e : M b = blockLat O p r S aTop aPlus m b := if_pos hb
      rw [e]; exact hFG b
    · have e : M b = ⊥ := if_neg hb
      rw [e]; infer_instance
  have hM0 : ∀ b, b ∉ T → M b = ⊥ := fun b hb => if_neg fun h => hb ((hmemT b).2 h)
  choose n al be hmem horth hli hsa hsb using fun b => smith_block (M b) (hMfg b)
  let ι := Σ b : {b // b ∈ T}, Fin (n b.1)
  let ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let AL : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (al x.1.1 x.2)
  let BE : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (be x.1.1 x.2)
  have hL : segLat O p r S aTop aPlus m = Submodule.pi Set.univ M := rfl
  have hALs : Submodule.span O (Set.range AL) = Submodule.pi Set.univ M := span_single M T hM0 n al hsa
  have hBEs : Submodule.span O (Set.range BE) = Submodule.pi Set.univ M := span_single M T hM0 n be hsb
  refine ⟨Fintype.card ι, AL ∘ ev.symm, BE ∘ ev.symm, fun i => (ev.symm i).1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hL, ← hALs]
    refine ⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩
    rw [hALs, ← hBEs]
    exact Submodule.subset_span ⟨_, rfl⟩
  · intro i b hb
    exact ⟨Pi.single_eq_of_ne hb _, Pi.single_eq_of_ne hb _⟩
  · intro i l hil
    set x := ev.symm i with hx
    set y := ev.symm l with hy
    have hxy : x ≠ y := fun h => hil (ev.symm.injective h)
    show segForm O p r S (AL x) (BE y) = 0
    rw [segForm_eq_sum p r S {x.1.1} (AL x) (BE y) (fun b hb => Pi.single_eq_of_ne (by simpa using hb) _),
      Finset.sum_singleton]
    show _ * fock ((Pi.single x.1.1 (al x.1.1 x.2) : SegVs O r s S.t) x.1.1)
      ((Pi.single y.1.1 (be y.1.1 y.2) : SegVs O r s S.t) x.1.1) = 0
    rw [Pi.single_eq_same]
    by_cases hb : x.1.1 = y.1.1
    · obtain ⟨⟨xb, hxb⟩, xi⟩ := x
      obtain ⟨⟨yb, hyb⟩, yi⟩ := y
      simp only at hb
      subst hb
      rw [Pi.single_eq_same, horth xb xi yi (fun h => hxy (by rw [h])), mul_zero]
    · rw [Pi.single_eq_of_ne hb, fock_zero_right, mul_zero]
  · have h1 := Pi.linearIndependent_single (R := O) al hli
    have hj : Function.Injective (fun x : ι => (⟨x.1.1, x.2⟩ : Σ b, Fin (n b))) := by
      rintro ⟨⟨xb, hxb⟩, xi⟩ ⟨⟨yb, hyb⟩, yi⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      rw [eq_of_heq h2]
    exact (h1.comp _ hj).comp _ ev.symm.injective
  · rw [hL, ← hALs, EquivLike.range_comp]
  · rw [hL, ← hBEs, EquivLike.range_comp]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

section FG

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vK_wpow {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) (n : ℕ) :
    vK p (algebraMap O (KK O) (w ^ n)) = ((((n : ℚ) / 2 : ℚ)) : WithTop ℚ) := by
  rw [valuation_algebraMap_eq_alt p _ (pow_ne_zero _ hw.ne_zero), dvr_order_pow hw.ne_zero, nv_irr hw, ramE_two hw h2]
  push_cast
  ring_nf

theorem bb_coeff {p : ℕ} (S : UniformizedDVR p O) (h2 : S.w ^ 2 = (p : O)) {σ : Type} (sp : ℕ)
    (F : MvPolynomial σ (KK O)) (hF : F ∈ bbSpec O p σ sp) (μ : σ →₀ ℕ) :
    ∃ a : O, algebraMap O (KK O) (S.w ^ (padicValNat p (expFact μ) + padicValNat p sp)) * F.coeff μ =
      algebraMap O (KK O) a := by
  classical
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ', c, hc, rfl⟩ := hx
    rw [coeff_monomial]
    split_ifs with h
    · subst h
      apply (valuation_nonneg_iff_integral S _).1
      rw [valuation_mul_alt, vK_wpow S.w_irr h2]
      have e : (((padicValNat p (expFact μ') + padicValNat p sp : ℕ) : ℚ) / 2 : ℚ) =
          (padicValNat p (expFact μ') : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 := by push_cast; ring
      rw [e, add_comm]
      exact hc
    · exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [coeff_add, mul_add, ha, hb, map_add]⟩
  | smul o x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨o * a, ?_⟩
    rw [coeff_smul, Algebra.smul_def, map_mul, ← ha]
    ring

theorem fg_inter {p : ℕ} (S : UniformizedDVR p O) (h2 : S.w ^ 2 = (p : O)) {σ : Type} (sp : ℕ)
    (V : Submodule (KK O) (MvPolynomial σ (KK O))) (hV : FiniteDimensional (KK O) V) :
    Module.Finite O (V.restrictScalars O ⊓ bbSpec O p σ sp : Submodule O (MvPolynomial σ (KK O))) := by
  classical
  haveI := hV
  let bV := Module.finBasis (KK O) V
  let Sμ : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun k => ((bV k : V) : MvPolynomial σ (KK O)).support
  have hsupp : ∀ F ∈ V, ∀ μ, μ ∉ Sμ → F.coeff μ = 0 := by
    intro F hF μ hμ
    have hF' : (⟨F, hF⟩ : V) = ∑ k, (bV.repr ⟨F, hF⟩ k) • bV k := (bV.sum_repr _).symm
    have : F = ∑ k, (bV.repr ⟨F, hF⟩ k) • ((bV k : V) : MvPolynomial σ (KK O)) := by
      have h := congrArg (fun v : V => (v : MvPolynomial σ (KK O))) hF'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [this, coeff_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [coeff_smul]
    have : μ ∉ ((bV k : V) : MvPolynomial σ (KK O)).support := fun h =>
      hμ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, h⟩)
    rw [MvPolynomial.notMem_support_iff.1 this, smul_zero]
  set Λ := (V.restrictScalars O ⊓ bbSpec O p σ sp : Submodule O (MvPolynomial σ (KK O)))
  let nμ : (σ →₀ ℕ) → ℕ := fun μ => padicValNat p (expFact μ) + padicValNat p sp
  let gen : Sμ → (Sμ → KK O) := fun μ => Pi.single μ (algebraMap O (KK O) (S.w ^ nμ μ))⁻¹
  let N : Submodule O (Sμ → KK O) := Submodule.span O (Set.range gen)
  let Φ : MvPolynomial σ (KK O) →ₗ[O] (Sμ → KK O) :=
    { toFun := fun F μ => F.coeff μ
      map_add' := fun F G => by funext μ; simp
      map_smul' := fun o F => by funext μ; simp }
  have hΦN : ∀ F ∈ Λ, Φ F ∈ N := by
    intro F hF
    have hw0 : algebraMap O (KK O) (S.w ^ 1) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective O (KK O))]; exact pow_ne_zero _ S.w_irr.ne_zero
    choose a ha using fun μ => bb_coeff S h2 sp F hF.2 μ
    have : Φ F = ∑ μ : Sμ, a μ • gen μ := by
      funext μ
      simp only [Finset.sum_apply, Pi.smul_apply, gen]
      rw [Finset.sum_eq_single μ (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]) (by simp),
        Pi.single_eq_same]
      show F.coeff μ = a μ • (algebraMap O (KK O) (S.w ^ nμ μ))⁻¹
      have hne : algebraMap O (KK O) (S.w ^ nμ μ) ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective O (KK O))]; exact pow_ne_zero _ S.w_irr.ne_zero
      rw [Algebra.smul_def, ← ha μ]
      field_simp
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)
  have hinj : ∀ F ∈ Λ, Φ F = 0 → F = 0 := by
    intro F hF h0
    ext μ
    by_cases hμ : μ ∈ Sμ
    · exact congrFun h0 ⟨μ, hμ⟩
    · simpa using hsupp F hF.1 μ hμ
  haveI : Module.Finite O N := Module.Finite.span_of_finite O (Set.finite_range gen)
  haveI : IsNoetherian O N := isNoetherian_of_isNoetherianRing_of_finite O N
  let f : Λ →ₗ[O] N := (Φ.comp Λ.subtype).codRestrict N fun F => hΦN F.1 F.2
  refine Module.Finite.of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  apply Subtype.ext
  exact hinj F.1 F.2 (congrArg Subtype.val hF)

end FG

theorem blockFG_all (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] (s : ℕ)
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) (Sd : UniformizedDVR p O)
    (h2 : Sd.w ^ 2 = (p : O)) : Module.Finite O (blockLat O p r S aTop aPlus m b) := by
  exact fg_inter Sd h2 _ _ (spanSSZ_finite (O := O) (N := 2 * s + 1) (r := r) (blockData p S aTop aPlus m b))

theorem smithAt_all (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : SmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS _ _ j
  exact smithData_seg X.p X.m _ _ _ _ fun b => blockFG_all O X.p X.m _ _ _ _ _ b (dvrOfStd hS) (dvrOfStd_sq hS)

theorem restSmith : RestSmith := TransportedAlt.of_all fun _ _ _ _ _ _ _ _ _ _ => smithAt_all _ _ _ _ _ _ _ _ _ _

theorem partners_to_factors_holds : PartnersToFactors := partners_factors_of_smith_bases restSmith

end Formalism.MainNotions.ColumnSystems.Pf
end
end
