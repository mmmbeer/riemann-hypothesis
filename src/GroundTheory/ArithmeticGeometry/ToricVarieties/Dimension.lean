import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.ExistsDualNegOfNotMemHullFinset

section
namespace GroundTheory.Arith.Toric

open Module PointedCone

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

def exposedFace (σ : PointedCone 𝕜 V) (u : Dual 𝕜 V) : PointedCone 𝕜 V :=
  σ ⊓ ofSubmodule (LinearMap.ker (u : V →ₗ[𝕜] 𝕜))

@[simp] theorem mem_exposedFace {σ : PointedCone 𝕜 V} {u : Dual 𝕜 V} {x : V} :
    x ∈ exposedFace σ u ↔ x ∈ σ ∧ u x = 0 := by
  simp [exposedFace]

theorem exposedFace_isFaceOf {σ : PointedCone 𝕜 V} {u : Dual 𝕜 V} (hu : ∀ x ∈ σ, 0 ≤ u x) :
    (exposedFace σ u).IsFaceOf σ where
  le := inf_le_left
  mem_of_smul_add_mem := by
    intro x y a hx hy ha h
    rw [mem_exposedFace] at h ⊢
    refine ⟨hx, ?_⟩
    have h2 : a * u x + u y = 0 := by simpa using h.2
    have h3 : a * u x = 0 := by nlinarith [mul_nonneg ha.le (hu x hx), hu y hy]
    exact (mul_eq_zero.1 h3).resolve_left ha.ne'

theorem isFaceOf_eq_hull_filter {F : PointedCone 𝕜 V} (S : Finset V) [DecidablePred (· ∈ F)]
    (hF : F.IsFaceOf (hull 𝕜 (S : Set V))) :
    F = hull 𝕜 ((S.filter (· ∈ F) : Finset V) : Set V) := by
  classical
  apply le_antisymm
  · intro x hxF
    have key : ∀ T : Finset V, T ⊆ S → ∀ x ∈ hull 𝕜 (T : Set V), x ∈ F →
        x ∈ hull 𝕜 ((T.filter (· ∈ F) : Finset V) : Set V) := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _ x hx _; simpa using hx
      | insert a T haT ih =>
        intro hTS x hx hxF
        have haS : a ∈ S := hTS (Finset.mem_insert_self a T)
        have hTS' : T ⊆ S := (Finset.subset_insert a T).trans hTS
        rw [Finset.coe_insert, mem_hull_insert] at hx
        obtain ⟨c, hc, y, hy, rfl⟩ := hx
        have hyS : y ∈ hull 𝕜 (S : Set V) := Submodule.span_mono (Finset.coe_subset.2 hTS') hy
        have haS' : a ∈ hull 𝕜 (S : Set V) := subset_hull haS
        have hyF : y ∈ F := hF.mem_of_add_mem_right (smul_mem _ hc haS') hyS hxF
        have hmono : hull 𝕜 ((T.filter (· ∈ F) : Finset V) : Set V) ≤
            hull 𝕜 (((insert a T).filter (· ∈ F) : Finset V) : Set V) :=
          Submodule.span_mono
            (Finset.coe_subset.2 (Finset.filter_subset_filter _ (Finset.subset_insert _ _)))
        rcases hc.eq_or_lt with rfl | hc
        · simpa using hmono (ih hTS' y hy hyF)
        · have haF : a ∈ F := hF.mem_of_smul_add_mem haS' hyS hc hxF
          exact add_mem (smul_mem _ hc.le (subset_hull (by simp [haF])))
            (hmono (ih hTS' y hy hyF))
    exact key S le_rfl x (hF.le hxF) hxF
  · rw [Submodule.span_le]
    intro y hy
    exact (Finset.mem_filter.1 hy).2

theorem fg_of_isFaceOf {σ F : PointedCone 𝕜 V} (hσ : σ.FG) (hF : F.IsFaceOf σ) : F.FG := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  exact ⟨_, (isFaceOf_eq_hull_filter S hF).symm⟩

theorem forall_hull_iff (S S' : Finset V) [DecidableEq V] (u : Dual 𝕜 V) :
    (∀ y ∈ ((S ∪ S'.image Neg.neg : Finset V) : Set V), 0 ≤ u y) ↔
      (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x) ∧ (∀ x ∈ hull 𝕜 (S' : Set V), u x ≤ 0) := by
  constructor
  · intro h
    refine ⟨fun x hx => nonneg_of_mem_hull (fun y hy => h y (by simp [hy])) hx, fun x hx => ?_⟩
    have := nonneg_of_mem_hull (f := -u) (s := (S' : Set V))
      (fun y hy => by simpa using h (-y) (by simp [hy])) hx
    simpa using this
  · rintro ⟨h1, h2⟩ y hy
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
      Set.mem_image] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact h1 y (subset_hull hy)
    · simpa using h2 z (subset_hull hz)

theorem exists_sub_of_mem_hull_union_neg (S S' : Finset V) [DecidableEq V] {x : V}
    (hx : x ∈ hull 𝕜 ((S ∪ S'.image Neg.neg : Finset V) : Set V)) :
    ∃ a ∈ hull 𝕜 (S : Set V), ∃ b ∈ hull 𝕜 (S' : Set V), x = a - b := by
  rw [Finset.coe_union] at hx
  obtain ⟨a, ha, b', hb', rfl⟩ := Submodule.mem_sup.1 ((Submodule.span_union _ _).le hx)
  have e : ((S'.image Neg.neg : Finset V) : Set V) = (-LinearMap.id : V →ₗ[𝕜] V) '' (S' : Set V) := by
    ext; simp
  rw [e] at hb'
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_hull_image (-LinearMap.id : V →ₗ[𝕜] V) hb'
  exact ⟨a, ha, b, hb, by simp [sub_eq_add_neg]⟩

theorem separation_of_generators (S S' : Finset V) (T : Finset (Dual 𝕜 V))
    (hT : ∀ u : Dual 𝕜 V, u ∈ hull 𝕜 (T : Set (Dual 𝕜 V)) ↔
      (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x) ∧ (∀ x ∈ hull 𝕜 (S' : Set V), u x ≤ 0))
    (h : (hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V)).IsFaceOf (hull 𝕜 (S : Set V)))
    (h' : (hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V)).IsFaceOf (hull 𝕜 (S' : Set V))) :
    (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ (∑ t ∈ T, t) x) ∧
      (∀ x ∈ hull 𝕜 (S' : Set V), (∑ t ∈ T, t) x ≤ 0) ∧
      exposedFace (hull 𝕜 (S : Set V)) (∑ t ∈ T, t) = hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V) ∧
      exposedFace (hull 𝕜 (S' : Set V)) (∑ t ∈ T, t) =
        hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V) := by
  classical
  set σ := hull 𝕜 (S : Set V)
  set σ' := hull 𝕜 (S' : Set V)
  set u : Dual 𝕜 V := ∑ t ∈ T, t with hu_def
  have hTmem : ∀ t ∈ T, (∀ x ∈ σ, 0 ≤ t x) ∧ (∀ x ∈ σ', t x ≤ 0) :=
    fun t ht => (hT t).1 (subset_hull ht)
  have hu : (∀ x ∈ σ, 0 ≤ u x) ∧ (∀ x ∈ σ', u x ≤ 0) :=
    (hT u).1 (Submodule.sum_mem _ fun t ht => subset_hull ht)
  have hu_apply : ∀ x, u x = ∑ t ∈ T, t x := fun x => by simp [hu_def]

  have key : ∀ z : V, z ∉ hull 𝕜 ((S ∪ S'.image Neg.neg : Finset V) : Set V) →
      ∃ t ∈ T, t z < 0 := by
    intro z hz
    obtain ⟨f, hf, hfz⟩ := exists_dual_neg_of_not_mem_hull_finset _ hz
    have hfT : f ∈ hull 𝕜 (T : Set (Dual 𝕜 V)) :=
      (hT f).2 ((forall_hull_iff S S' f).1 (fun y hy => hf y hy))
    by_contra hne
    push Not at hne
    have := nonneg_of_mem_hull (f := Dual.eval 𝕜 V z) (s := (T : Set (Dual 𝕜 V)))
      (fun t ht => by simpa using hne t ht) hfT
    simp at this
    linarith
  have hface : ∀ (C : PointedCone 𝕜 V) (R : Finset V) (u : Dual 𝕜 V), C = hull 𝕜 (R : Set V) →
      (∀ s ∈ R, u s = 0 → s ∈ σ ⊓ σ') → (∀ x ∈ C, 0 ≤ u x) →
      exposedFace C u ≤ σ ⊓ σ' := by
    intro C R u hC hR hCu
    have hE := exposedFace_isFaceOf hCu
    rw [hC] at hE
    rw [hC, isFaceOf_eq_hull_filter R hE, Submodule.span_le]
    intro s hs
    obtain ⟨hsR, hsE⟩ := Finset.mem_filter.1 hs
    exact hR s hsR (mem_exposedFace.1 hsE).2
  have hle : σ ⊓ σ' ≤ exposedFace σ u ⊓ exposedFace σ' u := by
    rintro x ⟨hx, hx'⟩
    have h0 : u x = 0 := le_antisymm (hu.2 x hx') (hu.1 x hx)
    exact ⟨mem_exposedFace.2 ⟨hx, h0⟩, mem_exposedFace.2 ⟨hx', h0⟩⟩
  refine ⟨hu.1, hu.2, le_antisymm ?_ (fun x hx => (hle hx).1),
    le_antisymm ?_ (fun x hx => (hle hx).2)⟩
  · refine hface σ S u rfl (fun s hs hus => ?_) hu.1
    by_contra hsτ
    have hsσ : s ∈ σ := subset_hull hs
    obtain ⟨t, ht, hts⟩ := key (-s) (fun hmem => by
      obtain ⟨a, ha, b, hb, hab⟩ := exists_sub_of_mem_hull_union_neg S S' hmem
      have hb' : b = s + a := by linear_combination (norm := module) hab
      have hbσ : b ∈ σ := hb' ▸ add_mem hsσ ha
      exact hsτ (h.mem_of_add_mem_left hsσ ha (hb' ▸ ⟨hbσ, hb⟩)))
    have hts' : 0 < t s := by simpa using hts
    have : t s ≤ u s := by
      rw [hu_apply]
      exact Finset.single_le_sum (f := fun t : Dual 𝕜 V => t s)
        (fun t ht => (hTmem t ht).1 s hsσ) ht
    linarith
  · have e : exposedFace σ' u = exposedFace σ' (-u) := by ext x; simp
    rw [e]
    refine hface σ' S' (-u) rfl (fun s hs hus => ?_) (fun x hx => by simpa using hu.2 x hx)
    · have hus : u s = 0 := by simpa using hus
      by_contra hsτ
      have hsσ' : s ∈ σ' := subset_hull hs
      obtain ⟨t, ht, hts⟩ := key s (fun hmem => by
        obtain ⟨a, ha, b, hb, hab⟩ := exists_sub_of_mem_hull_union_neg S S' hmem
        have ha' : a = s + b := by linear_combination (norm := module) -hab
        have haσ' : a ∈ σ' := ha' ▸ add_mem hsσ' hb
        exact hsτ (h'.mem_of_add_mem_left hsσ' hb (ha' ▸ ⟨ha, haσ'⟩)))
      have : u s ≤ t s := by
        rw [hu_apply]
        have := Finset.single_le_sum (f := fun t : Dual 𝕜 V => -t s)
          (fun t ht => by simpa using (hTmem t ht).2 s hsσ') ht
        simp only [Finset.sum_neg_distrib] at this
        linarith
      linarith

theorem exists_add_smul_mem_dual (S : Finset V) {u w : Dual 𝕜 V}
    (hu : ∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x)
    (hw : ∀ x ∈ exposedFace (hull 𝕜 (S : Set V)) u, 0 ≤ w x) :
    ∃ p : 𝕜, 0 ≤ p ∧ ∀ q : 𝕜, p ≤ q → ∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ w x + q * u x := by
  classical
  refine ⟨∑ s ∈ S, |-w s / u s|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun q hq x hx => ?_⟩
  have key : ∀ s ∈ (S : Set V), 0 ≤ (w + q • u) s := by
    intro s hs
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have hus := hu s (subset_hull hs)
    rcases hus.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero, add_zero]
      exact hw s (mem_exposedFace.2 ⟨subset_hull hs, h0.symm⟩)
    · have h1 : -w s / u s ≤ q :=
        (le_abs_self _).trans ((Finset.single_le_sum (f := fun s => |-w s / u s|)
          (fun _ _ => abs_nonneg _) (Finset.mem_coe.1 hs)).trans hq)
      rw [div_le_iff₀ hpos] at h1
      linarith
  simpa using nonneg_of_mem_hull key hx

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

theorem exists_finset_hull_eq_separating (S S' : Finset V) :
    ∃ T : Finset (Dual 𝕜 V), ∀ u : Dual 𝕜 V, u ∈ hull 𝕜 (T : Set (Dual 𝕜 V)) ↔
      (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x) ∧ (∀ x ∈ hull 𝕜 (S' : Set V), u x ≤ 0) := by
  classical
  obtain ⟨T, hT⟩ := fg_dual_finset (Dual.eval 𝕜 V) (S ∪ S'.image Neg.neg)
  refine ⟨T, fun u => ?_⟩
  rw [← forall_hull_iff S S' u]
  constructor
  · intro h y hy
    have h' : u ∈ dual (Dual.eval 𝕜 V) ((S ∪ S'.image Neg.neg : Finset V) : Set V) := by
      rw [← hT]; exact h
    simpa using h' hy
  · intro h
    have h' : u ∈ dual (Dual.eval 𝕜 V) ((S ∪ S'.image Neg.neg : Finset V) : Set V) :=
      fun y hy => by simpa using h y hy
    rw [← hT] at h'
    exact h'

theorem exists_separating {σ σ' : PointedCone 𝕜 V} (hσ : σ.FG) (hσ' : σ'.FG)
    (h : (σ ⊓ σ').IsFaceOf σ) (h' : (σ ⊓ σ').IsFaceOf σ') :
    ∃ u : Dual 𝕜 V, (∀ x ∈ σ, 0 ≤ u x) ∧ (∀ x ∈ σ', u x ≤ 0) ∧
      exposedFace σ u = σ ⊓ σ' ∧ exposedFace σ' u = σ ⊓ σ' := by
  obtain ⟨S, rfl⟩ := hσ
  obtain ⟨S', rfl⟩ := hσ'
  obtain ⟨T, hT⟩ := exists_finset_hull_eq_separating (𝕜 := 𝕜) S S'
  exact ⟨_, separation_of_generators S S' T hT h h'⟩

theorem isFaceOf_iff_exists_eq_exposedFace {σ F : PointedCone 𝕜 V} (hσ : σ.FG) :
    F.IsFaceOf σ ↔ ∃ u : Dual 𝕜 V, (∀ x ∈ σ, 0 ≤ u x) ∧ F = exposedFace σ u := by
  constructor
  · intro hF
    have hFσ : σ ⊓ F = F := inf_eq_right.2 hF.le
    obtain ⟨u, hu, -, hue, -⟩ := exists_separating hσ (fg_of_isFaceOf hσ hF)
      (by rw [hFσ]; exact hF) (by rw [hFσ])
    exact ⟨u, hu, by rw [hue, hFσ]⟩
  · rintro ⟨u, hu, rfl⟩
    exact exposedFace_isFaceOf hu

omit [FiniteDimensional 𝕜 V] in

theorem dual_id_dual_eval_of_fg {σ : PointedCone 𝕜 V} (hσ : σ.FG) :
    dual (LinearMap.id : Dual 𝕜 V →ₗ[𝕜] Dual 𝕜 V) (dual (Dual.eval 𝕜 V) (σ : Set V) : Set (Dual 𝕜 V))
      = σ := by
  refine le_antisymm (fun x hx => ?_) (fun x hx u hu => by simpa using hu hx)
  by_contra hxσ
  obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem hσ hxσ
  have hfd : f ∈ dual (Dual.eval 𝕜 V) (σ : Set V) := fun y hy => by simpa using hf y hy
  have := hx hfd
  simp only [LinearMap.id_apply] at this
  exact this.not_gt hfx

end FiniteDimensional

def dualFace (σ τ : PointedCone 𝕜 V) : PointedCone 𝕜 (Dual 𝕜 V) where
  carrier := {u | (∀ x ∈ σ, 0 ≤ u x) ∧ ∀ x ∈ τ, u x = 0}
  add_mem' := fun {u v} hu hv =>
    ⟨fun x hx => by simpa using add_nonneg (hu.1 x hx) (hv.1 x hx),
      fun x hx => by simp [hu.2 x hx, hv.2 x hx]⟩
  zero_mem' := ⟨fun _ _ => le_rfl, fun _ _ => rfl⟩
  smul_mem' := fun c u hu =>
    ⟨fun x hx => by
        have e : (c • u) x = (c : 𝕜) * u x := rfl
        rw [e]
        exact mul_nonneg c.2 (hu.1 x hx),
      fun x hx => by
        have e : (c • u) x = (c : 𝕜) * u x := rfl
        rw [e, hu.2 x hx, mul_zero]⟩

@[simp] theorem mem_dualFace {σ τ : PointedCone 𝕜 V} {u : Dual 𝕜 V} :
    u ∈ dualFace σ τ ↔ (∀ x ∈ σ, 0 ≤ u x) ∧ ∀ x ∈ τ, u x = 0 := Iff.rfl

def predualFace (σ : PointedCone 𝕜 V) (ν : PointedCone 𝕜 (Dual 𝕜 V)) : PointedCone 𝕜 V where
  carrier := {x | x ∈ σ ∧ ∀ u ∈ ν, u x = 0}
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun u hu => by simp [hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _⟩
  smul_mem' := fun c x hx =>
    ⟨Submodule.smul_mem _ c hx.1, fun u hu => by
      have e : u (c • x) = (c : 𝕜) * u x := by
        change u ((c : 𝕜) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [e, hx.2 u hu, mul_zero]⟩

@[simp] theorem mem_predualFace {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)} {x : V} :
    x ∈ predualFace σ ν ↔ x ∈ σ ∧ ∀ u ∈ ν, u x = 0 := Iff.rfl

theorem dualFace_isFaceOf {σ τ : PointedCone 𝕜 V} (hτ : τ ≤ σ) :
    (dualFace σ τ).IsFaceOf (dual (Dual.eval 𝕜 V) (σ : Set V)) where
  le := fun u hu x hx => by simpa using hu.1 x hx
  mem_of_smul_add_mem := by
    intro u v a hu hv ha h
    refine ⟨fun x hx => by simpa using hu hx, fun x hx => ?_⟩
    have h1 : 0 ≤ u x := by simpa using hu (hτ hx)
    have h2 : 0 ≤ v x := by simpa using hv (hτ hx)
    have h3 : a * u x + v x = 0 := by simpa using h.2 x hx
    have h4 : a * u x = 0 := by nlinarith [mul_nonneg ha.le h1]
    exact (mul_eq_zero.1 h4).resolve_left ha.ne'

theorem predualFace_isFaceOf {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)}
    (hν : ν ≤ dual (Dual.eval 𝕜 V) (σ : Set V)) : (predualFace σ ν).IsFaceOf σ where
  le := fun x hx => hx.1
  mem_of_smul_add_mem := by
    intro x y a hx hy ha h
    refine ⟨hx, fun u hu => ?_⟩
    have h1 : 0 ≤ u x := by simpa using hν hu hx
    have h2 : 0 ≤ u y := by simpa using hν hu hy
    have h3 : a * u x + u y = 0 := by simpa using h.2 u hu
    have h4 : a * u x = 0 := by nlinarith [mul_nonneg ha.le h1]
    exact (mul_eq_zero.1 h4).resolve_left ha.ne'

theorem dualFace_anti {σ τ₁ τ₂ : PointedCone 𝕜 V} (h : τ₁ ≤ τ₂) :
    dualFace σ τ₂ ≤ dualFace σ τ₁ :=
  fun _ hu => ⟨hu.1, fun x hx => hu.2 x (h hx)⟩

theorem predualFace_anti {σ : PointedCone 𝕜 V} {ν₁ ν₂ : PointedCone 𝕜 (Dual 𝕜 V)} (h : ν₁ ≤ ν₂) :
    predualFace σ ν₂ ≤ predualFace σ ν₁ :=
  fun _ hx => ⟨hx.1, fun u hu => hx.2 u (h hu)⟩

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

theorem predualFace_dualFace {σ τ : PointedCone 𝕜 V} (hσ : σ.FG) (hτ : τ.IsFaceOf σ) :
    predualFace σ (dualFace σ τ) = τ := by
  obtain ⟨u, hu, rfl⟩ := (isFaceOf_iff_exists_eq_exposedFace hσ).1 hτ
  apply le_antisymm
  · intro x hx
    exact mem_exposedFace.2 ⟨hx.1, hx.2 u ⟨hu, fun y hy => (mem_exposedFace.1 hy).2⟩⟩
  · intro x hx
    exact ⟨(mem_exposedFace.1 hx).1, fun v hv => hv.2 x hx⟩

theorem dualFace_predualFace {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)} (hσ : σ.FG)
    (hν : ν.IsFaceOf (dual (Dual.eval 𝕜 V) (σ : Set V))) :
    dualFace σ (predualFace σ ν) = ν := by
  have hσd : (dual (Dual.eval 𝕜 V) (σ : Set V)).FG := fg_dual _ hσ
  obtain ⟨φ, hφ, rfl⟩ := (isFaceOf_iff_exists_eq_exposedFace hσd).1 hν
  set x := (Module.evalEquiv 𝕜 V).symm φ with hx
  have hφx : ∀ u : Dual 𝕜 V, φ u = u x := fun u => by
    rw [hx, Module.apply_evalEquiv_symm_apply]
  have hxσ : x ∈ σ := by
    rw [← dual_id_dual_eval_of_fg hσ]
    intro u hu
    simpa [hφx] using hφ u hu
  apply le_antisymm
  · intro u hu
    refine mem_exposedFace.2 ⟨fun y hy => by simpa using hu.1 y hy, ?_⟩
    rw [hφx]
    exact hu.2 x ⟨hxσ, fun v hv => by simpa [hφx] using (mem_exposedFace.1 hv).2⟩
  · intro u hu
    obtain ⟨hu1, -⟩ := mem_exposedFace.1 hu
    exact ⟨fun y hy => by simpa using hu1 hy, fun y hy => hy.2 u hu⟩

def faceOrderIso {σ : PointedCone 𝕜 V} (hσ : σ.FG) :
    {τ : PointedCone 𝕜 V // τ.IsFaceOf σ} ≃o
      OrderDual {ν : PointedCone 𝕜 (Dual 𝕜 V) // ν.IsFaceOf (dual (Dual.eval 𝕜 V) (σ : Set V))} where
  toFun τ := OrderDual.toDual ⟨dualFace σ τ.1, dualFace_isFaceOf τ.2.le⟩
  invFun ν := ⟨predualFace σ (OrderDual.ofDual ν).1, predualFace_isFaceOf (OrderDual.ofDual ν).2.le⟩
  left_inv τ := Subtype.ext (predualFace_dualFace hσ τ.2)
  right_inv ν := Subtype.ext (dualFace_predualFace hσ (OrderDual.ofDual ν).2)
  map_rel_iff' := by
    intro τ₁ τ₂
    change dualFace σ τ₂.1 ≤ dualFace σ τ₁.1 ↔ τ₁.1 ≤ τ₂.1
    constructor
    · intro h
      have := predualFace_anti (σ := σ) h
      rwa [predualFace_dualFace hσ τ₁.2, predualFace_dualFace hσ τ₂.2] at this
    · exact dualFace_anti

end FiniteDimensional


end GroundTheory.Arith.Toric
end

section
namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct

section Comb

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]


theorem hull_basis_neg_eq_top {ι : Type*} (b : Basis ι 𝕜 E) :
    hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have key : ∀ y ∈ Submodule.span 𝕜 (Set.range b),
      y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) ∧
        -y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨subset_hull (Or.inl ⟨i, rfl⟩), subset_hull (Or.inr ⟨i, rfl⟩)⟩
    | zero => simp
    | add y z _ _ hy hz =>
      exact ⟨add_mem hy.1 hz.1, by rw [neg_add]; exact add_mem hy.2 hz.2⟩
    | smul c y _ hy =>
      rcases le_total 0 c with hc | hc
      · exact ⟨smul_mem _ hc hy.1, by rw [← smul_neg]; exact smul_mem _ hc hy.2⟩
      · refine ⟨?_, ?_⟩
        · rw [← neg_neg c, neg_smul, ← smul_neg]; exact smul_mem _ (neg_nonneg.2 hc) hy.2
        · rw [← neg_smul]; exact smul_mem _ (neg_nonneg.2 hc) hy.1
  exact (key x (by rw [b.span_eq]; exact Submodule.mem_top)).1

end Comb

section Integral

variable {L E : Type*} [AddCommGroup L] [AddCommGroup E] [Module ℝ E]

def IsRationalPolyhedral (ι : L →ₗ[ℤ] E) (σ : PointedCone ℝ E) : Prop :=
  ∃ S : Finset L, hull ℝ (ι '' S) = σ

theorem IsRationalPolyhedral.fg {ι : L →ₗ[ℤ] E} {σ : PointedCone ℝ E}
    (hσ : IsRationalPolyhedral ι σ) : σ.FG := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  exact ⟨S.image ι, by rw [Finset.coe_image]⟩

theorem hull_image_inf_halfspace_int [DecidableEq L] (ι : L →ₗ[ℤ] E) (T : Finset L)
    (g : Dual ℝ E) (gL : L →ₗ[ℤ] ℤ) (hg : ∀ l, g (ι l) = gL l) :
    hull ℝ (ι '' T) ⊓ (positive ℝ ℝ).comap g =
      hull ℝ (ι '' ↑(T.filter (fun t => 0 ≤ gL t) ∪
        ((T ×ˢ T).filter (fun st => 0 < gL st.1 ∧ gL st.2 < 0)).image
          (fun st => gL st.1 • st.2 - gL st.2 • st.1))) := by
  classical
  have h := hull_inf_halfspace (𝕜 := ℝ) (T.image ι) g
  rw [Finset.coe_image] at h
  rw [h]
  have hcomb : ∀ a b, g (ι a) • ι b - g (ι b) • ι a = ι (gL a • b - gL b • a) := by
    intro a b
    simp [hg, map_sub, Int.cast_smul_eq_zsmul]
  congr 1
  ext y
  simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image, Set.mem_union,
    Set.mem_ofPred_eq, Set.mem_image, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro (⟨⟨a, ha, rfl⟩, hga⟩ | ⟨s, t, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, h1, h2⟩, rfl⟩)
    · rw [hg] at hga
      exact ⟨a, Or.inl ⟨ha, by exact_mod_cast hga⟩, rfl⟩
    · rw [hg] at h1 h2
      refine ⟨gL a • b - gL b • a, Or.inr ⟨a, b, ⟨⟨ha, hb⟩, by exact_mod_cast h1,
        by exact_mod_cast h2⟩, rfl⟩, (hcomb a b).symm⟩
  · rintro ⟨l, (⟨hl, hgl⟩ | ⟨a, b, ⟨⟨ha, hb⟩, h1, h2⟩, rfl⟩), rfl⟩
    · exact Or.inl ⟨⟨l, hl, rfl⟩, by rw [hg]; exact_mod_cast hgl⟩
    · refine Or.inr ⟨ι a, ι b, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, by rw [hg]; exact_mod_cast h1,
        by rw [hg]; exact_mod_cast h2⟩, hcomb a b⟩

def latticePoints (ι : L →ₗ[ℤ] E) (τ : PointedCone ℝ E) : AddSubmonoid L :=
  τ.toAddSubmonoid.comap ι.toAddMonoidHom

@[simp]
theorem mem_latticePoints {ι : L →ₗ[ℤ] E} {τ : PointedCone ℝ E} {m : L} :
    m ∈ latticePoints ι τ ↔ ι m ∈ τ := Iff.rfl

end Integral

section Lattice

variable (N : Type*) [AddCommGroup N]

def toRealSpan : N →ₗ[ℤ] ℝ ⊗[ℤ] N := TensorProduct.mk ℤ ℝ N 1

def toRealDual : Dual ℤ N →ₗ[ℤ] Dual ℝ (ℝ ⊗[ℤ] N) := Module.Dual.baseChange ℝ

variable {N}

theorem toRealSpan_apply (n : N) : toRealSpan N n = (1 : ℝ) ⊗ₜ n := rfl

@[simp]
theorem toRealDual_apply_toRealSpan (m : Dual ℤ N) (n : N) :
    toRealDual N m (toRealSpan N n) = (m n : ℝ) := by
  simp [toRealDual, toRealSpan_apply, Module.Dual.baseChange_apply_tmul]

theorem toRealDual_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ N) (j : ι) :
    toRealDual N (e.dualBasis j) = (e.baseChange ℝ).dualBasis j := by
  refine (e.baseChange ℝ).ext fun i => ?_
  rw [Basis.dualBasis_apply_self, Basis.baseChange_apply, ← toRealSpan_apply,
    toRealDual_apply_toRealSpan, Basis.dualBasis_apply_self]
  split_ifs <;> simp

variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem isRationalPolyhedral_top_dual :
    IsRationalPolyhedral (toRealDual N) (⊤ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))) := by
  classical
  let e := Module.Free.chooseBasis ℤ N
  refine ⟨Finset.univ.image e.dualBasis ∪ Finset.univ.image (fun j => -e.dualBasis j), ?_⟩
  have h1 : (toRealDual N ∘ e.dualBasis) = (e.baseChange ℝ).dualBasis :=
    funext fun j => toRealDual_dualBasis e j
  have h2 : (toRealDual N ∘ fun j => -e.dualBasis j) = fun j => -(e.baseChange ℝ).dualBasis j :=
    funext fun j => by simp only [Function.comp_apply, map_neg, toRealDual_dualBasis]
  rw [← hull_basis_neg_eq_top (e.baseChange ℝ).dualBasis, Finset.coe_union, Finset.coe_image,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, h1, h2]

theorem isRationalPolyhedral_top :
    IsRationalPolyhedral (toRealSpan N) (⊤ : PointedCone ℝ (ℝ ⊗[ℤ] N)) := by
  classical
  let e := Module.Free.chooseBasis ℤ N
  refine ⟨Finset.univ.image e ∪ Finset.univ.image (fun j => -e j), ?_⟩
  have h1 : (toRealSpan N ∘ e) = e.baseChange ℝ :=
    funext fun j => by simp [Basis.baseChange_apply, toRealSpan_apply]
  have h2 : (toRealSpan N ∘ fun j => -e j) = fun j => -(e.baseChange ℝ) j :=
    funext fun j => by simp [Basis.baseChange_apply, toRealSpan_apply, TensorProduct.tmul_neg]
  rw [← hull_basis_neg_eq_top (e.baseChange ℝ), Finset.coe_union, Finset.coe_image,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, h1, h2]

theorem IsRationalPolyhedral.dual {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) :
    IsRationalPolyhedral (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N))) := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [dual_hull]
  induction S using Finset.induction_on with
  | empty => simpa using isRationalPolyhedral_top_dual
  | insert n S _ ih =>
    obtain ⟨T, hT⟩ := ih
    rw [Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hT,
      hull_image_inf_halfspace_int (toRealDual N) T _ (Dual.eval ℤ N n) (fun m => by simp)]
    exact ⟨_, rfl⟩

theorem IsRationalPolyhedral.predual {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) :
    IsRationalPolyhedral (toRealSpan N)
      (PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] Dual ℝ (ℝ ⊗[ℤ] N)) (τ : Set _)) := by
  classical
  obtain ⟨T, rfl⟩ := hτ
  rw [dual_hull]
  induction T using Finset.induction_on with
  | empty => simpa using isRationalPolyhedral_top
  | insert m T _ ih =>
    obtain ⟨S, hS⟩ := ih
    rw [Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hS,
      hull_image_inf_halfspace_int (toRealSpan N) S _ m (fun n => by simp)]
    exact ⟨_, rfl⟩

end Lattice

section Duality

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem dual_dual_eq_self {σ : PointedCone ℝ V} (hσ : σ.FG) :
    dual (LinearMap.id : Dual ℝ V →ₗ[ℝ] Dual ℝ V) (dual (Dual.eval ℝ V) (σ : Set V)) = σ :=
  dual_dual_flip_of_fg _ Function.surjective_id hσ

theorem IsRationalPolyhedral.sup {L : Type*} [AddCommGroup L] [DecidableEq L] {ι : L →ₗ[ℤ] V}
    {σ σ' : PointedCone ℝ V} (h : IsRationalPolyhedral ι σ) (h' : IsRationalPolyhedral ι σ') :
    IsRationalPolyhedral ι (σ ⊔ σ') := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨S', rfl⟩ := h'
  exact ⟨S ∪ S', by rw [Finset.coe_union, Set.image_union]; exact Submodule.span_union _ _⟩

end Duality

section Operations

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

theorem IsRationalPolyhedral.inf {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (h : IsRationalPolyhedral (toRealSpan N) σ) (h' : IsRationalPolyhedral (toRealSpan N) σ') :
    IsRationalPolyhedral (toRealSpan N) (σ ⊓ σ') := by
  classical
  have key : σ ⊓ σ' = PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] _)
      ((PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set _) ⊔
        PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ' : Set _) : PointedCone ℝ _) : Set _) := by
    rw [dual_sup, dual_union, dual_dual_eq_self h.fg, dual_dual_eq_self h'.fg]
  rw [key]
  exact (h.dual.sup h'.dual).predual

end Operations

section Gordan

variable {N : Type*} [AddCommGroup N]

def dualMonoid (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : AddSubmonoid (Dual ℤ N) :=
  latticePoints (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N)))

theorem mem_dualMonoid {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)} {m : Dual ℤ N} :
    m ∈ dualMonoid σ ↔ ∀ x ∈ σ, 0 ≤ toRealDual N m x := Iff.rfl

variable [Module.Free ℤ N] [Module.Finite ℤ N]



end Gordan

end GroundTheory.Arith.Toric
end

section
namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct


variable {N : Type*} [AddCommGroup N]


theorem dualMonoid_anti {σ₁ σ₂ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : σ₁ ≤ σ₂) :
    dualMonoid σ₂ ≤ dualMonoid σ₁ :=
  fun _ hm => mem_dualMonoid.2 fun x hx => mem_dualMonoid.1 hm x (h hx)

variable [Module.Free ℤ N] [Module.Finite ℤ N]



omit [Module.Free ℤ N] [Module.Finite ℤ N] in

theorem dualMonoid_exposedFace {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) {u : Dual ℤ N} (hu : u ∈ dualMonoid σ) :
    dualMonoid (exposedFace σ (toRealDual N u)) = dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [← Finset.coe_image] at hu ⊢
  apply le_antisymm
  · intro m hm
    obtain ⟨p, -, hp⟩ := exists_add_smul_mem_dual (S.image (toRealSpan N))
      (u := toRealDual N u) (w := toRealDual N m) (mem_dualMonoid.1 hu) (mem_dualMonoid.1 hm)
    have hk : p ≤ ((⌈p⌉₊ : ℕ) : ℝ) := Nat.le_ceil p
    rw [AddSubmonoid.mem_sup]
    refine ⟨m + ⌈p⌉₊ • u, mem_dualMonoid.2 fun x hx => ?_, ⌈p⌉₊ • (-u),
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_singleton _)) _,
      by rw [smul_neg, add_neg_cancel_right]⟩
    have := hp _ hk x hx
    rw [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact this
  · refine sup_le (dualMonoid_anti fun x hx => (mem_exposedFace.1 hx).1) ?_
    rw [AddSubmonoid.closure_le, Set.singleton_subset_iff]
    exact mem_dualMonoid.2 fun x hx => by simp [(mem_exposedFace.1 hx).2]

end GroundTheory.Arith.Toric
end

section
namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry

universe u

section SemigroupAlgebra

variable (k : Type*) [CommSemiring k] {G : Type*} [AddCommMonoid G]

noncomputable def semigroupAlgebra (S : AddSubmonoid G) : Subalgebra k (AddMonoidAlgebra k G) :=
  (AddMonoidAlgebra.supported k k (S : Set G)).toSubalgebra
    (by
      rw [AddMonoidAlgebra.mem_supported]
      exact (Finset.coe_subset.2 (support_coeff_one_subset)).trans
        (by simp [S.zero_mem]))
    (by
      classical
      intro x y hx hy
      rw [AddMonoidAlgebra.mem_supported] at hx hy ⊢
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset x y hm)
      exact S.add_mem (hx ha) (hy hb))

variable {k}

theorem mem_semigroupAlgebra {S : AddSubmonoid G} {f : AddMonoidAlgebra k G} :
    f ∈ semigroupAlgebra k S ↔ ↑f.coeff.support ⊆ (S : Set G) := Iff.rfl

theorem single_mem_semigroupAlgebra {S : AddSubmonoid G} {s : G} (hs : s ∈ S) (a : k) :
    single s a ∈ semigroupAlgebra k S := by
  rw [mem_semigroupAlgebra, coeff_single]
  exact (Finset.coe_subset.2 Finsupp.support_single_subset).trans (by simpa using hs)

theorem semigroupAlgebra_mono {S T : AddSubmonoid G} (h : S ≤ T) :
    semigroupAlgebra k S ≤ semigroupAlgebra k T :=
  fun _ hf => (mem_semigroupAlgebra.1 hf).trans (SetLike.coe_subset_coe.2 h)

theorem toSubmodule_semigroupAlgebra (S : AddSubmonoid G) :
    Subalgebra.toSubmodule (semigroupAlgebra k S) =
      Submodule.span k ((fun s => single s (1 : k)) '' (S : Set G)) :=
  AddMonoidAlgebra.supported_eq_span_single k (S : Set G)

theorem semigroupAlgebra_eq_adjoin (S : AddSubmonoid G) :
    semigroupAlgebra k S = Algebra.adjoin k ((fun s => single s (1 : k)) '' (S : Set G)) := by
  apply le_antisymm
  · intro f hf
    have : f ∈ Subalgebra.toSubmodule (semigroupAlgebra k S) := hf
    rw [toSubmodule_semigroupAlgebra] at this
    exact Algebra.span_le_adjoin k _ this
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact single_mem_semigroupAlgebra hs 1



variable (k) in

noncomputable def semigroupAlgebraEquiv (S : AddSubmonoid G) :
    AddMonoidAlgebra k S ≃ₐ[k] semigroupAlgebra k S :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k S.subtype)
      (mapDomain_injective Subtype.val_injective)).trans
    (Subalgebra.equivOfEq _ _ (by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        induction f using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
        | single s a =>
          have e : mapDomainAlgHom k k S.subtype (single s a) = single (s : G) a := by simp
          change mapDomainAlgHom k k S.subtype (single s a) ∈ _
          rw [e]
          exact single_mem_semigroupAlgebra s.2 a
      · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨single ⟨s, hs⟩ 1, by simp [mapDomainAlgHom_apply, mapDomain_single]⟩))

end SemigroupAlgebra

section Domain

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

theorem uniqueSums_of_free [Module.Free ℤ G] : UniqueSums G :=
  UniqueSums.of_injective_addHom
    ((Module.Free.chooseBasis ℤ G).repr.toLinearMap.toAddMonoidHom.toAddHom)
    (Module.Free.chooseBasis ℤ G).repr.injective inferInstance

instance isDomain_addMonoidAlgebra [IsDomain k] [Module.Free ℤ G] :
    IsDomain (AddMonoidAlgebra k G) :=
  haveI := uniqueSums_of_free (G := G)
  NoZeroDivisors.to_isDomain _

instance isDomain_semigroupAlgebra [IsDomain k] [Module.Free ℤ G] (S : AddSubmonoid G) :
    IsDomain (semigroupAlgebra k S) :=
  inferInstance

end Domain

section Localization

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

noncomputable abbrev semigroupAlgebraAlgebra {S T : AddSubmonoid G} (h : S ≤ T) :
    Algebra (semigroupAlgebra k S) (semigroupAlgebra k T) :=
  (Subalgebra.inclusion (semigroupAlgebra_mono h)).toRingHom.toAlgebra


end Localization

section Toric

variable {N : Type u} [AddCommGroup N] (k : Type u) [CommRing k]

noncomputable abbrev toricAlgebra (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    Subalgebra k (AddMonoidAlgebra k (Dual ℤ N)) :=
  semigroupAlgebra k (dualMonoid σ)

noncomputable abbrev affineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : Scheme.{u} :=
  Spec (CommRingCat.of (toricAlgebra k σ))

variable {k}
variable [Module.Free ℤ N] [Module.Finite ℤ N]


instance affineToricVariety_isIntegral [IsDomain k] (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    IsIntegral (affineToricVariety k σ) :=
  inferInstance

end Toric

section Faces

variable {N : Type u} [AddCommGroup N] {k : Type u} [CommRing k]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

variable (k) in

noncomputable def affineToricVarietyMap {σ τ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : τ ≤ σ) :
    affineToricVariety k τ ⟶ affineToricVariety k σ :=
  Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion (semigroupAlgebra_mono (k := k) (dualMonoid_anti h))).toRingHom)

end Faces

section Torus

variable (N : Type u) [AddCommGroup N] (k : Type u) [CommRing k]

noncomputable abbrev torus : Scheme.{u} :=
  Spec (CommRingCat.of (AddMonoidAlgebra k (Dual ℤ N)))

variable {N k}

variable (k) in

noncomputable def torusToAffineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    torus N k ⟶ affineToricVariety k σ :=
  Spec.map (CommRingCat.ofHom (toricAlgebra k σ).val.toRingHom)

variable [Module.Free ℤ N] [Module.Finite ℤ N]

end Torus

end GroundTheory.Arith.Toric
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial

section HalfSpace

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)

def LowerBound (f : AddMonoidAlgebra k G) (a : ℤ) : Prop :=
  ∀ m ∈ f.coeff.support, a ≤ φ m

variable {φ}

theorem LowerBound.mono {f : AddMonoidAlgebra k G} {a b : ℤ} (h : LowerBound φ f a) (hab : b ≤ a) :
    LowerBound φ f b :=
  fun m hm => hab.trans (h m hm)

theorem lowerBound_zero (a : ℤ) : LowerBound φ (0 : AddMonoidAlgebra k G) a := by
  intro m hm; simp at hm

theorem LowerBound.add {f g : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g a) : LowerBound φ (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (Finsupp.support_add (by simpa using hm)) with h | h
  · exact hf m h
  · exact hg m h

theorem LowerBound.neg {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a) :
    LowerBound φ (-f) a := by
  intro m hm
  exact hf m (by simpa using hm)

theorem LowerBound.sum {ι : Type*} (s : Finset ι) {f : ι → AddMonoidAlgebra k G} {a : ℤ}
    (hf : ∀ i ∈ s, LowerBound φ (f i) a) : LowerBound φ (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerBound_zero a
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem LowerBound.mul {f g : AddMonoidAlgebra k G} {a b : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g b) : LowerBound φ (f * g) (a + b) := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g hm)
  rw [map_add]
  exact add_le_add (hf x hx) (hg y hy)

theorem lowerBound_one : LowerBound φ (1 : AddMonoidAlgebra k G) 0 := by
  intro m hm
  have := support_coeff_one_subset hm
  simp only [Finset.mem_zero] at this
  rw [this, map_zero]

theorem LowerBound.pow {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a) (n : ℕ) :
    LowerBound φ (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using lowerBound_one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring

theorem LowerBound.coeff_eq_zero {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    {m : G} (hm : φ m < a) : f.coeff m = 0 := by
  by_contra h
  exact absurd (hf m (Finsupp.mem_support_iff.2 h)) (not_le.2 hm)

end HalfSpace

section GroupAlgebra

variable (k : Type*) [CommRing k] [IsDomain k] [IsIntegrallyClosed k]

variable {k} {G : Type*} [AddCommGroup G] {ι : Type*} (b : Basis ι ℤ G)

noncomputable def natCombination : (ι →₀ ℕ) →+ G where
  toFun c := Finsupp.linearCombination ℤ b (c.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero)
  map_zero' := by simp
  map_add' c d := by
    rw [← map_add]
    congr 1
    exact Finsupp.mapRange_add (fun _ _ => Nat.cast_add _ _) c d

theorem repr_natCombination (c : ι →₀ ℕ) :
    b.repr (natCombination b c) = c.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero :=
  b.repr_linearCombination _

theorem natCombination_injective : Function.Injective (natCombination b) := by
  intro c d h
  have := congrArg b.repr h
  rw [repr_natCombination, repr_natCombination] at this
  ext i
  have := congrArg (fun f => f i) this
  simpa using this

variable (k) in

noncomputable def mvPolynomialEquiv :
    MvPolynomial ι k ≃ₐ[k] semigroupAlgebra k (AddMonoidHom.mrange (natCombination b)) :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k (natCombination b))
      (mapDomain_injective (natCombination_injective b))).trans
    (Subalgebra.equivOfEq _ _ (by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        induction f using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
        | single c a =>
          have e : mapDomainAlgHom k k (natCombination b) (single c a) =
              single (natCombination b c) a := by simp
          change mapDomainAlgHom k k (natCombination b) (single c a) ∈ _
          rw [e]
          exact single_mem_semigroupAlgebra (AddMonoidHom.mem_mrange.2 ⟨c, rfl⟩) a
      · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨s, ⟨c, rfl⟩, rfl⟩
        exact ⟨single c 1, by simp⟩))

end GroupAlgebra

section Normal

variable {k : Type*} [CommRing k] [IsDomain k] [IsIntegrallyClosed k]

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

end Normal

end GroundTheory.Arith.Toric
end

section
namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra

section IntegralDim

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

theorem ringKrullDim_le_of_isIntegral : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ hpq =>
    Ideal.IsIntegral.comap_lt_comap (R := R) hpq

theorem exists_ltSeries_lift (hinj : Function.Injective (algebraMap R A))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ l' : LTSeries (PrimeSpectrum A), l'.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R A) l'.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal A)
      (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, PrimeSpectrum.ext hQx⟩
  | snoc p x hx ih =>
    obtain ⟨l', hlen, hlast⟩ := ih
    have hle : l'.last.asIdeal.comap (algebraMap R A) ≤ x.asIdeal := by
      have := congrArg PrimeSpectrum.asIdeal hlast
      rw [PrimeSpectrum.comap_asIdeal] at this
      rw [this]
      exact le_of_lt hx
    obtain ⟨Q, hQle, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal l'.last.asIdeal hle
    have hlt : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle fun h => ?_
      have h1 : PrimeSpectrum.comap (algebraMap R A) l'.last = x := by
        rw [h]; exact PrimeSpectrum.ext hQx
      exact (ne_of_lt hx) (hlast.symm.trans h1)
    exact ⟨l'.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], PrimeSpectrum.ext (by simpa using hQx)⟩

theorem ringKrullDim_le_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim R ≤ ringKrullDim A := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift hinj l
  exact le_iSup_of_le l' (by rw [hlen])

theorem ringKrullDim_eq_of_isIntegral (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective hinj)

end IntegralDim

section Trdeg

variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]


variable [Module.Finite ℤ G]


end Trdeg

section Dim

variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]



end Dim

end GroundTheory.Arith.Toric
end
