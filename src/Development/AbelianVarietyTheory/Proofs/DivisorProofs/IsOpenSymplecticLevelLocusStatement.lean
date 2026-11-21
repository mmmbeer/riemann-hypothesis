import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompPowPts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

def SympAt {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) (z : kˣ) : Prop :=
  (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))

theorem isSympLev_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type}
    [CommRing B] (ζ : B) (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) :
    IsSympLev P h M ζ t₁ lev ↔ (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
        (z : k) = β ζ → SympAt P h M lev k x z :=
  Iff.rfl

end GlobalTheory.SympLevLocus

namespace GlobalTheory.SympLevLocus

open GlobalTheory.SiegelPull in

theorem sympAt_pullback_iff {S T : Scheme.{0}} (g : T ⟶ S) {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over T}
    [GrpObj A'] [IsCommMonObj A'] {P : LB (G2 A).left} {P' : LB (G2 A').left} {φ : A'.left ⟶ A.left}
    {φ₂ : (G2 A').left ⟶ (G2 A).left} {h M : ℕ} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ A')} (hP : P.IsLB) (hP' : P'.IsLB)
    (pb : IsGrpPullback A' A g φ) (sq : IsSquare φ φ₂) (iso : LBIso P' (P.pull φ₂))
    (hl : ∀ a, (lev' a).left ≫ φ = g ≫ (lev a).left) (k : Type) [Field k] (x : Sp k ⟶ T) (z : kˣ) :
    SympAt P' h M lev' k x z ↔ SympAt P h M lev k (x ≫ g) z := by
  have push : ∀ a, pushHom pb (Over.mk x) (toUnit (Over.mk x) ≫ lev' a) = toUnit (Over.mk (x ≫ g)) ≫ lev a := by
    intro a
    apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (lev' a).left) ≫ φ = (toUnit (Over.mk (x ≫ g))).left ≫ (lev a).left
    rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl
  have inj := push_injective pb (Over.mk x)
  have surj := push_surjective pb (Over.mk x)
  refine and_congr (forall_congr' fun a => ?_) (and_congr ⟨fun H g₀ hg₀ => ?_, fun H g₀ hg₀ => ?_⟩
    (forall_congr' fun a => forall_congr' fun b => ?_))
  · rw [← inj.eq_iff, push, map_one]
  · obtain ⟨g₁, rfl⟩ := surj g₀
    obtain ⟨a, ha⟩ := H g₁ (inj (by rw [map_pow, map_one]; exact hg₀))
    exact ⟨a, (push a).symm.trans (congrArg _ ha)⟩
  · obtain ⟨a, ha⟩ := H (pushHom pb (Over.mk x) g₀) (by rw [← map_pow, hg₀, map_one])
    exact ⟨a, inj ((push a).trans ha)⟩
  · exact weilIs_grpPullback_of_comm S T A A' g φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb
      (diag_iso sq iso) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push a).symm) (congrArg (fun q => q.left) (push b).symm)

end GlobalTheory.SympLevLocus
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevTrivOpen

variable {S : Scheme.{0}}

theorem range_subset_iff_mem {k : Type} [Field k] (x : Sp k ⟶ S) (U : Set S) (p : Sp k) :
    Set.range x.base ⊆ U ↔ x.base p ∈ U := by
  refine ⟨fun h => h ⟨p, rfl⟩, ?_⟩
  rintro h _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

theorem pow_nsmul {G : Over S} [GrpObj G] {h : ℕ} (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G))
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (n : ℕ) (c : Fin h ⊕ Fin h → ℤ) : lev (n • c) = lev c ^ n := by
  have h0 : lev 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.LevTrivOpen

open GlobalTheory.LevCover GlobalTheory.LevTrivOpen in
theorem GlobalTheory.levTriv_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  intro S _ M t G _ _ h lev hab hM hadd hpow k _ _ x₀ hx₀
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    have := (GlobalTheory.SiegelTor.isUnit_natCast (n := M) (by omega)).map
      (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.SiegelTor.cycAway M))).inv.hom)
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G (hG := hab) hu
  have hU : ∀ f : 𝟙_ (Over S) ⟶ G, ∃ U : S.Opens, IsClosed (U : Set S) ∧ (f ^ M = 1 → ∀ (k' : Type) [Field k']
      [IsAlgClosed k'] (x : Sp k' ⟶ S), (toUnit (Over.mk x) ≫ f = 1 ↔ Set.range x.base ⊆ U)) := fun f => by
    by_cases hf : f ^ M = 1
    · obtain ⟨U, hUc, HU⟩ := GlobalTheory.TorsionSections.clopenCond_torsion_eq (n := M) (T := 𝟙_ (Over S)) hf (one_pow M)
      refine ⟨U, hUc, fun _ k' _ _ x => ?_⟩
      have := HU (Over.mk x) (toUnit (Over.mk x))
      simp only [MonObj.comp_one] at this
      simpa using this
    · exact ⟨⊤, isClosed_univ, fun h => absurd h hf⟩
  choose Uf hUc HU using hU
  classical
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) (show 0 < M by omega)
  let P : (Fin h ⊕ Fin h → ℤ) → Prop := fun a => ∃ b, a = M • b
  let A : (Fin h ⊕ Fin h → ℤ) → Set S := fun a => {s | s ∈ (Uf (lev a) : Set S) ↔ P a}
  have hAo : ∀ a, IsOpen (A a) := fun a => by
    by_cases hp : P a
    · convert (Uf (lev a)).isOpen using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_true, SetLike.mem_coe]
    · convert (hUc (lev a)).isOpen_compl using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_false, Set.mem_compl_iff, SetLike.mem_coe]
  have hAq : ∀ a a', q a = q a' → A a = A a' := fun a a' e => by
    obtain ⟨c, rfl⟩ := hq a a' e
    have hl : lev (a + M • c) = lev a := by rw [hadd, pow_nsmul lev hadd, hpow, _root_.mul_one]
    have hP : P (a + M • c) ↔ P a :=
      ⟨fun ⟨b, hb⟩ => ⟨b - c, by rw [smul_sub, ← hb]; abel⟩, fun ⟨b, hb⟩ => ⟨b + c, by rw [hb, smul_add]⟩⟩
    ext s
    simp only [A, Set.mem_setOf_eq, hl, hP]
  let pick : κ → (Fin h ⊕ Fin h → ℤ) := fun c => if hc : ∃ a, q a = c then hc.choose else 0
  have hpick : ∀ a, A a = A (pick (q a)) := fun a => by
    have hc : ∃ a', q a' = q a := ⟨a, rfl⟩
    refine hAq _ _ ?_
    simp only [pick, dif_pos hc]
    exact hc.choose_spec.symm
  refine ⟨⟨⋂ c, A (pick c), isOpen_iInter_of_finite fun c => hAo _⟩, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter]
    intro c
    show x₀.base p ∈ (Uf (lev (pick c)) : Set S) ↔ P (pick c)
    rw [← range_subset_iff_mem, ← HU _ (hpow _) k x₀]
    exact hx₀ _
  · intro k' _ _ x hx a
    obtain ⟨p⟩ := (inferInstance : Nonempty (Sp k'))
    have h1 := hx ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter] at h1
    have h2 : x.base p ∈ A a := by rw [hpick]; exact h1 _
    rw [HU _ (hpow a) k' x, range_subset_iff_mem _ _ p]
    exact h2
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_sections_exact_kernel_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  first | (exact @GlobalTheory.levTriv_locus_open) | (exact GlobalTheory.levTriv_locus_open) | (intros; apply GlobalTheory.levTriv_locus_open  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionFamily

section General

variable {S : Scheme.{0}}

noncomputable def torsionLift (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    T ⟶ torsion G n :=
  pullback.lift f (toUnit T) (by rw [GlobalTheory.GrpTangent.comp_mulN, hf, Hom.one_def])

@[reassoc]
theorem torsionLift_ι (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    torsionLift G f n hf ≫ torsion.ι G n = f :=
  pullback.lift_fst _ _ _

theorem torsion_ι_pow (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GlobalTheory.GrpTangent.comp_mulN, Hom.one_def]
  exact pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))

end General

end GlobalTheory.TorsionFamily
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevSurjOpen

theorem lev_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : Type} [AddCommGroup L]
    (lev : L → (𝟙_ (Over S) ⟶ G)) (hadd : ∀ a b, lev (a + b) = lev a * lev b) (a : L) :
    ∀ n : ℕ, lev (n • a) = lev a ^ n
  | 0 => by
    have h := hadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | n + 1 => by rw [succ_nsmul, hadd, lev_nsmul lev hadd a n, pow_succ]

theorem range_subset_iff_pt {k : Type} [Field k] {X : Scheme.{0}} (y : Sp k ⟶ X) (O : Set X) :
    Set.range y.base ⊆ O ↔ y.base (⊥ : PrimeSpectrum k) ∈ O := by
  haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Set.range_subset_iff]
  refine ⟨fun H => H _, fun H p => ?_⟩
  have : p = (⊥ : PrimeSpectrum k) := Subsingleton.elim (α := Sp k) p (⊥ : PrimeSpectrum k)
  rw [this]
  exact H

theorem torsion_hom_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : ℕ} {X : Over S} (u v : X ⟶ torsion G M)
    (h : u ≫ torsion.ι G M = v ≫ torsion.ι G M) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem exists_open_levSurj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  intro S _ M t G _ _ h lev hab hM hadd htors k _ _ x₀ hx₀
  haveI := hab
  have hM0 : M ≠ 0 := by omega
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    simpa using (GlobalTheory.SiegelTor.isUnit_natCast hM0).map
      ((Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv ≫ t.appTop).hom
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G hu
  haveI := hfin
  haveI := het
  let ℓ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ torsion G M) := fun a =>
    GlobalTheory.TorsionFamily.torsionLift G (lev a) M (htors a)
  have hℓ : ∀ a, ℓ a ≫ torsion.ι G M = lev a := fun a => GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

  have hcl : ∀ a, GlobalTheory.LevCover.ClopenCond (torsion G M)
      fun _ y => y ≫ 𝟙 (torsion G M) = y ≫ (toUnit (torsion G M) ≫ ℓ a) :=
    fun a => GlobalTheory.LevCover.clopenCond_eq _ _
  choose U hUc hU using hcl
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod (Fin h ⊕ Fin h → ℤ) (n := M) (by omega)
  let rep : Set.range q → (Fin h ⊕ Fin h → ℤ) := fun c => c.2.choose
  have hrep : ∀ a, lev (rep ⟨q a, a, rfl⟩) = lev a := by
    intro a
    obtain ⟨c, hc⟩ := hq _ _ ((⟨q a, a, rfl⟩ : Set.range q).2.choose_spec)
    have e := congrArg lev hc
    rw [hadd, lev_nsmul lev hadd, htors, _root_.mul_one] at e
    exact e.symm

  let Zs : Set (torsion G M).left := ⋃ c : Set.range q, (U (rep c) : Set (torsion G M).left)
  have hZo : IsOpen Zs := isOpen_iUnion fun c => (U _).isOpen
  have hZc : IsClosed Zs := isClosed_iUnion_of_finite fun c => hUc _
  let C : (torsion G M).left.Opens := ⟨Zsᶜ, hZc.isOpen_compl⟩
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := GlobalTheory.LevCover.exists_sub C hZo.isClosed_compl
  haveI := hVf
  haveI := hVe
  haveI : IsFinite (𝟙_ (Over S)).hom := by show IsFinite (𝟙 S); infer_instance
  haveI : Etale (𝟙_ (Over S)).hom := by show Etale (𝟙 S); infer_instance

  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.LevCover.exists_image (toUnit V)
  let U₁ : Set S := (U₀ : Set (𝟙_ (Over S)).left)
  have hU₁c : IsClosed U₁ := hU₀c
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S),
      Set.range x.base ⊆ U₁ ↔ Nonempty (Over.mk x ⟶ V) := by
    intro k' _ _ x
    have H := hU₀ k' x (toUnit _)
    have hz : (toUnit (Over.mk x) : Over.mk x ⟶ 𝟙_ (Over S)).left = x := by
      simpa using Over.w (toUnit (Over.mk x))
    rw [hz] at H
    exact H.trans ⟨fun ⟨w, _⟩ => ⟨w⟩, fun ⟨w⟩ => ⟨w, toUnit_unique _ _⟩⟩
  refine ⟨⟨U₁ᶜ, hU₁c.isOpen_compl⟩, ?_, ?_⟩
  · intro _ ⟨p, hp⟩ hpU
    subst hp
    have hr : Set.range x₀.base ⊆ U₁ := by
      rw [range_subset_iff_pt]
      have : p = (⊥ : PrimeSpectrum k) :=
        @Subsingleton.elim (Sp k) (inferInstanceAs (Subsingleton (PrimeSpectrum k))) p (⊥ : PrimeSpectrum k)
      rw [← this]
      exact hpU
    obtain ⟨w⟩ := (key k x₀).1 hr
    let y := w ≫ i
    have hy : Set.range y.left.base ⊆ (C : Set (torsion G M).left) := (hV _ y).2 ⟨w, rfl⟩
    have hg : (y ≫ torsion.ι G M) ^ M = 1 := by
      rw [← MonObj.comp_pow, GlobalTheory.TorsionFamily.torsion_ι_pow, MonObj.comp_one]
    obtain ⟨a, ha⟩ := hx₀ _ hg
    have e1 : (toUnit (Over.mk x₀) ≫ ℓ (rep ⟨q a, a, rfl⟩)) ≫ torsion.ι G M = toUnit _ ≫ lev a := by
      rw [Category.assoc, hℓ, hrep]
    have e2 : y ≫ torsion.ι G M = toUnit _ ≫ lev a := ha.symm
    have hy' : y = toUnit _ ≫ ℓ (rep ⟨q a, a, rfl⟩) := torsion_hom_ext _ _ (e2.trans e1.symm)
    have hin : Set.range y.left.base ⊆ (U (rep ⟨q a, a, rfl⟩) : Set (torsion G M).left) := by
      refine (hU _ _ y).1 ?_
      show y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ _
      rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _), ← hy']
    have h1 := (range_subset_iff_pt _ _).1 hy
    have h2 := (range_subset_iff_pt _ _).1 hin
    exact h1 (Set.mem_iUnion.2 ⟨⟨q a, a, rfl⟩, h2⟩)
  · intro k' _ _ x hx g hg
    let y := GlobalTheory.TorsionFamily.torsionLift G g M hg
    have hnC : ¬ Set.range y.left.base ⊆ (C : Set (torsion G M).left) := by
      intro H
      obtain ⟨w, -⟩ := (hV _ y).1 H
      have hr := (key k' x).2 ⟨w⟩
      have h1 := (range_subset_iff_pt _ _).1 hr
      have h2 := (range_subset_iff_pt _ _).1 hx
      exact h2 h1
    rw [range_subset_iff_pt] at hnC
    have hZ : y.left.base (⊥ : PrimeSpectrum k') ∈ Zs := not_not.1 hnC
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hZ
    have hin : Set.range y.left.base ⊆ (U (rep c) : Set (torsion G M).left) :=
      (range_subset_iff_pt _ _).2 hc
    have e : y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ (rep c) := (hU _ _ y).2 hin
    rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _)] at e
    refine ⟨rep c, ?_⟩
    rw [← hℓ, ← Category.assoc, ← e]
    exact GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

end GlobalTheory.LevSurjOpen
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  first | (exact @GlobalTheory.LevSurjOpen.exists_open_levSurj) | (exact GlobalTheory.LevSurjOpen.exists_open_levSurj) | (intros; apply GlobalTheory.LevSurjOpen.exists_open_levSurj  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
noncomputable section

namespace GlobalTheory.WeilOpenLocus

open GlobalTheory.CechPic GlobalTheory.DiagPairing GlobalTheory.LevCover

attribute [local instance] Over.cartesianMonoidalCategory

theorem biadd_noeth {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hG : Out.GlobalFnsSt)
    (hA : IsAbelianScheme A) (P : LB (G2 A).left) (hP : P.IsLB)
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) (T : Over S) (x x' y : T ⟶ A) :
    (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen,
      t.IsGen) ∧
    ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen,
      t.IsGen := by
  constructor
  · have := GlobalTheory.CubeNoeth.triv_add (𝟙 (A ⊗ A)) hG hA hP (by rw [Category.comp_id]; exact h₁)
      (by rw [Category.comp_id]; exact h₂) x x' y
    simp only [Category.comp_id] at this
    exact this
  · have sw : ∀ {T : Over S} (a b : T ⟶ A), lift a b ≫ lift (snd A A) (fst A A) = lift b a := fun a b => by
      rw [comp_lift, lift_snd, lift_fst]
    have := GlobalTheory.CubeNoeth.triv_add (lift (snd A A) (fst A A)) hG hA hP (by rw [sw]; exact h₂)
      (by rw [sw]; exact h₁) x x' y
    simp only [sw] at this
    exact this

theorem exists_weilIs_root {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (P : LB (G2 A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (N : ℕ) (hN : 0 < N) {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (biadd_noeth hG hA P hP r₁ r₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (biadd_noeth hG hA P hP r₁ r₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, GlobalTheory.CommutatorPairing.weilIs_unique hG hA hD hp (e₁' ▸ hc₁), hc₀⟩

theorem weil_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro S _ M t G _ _ P h lev hA hP r₁ r₂ _hsym hM3 _hodd ladd ltors k _ _ x₀ β₀ z₀ hx₀ hz₀ Hx₀
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hM0 : M ≠ 0 := by omega
  have hMpos : 0 < M := by omega
  have hMS : IsUnit (M : Γ(S, ⊤)) := by
    have := (isUnit_natCast hM0).map (fnOn t)
    rwa [map_natCast] at this
  let ζu : (cycAway M)ˣ := (cycBase hM0).ζ
  have hζv : (ζu : cycAway M) = zetaAway M := rfl
  have hzeta : zetaAway M ^ M = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp M hM0).pow_eq_one
  have hζu : ζu ^ M = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζv, Units.val_one]; exact hzeta)
  have hζM : ∀ (k : Type) [Field k] (β : cycAway M →+* k), Units.map β.toMonoidHom ζu ^ M = 1 := fun k _ β => by
    rw [← map_pow, hζu, map_one]
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond S := fun a c k _ _ x =>
    ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a)
        (toUnit (Over.mk x) ≫ lev c) (unitOn (z ^ (2 * omegaStd a c)))
  have locPair : ∀ a c, HkClopen.Loc (P2 a c) := fun a c => by
    obtain ⟨v, hv, hW⟩ := exists_weilIs_root hA P hP r₁ r₂ M hMpos (ltors a) (ltors c)
    refine (GlobalTheory.loc_units_eq S M v (Units.map (fnOn t).toMonoidHom (ζu ^ (2 * omegaStd a c))) hMS hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t)
      rw [map_fnOn _ g β hβ, ← GlobalTheory.SiegCover.unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζM, one_zpow]
      exact GlobalTheory.SiegCover.unitOn_one'
    · have hW' := GlobalTheory.CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk g)) hW
      have hgl : (toUnit (Over.mk g)).left = g := by simpa using Over.w (toUnit (Over.mk g))
      rw [hgl] at hW'
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t)
      have hu := map_fnOn _ g β hβ (ζu ^ (2 * omegaStd a c))
      rw [show Units.map β.toMonoidHom (ζu ^ (2 * omegaStd a c)) =
        Units.map β.toMonoidHom ζu ^ (2 * omegaStd a c) from map_zpow _ _ _] at hu
      have hzβ : ((Units.map β.toMonoidHom ζu : kˣ) : k) = β (zetaAway M) := by
        rw [Units.coe_map]; rfl
      constructor
      · intro E β' z hβ' hz
        obtain rfl : β = β' := spMap_inj' (hβ.symm.trans hβ')
        obtain rfl : z = Units.map β.toMonoidHom ζu := Units.ext (hz.trans hzβ.symm)
        rw [← hu, ← E]
        exact hW'
      · intro H
        exact GlobalTheory.CommutatorPairing.weilIs_unique hG hA hD hW' (hu ▸ H β _ hβ hzβ)
  have e1 : ∀ a c, lev (a + M • c) = lev a := fun a c => by
    rw [ladd, add_map_nsmul ladd, ltors, _root_.mul_one]
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + M • c₁) (a' + M • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β z hβ hz
    have hzM : z ^ M = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, hzeta, map_one, Units.val_one])
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + M • c₁) (a' + M • c₂) = omegaStd a a' + M * m :=
      ⟨_, GlobalTheory.SiegCover.omegaStd_add_nsmul M a a' c₁ c₂⟩
    have hz' : z ^ (2 * omegaStd (a + M • c₁) (a' + M • c₂)) = z ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (M * m) = M * (2 * m) by ring, zpow_mul _ (M : ℤ), zpow_natCast,
        hzM, one_zpow, _root_.mul_one]
    show Out.WeilIs _ _ _ _ _ _
    rw [e1, e1, hz']
    exact H β z hβ hz
  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hMpos
  haveI := hκ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  obtain ⟨V, hV, HV⟩ := localization₂
  refine ⟨⟨V, hV.isOpen⟩, ?_, fun k' _ _ x β z hxW hβ hz a b => ?_⟩
  · refine (HkClopen.range_subset_iff x₀ V).2 ((HV k x₀).2 fun a b β z hβ hz => ?_)
    obtain rfl : β₀ = β := spMap_inj' (hx₀.symm.trans hβ)
    obtain rfl : z₀ = z := Units.ext (hz₀.trans hz.symm)
    exact Hx₀ a b
  · exact (HV k' x).1 ((HkClopen.range_subset_iff x V).1 hxW) a b β z hβ hz

end GlobalTheory.WeilOpenLocus
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_bundle_level_odd : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.WeilOpenLocus.weil_open) | (exact GlobalTheory.WeilOpenLocus.weil_open) | (intros; apply GlobalTheory.WeilOpenLocus.weil_open  <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

theorem range_sub_iff {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (W : Set X) (p₀ : Sp k) :
    Set.range x.base ⊆ W ↔ x.base p₀ ∈ W := by
  refine ⟨fun H => H ⟨p₀, rfl⟩, ?_⟩
  rintro H _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p p₀]

open GlobalTheory.SiegelPull in

theorem exists_open_sympLev : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  intro h M S' _ t G _ _ P lev hab hP hr₁ hr₂ hsy hM hodd hadd htor
  let Good : S'.Opens → Prop := fun W => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S')
    (β : cycAway M →+* k) (z : kˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      SympAt P h M lev k x z
  have hsup : ∀ (k : Type) [Field k] (x : Sp k ⟶ S'), Set.range x.base ⊆ (sSup {W | Good W} : S'.Opens) →
      ∃ W, Good W ∧ Set.range x.base ⊆ W := by
    intro k _ x hx
    let p₀ : Sp k := (⊥ : PrimeSpectrum k)
    rw [range_sub_iff x _ p₀] at hx
    obtain ⟨W, hW, hpW⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨W, hW, (range_sub_iff x _ p₀).2 hpW⟩
  refine ⟨sSup {W | Good W}, fun V hV => ?_, ?_⟩
  · have pb := Pdiv.PullbackComparison.isGrpPullback V.ι G
    refine (isSympLev_iff _ _ _ _ _ _).2 ⟨fun a b => push_injective pb _ ?_, fun a => push_injective pb _ ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · rw [map_mul, push_secPull', push_secPull', push_secPull', hadd, MonObj.comp_mul]
    · rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, htor, MonObj.comp_one]
    · rw [sympAt_pullback_iff V.ι hP (pull_isLB hP _) pb (Pdiv.PullbackComparison.isSquare V.ι G)
        (Pdiv.PullbackComparison.gen_refl _ (pull_isLB hP _)) (fun a => secPull_left pb _)]
      obtain ⟨W, hW, hxW⟩ := hsup k (x ≫ V.ι) (by
        rintro _ ⟨p, rfl⟩
        exact hV (by first | exact (x.base p).2 | simp | (rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩)))
      exact hW k (x ≫ V.ι) β z hxW (by rw [Category.assoc]; exact hx) hz
  · intro T g c' φ φ₂ pb sq iso hl
    rintro _ ⟨τ, rfl⟩
    obtain ⟨K, _, _, x₀, ⟨q, hq⟩⟩ := GlobalTheory.SiegelTypings.exists_geomPt τ
    obtain ⟨β, hβ⟩ := (⟨(Spec.preimage (x₀ ≫ g ≫ t)).hom, by simp [spMap]⟩ : ∃ β : cycAway M →+* K, spMap β = x₀ ≫ g ≫ t)
    let z : Kˣ := ((GlobalTheory.LowChart.isUnit_zetaAway M hM).map β).unit
    have hc : SympAt c'.P h M c'.lev K x₀ z := c'.geom K x₀ β z hβ.symm rfl
    obtain ⟨hS₁, hS₂, hS₃⟩ := (sympAt_pullback_iff g hP c'.isLB pb sq iso hl K x₀ z).1 hc
    have e₁ := GlobalTheory.T.level_sections_exact_kernel_locus_open S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₂ := GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₃ := GlobalTheory.T.symmetric_bundle_level_odd S' M t G P h lev hab hP hr₁ hr₂ hsy hM hodd hadd htor K (x₀ ≫ g) β z (by rw [Category.assoc, hβ]) rfl
    obtain ⟨W₁, hW₁, H₁⟩ := e₁ hS₁
    obtain ⟨W₂, hW₂, H₂⟩ := e₂ hS₂
    obtain ⟨W₃, hW₃, H₃⟩ := e₃ hS₃
    have hgood : Good (W₁ ⊓ W₂ ⊓ W₃) := fun k _ _ x β' z' hx hxt hz' =>
      ⟨H₁ k x (hx.trans (le_trans inf_le_left inf_le_left)), H₂ k x (hx.trans (le_trans inf_le_left inf_le_right)),
        H₃ k x β' z' (hx.trans inf_le_right) hxt hz'⟩
    have hmem : g.base τ ∈ (W₁ ⊓ W₂ ⊓ W₃ : S'.Opens) := by
      have e : (x₀ ≫ g).base q = g.base τ := by first | simp [← hq] | (rw [Scheme.Hom.comp_apply, hq]) | (rw [Scheme.comp_base_apply, hq])
      rw [← e]
      exact ⟨⟨hW₁ ⟨q, rfl⟩, hW₂ ⟨q, rfl⟩⟩, hW₃ ⟨q, rfl⟩⟩
    exact (le_sSup (show W₁ ⊓ W₂ ⊓ W₃ ∈ {W | Good W} from hgood)) hmem

end GlobalTheory.SympLevLocus
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_symplecticLevel_locus : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.SympLevLocus.exists_open_sympLev) | (exact GlobalTheory.SympLevLocus.exists_open_sympLev) | (intros; apply GlobalTheory.SympLevLocus.exists_open_sympLev  <;> assumption)
end
