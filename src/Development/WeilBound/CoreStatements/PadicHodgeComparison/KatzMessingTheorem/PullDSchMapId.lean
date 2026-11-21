import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff

section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace CompanionTheory.KM

variable (k : Type) [Field k] [Fintype k] (kb : Type) [Field kb] [IsAlgClosed kb] [Algebra k kb]

abbrev Sk : Scheme := Spec (CommRingCat.of k)

structure Var where
  Y : Scheme
  s : Y ⟶ Sk k
  smooth : Smooth s
  proper : IsProper s

variable {k}

structure Corr (Y : Var k) where
  C : Scheme
  c₁ : C ⟶ Y.Y
  c₂ : C ⟶ Y.Y
  base : c₁ ≫ Y.s = c₂ ≫ Y.s
  fin₁ : IsFinite c₁
  fin₂ : IsFinite c₂
  et₁ : Etale c₁
  et₂ : Etale c₂

def IsFrobK (σ : kb →+* kb) : Prop := ∀ x, σ x = x ^ Fintype.card k

def Fix {Y : Var k} (c : Corr Y) (σ : kb →+* kb) (n : ℕ) : Set (Spec (CommRingCat.of kb) ⟶ c.C) :=
  {z | z ≫ c.c₁ ≫ Y.s = Spec.map (CommRingCat.ofHom (algebraMap k kb)) ∧
    z ≫ c.c₂ = Spec.map (CommRingCat.ofHom (σ ^ n)) ≫ z ≫ c.c₁}

structure CohModel (F : Type) [Field F] where

  H : Var k → ℕ → Type
  [acg : ∀ Y i, AddCommGroup (H Y i)]
  [mod : ∀ Y i, Module F (H Y i)]
  [fd : ∀ Y i, FiniteDimensional F (H Y i)]
  top : Var k → ℕ
  vanish : ∀ Y i, top Y < i → Subsingleton (H Y i)
  frob : ∀ Y i, H Y i →ₗ[F] H Y i
  act : ∀ {Y : Var k}, Corr Y → ∀ i, H Y i →ₗ[F] H Y i
  comm : ∀ {Y : Var k} (c : Corr Y) i, act c i ∘ₗ frob Y i = frob Y i ∘ₗ act c i

attribute [instance] CohModel.acg CohModel.mod CohModel.fd

variable {F : Type} [Field F] {E : Type} [Field E] [CharZero E]

def CohModel.actQ [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) (i : ℕ) :
    M.H Y i →ₗ[F] M.H Y i :=
  e.sum fun c a => algebraMap E F a • M.act c i

theorem CohModel.actQ_frob [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) (i : ℕ)
    (y : M.H Y i) : M.actQ e i (M.frob Y i y) = M.frob Y i (M.actQ e i y) := by
  unfold CohModel.actQ Finsupp.sum
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [LinearMap.smul_apply, map_smul]
  rw [← LinearMap.comp_apply (M.act c i), M.comm c i, LinearMap.comp_apply]

def Lefschetz (M : CohModel (k := k) F) : Prop :=
  ∀ (Y : Var k) (c : Corr Y) (σ : kb →+* kb), IsFrobK (k := k) kb σ → ∀ n : ℕ, 1 ≤ n →
    (Fix kb c σ n).Finite ∧
    ∑ i ∈ Finset.range (M.top Y + 1), (-1 : F) ^ i * LinearMap.trace F (M.H Y i) (M.act c i ∘ₗ M.frob Y i ^ n) =
      (Nat.card ↥(Fix kb c σ n) : F)

end CompanionTheory.KM
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison

namespace CompanionTheory.KM.Cris

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Fintype k] [CharP k p]

abbrev DX {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : Type 1 :=
  Wc.D p (B.schFn q) (RingHom.id k) n

abbrev Dcr (Y : Var k) (n : ℕ) : Type 1 := DX p Y.s n

def pullX {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of k)} {q' : X' ⟶ Spec (CommRingCat.of k)} (u : X ⟶ X')
    (hu : u ≫ q' = q) (n : ℕ) : DX p q' n →ₗ[Wc.K₀ p k] DX p q n :=
  Wc.pullD p (RingHom.id k) (B.schMap u hu) n

omit [Fact p.Prime] [Fintype k] in

theorem p_zero {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) {B₀ : CommRingCat.{0}} (y : Spec B₀ ⟶ X) :
    ((p : ℕ) : B₀) = 0 := by
  let g : k →+* B₀ := (Scheme.ΓSpecIso B₀).hom.hom.comp
    (((y ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  rw [← map_natCast g, CharP.cast_eq_zero, map_zero]

def frbq (f : ℕ) {B₀ : Type} [CommRing B₀] (h : ((p : ℕ) : B₀) = 0) : B₀ →+* B₀ := Wc.frb (l := p) h ^ f

theorem frbq_apply (f : ℕ) {B₀ : Type} [CommRing B₀] (h : ((p : ℕ) : B₀) = 0) (x : B₀) : frbq p f h x = x ^ p ^ f := by
  induction f generalizing x with
  | zero =>
    unfold frbq
    rw [pow_zero, pow_zero, pow_one]
    rfl
  | succ n ih =>
    have e : frbq p (n + 1) h x = frbq p n h (Wc.frb h x) := by
      unfold frbq
      rw [pow_succ]
      rfl
    rw [e, ih]
    change (x ^ p) ^ p ^ n = _
    rw [← pow_mul, ← pow_succ']

variable {p}

def qFrob {f : ℕ} (hq : Fintype.card k = p ^ f) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) :
    B.Fn.Map (B.schFn q) (B.schFn q) where
  u := { app := fun B₀ => TypeCat.ofHom fun (y : Spec B₀ ⟶ X) =>
            Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y
         naturality := fun B₀ B₁ φ => by
           ext y
           change Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q (Spec.map φ ≫ y)))) ≫ (Spec.map φ ≫ y) =
             Spec.map φ ≫ (Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y)
           rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
           congr 2
           ext x
           simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, frbq_apply, map_pow] }
  ov {B₀ y g} h := by
    change (Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y) ≫ q = Spec.map (CommRingCat.ofHom g)
    rw [Category.assoc, h, ← Spec.map_comp]
    congr 2
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, frbq_apply, ← map_pow, ← hq,
      FiniteField.pow_card]


variable (p)

def frobD {f : ℕ} (hq : Fintype.card k = p ^ f) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    DX p q n →ₗ[Wc.K₀ p k] DX p q n :=
  Wc.pullD p (RingHom.id k) (qFrob hq q) n

variable (k)

def PullFrob : Prop :=
  ∀ {f : ℕ} (hq : Fintype.card k = p ^ f) {X X' : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k))
    (q' : X' ⟶ Spec (CommRingCat.of k)) (u : X ⟶ X') (hu : u ≫ q' = q) (n : ℕ) (x : DX p q' n),
    pullX p u hu n (frobD p hq q' n x) = frobD p hq q n (pullX p u hu n x)

abbrev Push : Type 1 :=
  ∀ {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of k)} {q' : X' ⟶ Spec (CommRingCat.of k)} (g : X ⟶ X')
    (_ : g ≫ q' = q), IsFinite g → Etale g → ∀ n : ℕ, DX p q n →ₗ[Wc.K₀ p k] DX p q' n

variable {k}

def PushFrob (push : Push p k) : Prop :=
  ∀ {f : ℕ} (hq : Fintype.card k = p ^ f) {X X' : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k))
    (q' : X' ⟶ Spec (CommRingCat.of k)) (g : X ⟶ X') (hg : g ≫ q' = q) (hfin : IsFinite g) (het : Etale g) (n : ℕ)
    (x : DX p q n), push g hg hfin het n (frobD p hq q n x) = frobD p hq q' n (push g hg hfin het n x)

def actD (push : Push p k) {Y : Var k} (c : Corr Y) (n : ℕ) : Dcr p Y n →ₗ[Wc.K₀ p k] Dcr p Y n :=
  push c.c₂ c.base.symm c.fin₂ c.et₂ n ∘ₗ pullX p c.c₁ rfl n

variable (k)

class FinDim : Prop where
  fin : ∀ (Y : Var k) (n : ℕ), FiniteDimensional (Wc.K₀ p k) (Dcr p Y n)

def Vanish : Prop := ∀ Y : Var k, ∃ N : ℕ, ∀ n, N < n → Subsingleton (Dcr p Y n)

variable {k}

instance [h : FinDim p k] (Y : Var k) (n : ℕ) : FiniteDimensional (Wc.K₀ p k) (Dcr p Y n) := h.fin Y n

instance [FinDim p k] (Y : Var k) (n : ℕ) : Small.{0} (Dcr p Y n) := Module.Finite.small.{0} (Wc.K₀ p k) _

abbrev HS [FinDim p k] (Y : Var k) (n : ℕ) : Type := Shrink.{0} (Dcr p Y n)

def eS [FinDim p k] (Y : Var k) (n : ℕ) : HS p Y n ≃ₗ[Wc.K₀ p k] Dcr p Y n := Shrink.linearEquiv (Wc.K₀ p k) (Dcr p Y n)

def conjS [FinDim p k] {Y : Var k} {n : ℕ} (L : Dcr p Y n →ₗ[Wc.K₀ p k] Dcr p Y n) : HS p Y n →ₗ[Wc.K₀ p k] HS p Y n :=
  (eS p Y n).symm.toLinearMap ∘ₗ L ∘ₗ (eS p Y n).toLinearMap

theorem conjS_comp [FinDim p k] {Y : Var k} {n : ℕ} (L M : Dcr p Y n →ₗ[Wc.K₀ p k] Dcr p Y n) :
    conjS p L ∘ₗ conjS p M = conjS p (L ∘ₗ M) := by
  ext x
  simp [conjS]

def model [FinDim p k] {f : ℕ} (hq : Fintype.card k = p ^ f) (push : Push p k) (hV : Vanish p k) (hP : PullFrob p k)
    (hT : PushFrob p push) : CohModel (k := k) (Wc.K₀ p k) where
  H Y n := HS p Y n
  top Y := Classical.choose (hV Y)
  vanish Y n hn := by
    have := Classical.choose_spec (hV Y) n hn
    exact (eS p Y n).toEquiv.subsingleton
  frob Y n := conjS p (frobD p hq Y.s n)
  act c n := conjS p (actD p push c n)
  comm c n := by
    rw [conjS_comp, conjS_comp]
    congr 1
    ext x
    simp only [actD, LinearMap.comp_apply]
    rw [hP hq _ _ c.c₁ rfl n x, hT hq _ _ c.c₂ c.base.symm c.fin₂ c.et₂ n]

end CompanionTheory.KM.Cris
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison GlobalTheory.LogCris DividedPowers

namespace CompanionTheory.KM.Cris

section General

variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] (ρ : O →+* k)

def mapId (F : B.Fn O) : B.Fn.Map F F := ⟨𝟙 _, fun h => h⟩

def mapComp {F F' F'' : B.Fn O} (u : B.Fn.Map F F') (v : B.Fn.Map F' F'') : B.Fn.Map F F'' where
  u := u.u ≫ v.u
  ov h := v.ov (u.ov h)

omit [CommRing O] in
theorem map_ext [CommRing O] {F F' : B.Fn O} {u v : B.Fn.Map F F'} (h : u.u = v.u) : u = v := by
  cases u
  cases v
  cases h
  rfl

theorem pullMor_id (F : B.Fn O) (m j : ℕ) (x : CH.H (Wc.OM l F ρ m) j) : (Wc.pullMor l ρ (mapId F) m).pull j x = x := by
  refine (cr_pull_eq (Wc.pullMor l ρ (mapId F) m) (CH.Mor.id _)
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (DPMorphism.id _).isDPMorphism fun h => pt_id _ h _)
    (fun _ _ => rfl) (fun _ _ => rfl) j x).trans ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem limS_id (F : B.Fn O) (j : ℕ) : (Wc.pullS l ρ (mapId F) j).lim = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext (funext fun m => pullMor_id l ρ F m j (x.1 m))

theorem pullD_id (F : B.Fn O) (j : ℕ) (x : Wc.D l F ρ j) : Wc.pullD l ρ (mapId F) j x = x := by
  unfold Wc.pullD
  rw [limS_id, LinearMap.baseChange_id]
  rfl

omit [Fact l.Prime] [Field k] [CharP k l] [PerfectRing k l] in
theorem schMap_id {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (h : 𝟙 X ≫ q = q) :
    B.schMap (𝟙 X) h = mapId (B.schFn q) := by
  refine map_ext ?_
  ext B₀ y
  exact Category.comp_id y

theorem pullD_schMap_id {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (h : 𝟙 X ≫ q = q) (j : ℕ)
    (x : Wc.D l (B.schFn q) ρ j) : Wc.pullD l ρ (B.schMap (𝟙 X) h) j x = x := by
  rw [schMap_id, pullD_id]

end General

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [Fintype k] [CharP k p]

end CompanionTheory.KM.Cris
end
end
