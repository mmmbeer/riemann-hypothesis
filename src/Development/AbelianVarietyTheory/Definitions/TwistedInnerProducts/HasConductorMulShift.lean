import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev Unif : Type _ := {q : 𝒪[k] // Irreducible q}

instance : Nonempty (Unif k) :=
  let ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  ⟨⟨q, hq⟩⟩

variable {k}

namespace Unif
variable (q : Unif k)

theorem ne_zero : ((q.1 : 𝒪[k]) : k) ≠ 0 := fun h => q.2.ne_zero (Subtype.ext h)

def unit : kˣ := Units.mk0 _ q.ne_zero

def inv : k := ((q.1 : 𝒪[k]) : k)⁻¹

theorem mem_max_iff {a : 𝒪[k]} : a ∈ maximalIdeal 𝒪[k] ↔ q.1 ∣ a := by
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem mem_max : q.1 ∈ maximalIdeal 𝒪[k] := q.mem_max_iff.2 dvd_rfl

@[simp] theorem smul_inv_smul {n : Type*} (x : n → k) : q.1 • q.inv • x = x := by
  change ((q.1 : 𝒪[k]) : k) • q.inv • x = x
  rw [smul_smul, inv, mul_inv_cancel₀ q.ne_zero, one_smul]

@[simp] theorem inv_smul_smul {n : Type*} (x : n → k) : q.inv • q.1 • x = x := by
  rw [smul_comm, smul_inv_smul]

end Unif

variable (k) in

structure Pair (n : Type*) where

  lat : Submodule 𝒪[k] (n → k)
  isLat : lat.IsLattice k

  fn : lat →ₗ[𝒪[k]] 𝓀[k]
  fn_ne : fn ≠ 0

variable {n n' : Type*}

namespace Pair

def HasVal (P : Pair k n) (x : n → k) (a : 𝓀[k]) : Prop := ∃ h : x ∈ P.lat, P.fn ⟨x, h⟩ = a

variable {P Q : Pair k n} {x y e : n → k} {a b : 𝓀[k]}

theorem HasVal.mem (h : P.HasVal x a) : x ∈ P.lat := h.1

theorem HasVal.unique (h : P.HasVal x a) (h' : P.HasVal x b) : a = b := h.2.symm.trans h'.2

theorem hasVal_fn (P : Pair k n) (x : P.lat) : P.HasVal x (P.fn x) := ⟨x.2, rfl⟩

theorem mem_lat_iff : x ∈ P.lat ↔ ∃ a, P.HasVal x a := ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h⟩ => h.1⟩

theorem HasVal.add (h : P.HasVal x a) (h' : P.HasVal y b) : P.HasVal (x + y) (a + b) :=
  ⟨add_mem h.1 h'.1, by rw [← h.2, ← h'.2, ← map_add]; rfl⟩

theorem HasVal.sub (h : P.HasVal x a) (h' : P.HasVal y b) : P.HasVal (x - y) (a - b) :=
  ⟨sub_mem h.1 h'.1, by rw [← h.2, ← h'.2, ← map_sub]; rfl⟩

theorem HasVal.smul (h : P.HasVal x a) (s : 𝒪[k]) : P.HasVal (s • x) (residue 𝒪[k] s * a) :=
  ⟨P.lat.smul_mem s h.1, by
    rw [← h.2, ← ResidueField.algebraMap_eq, ← Algebra.smul_def, ← map_smul]; rfl⟩

theorem ext (h : ∀ x a, P.HasVal x a ↔ Q.HasVal x a) : P = Q := by
  obtain ⟨L, hL, f, hf⟩ := P
  obtain ⟨L', hL', f', hf'⟩ := Q
  have : L = L' := by
    ext x
    exact (mem_lat_iff (P := ⟨L, hL, f, hf⟩)).trans
      ((exists_congr (h x)).trans (mem_lat_iff (P := ⟨L', hL', f', hf'⟩)).symm)
  subst this
  have : f = f' := by
    ext x
    exact ((h x _).1 ⟨x.2, rfl⟩).2.symm
  subst this
  rfl

theorem exists_hasVal_one (P : Pair k n) : ∃ e, P.HasVal e 1 := by
  obtain ⟨x, hx⟩ : ∃ x, P.fn x ≠ 0 := by
    by_contra h
    push Not at h
    exact P.fn_ne (LinearMap.ext h)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (P.fn x)⁻¹
  exact ⟨s • (x : n → k), by simpa [hs, inv_mul_cancel₀ hx] using (P.hasVal_fn x).smul s⟩

def ker (P : Pair k n) : Submodule 𝒪[k] (n → k) := (LinearMap.ker P.fn).map P.lat.subtype

theorem mem_ker : x ∈ P.ker ↔ P.HasVal x 0 :=
  ⟨fun ⟨y, hy, h⟩ => h ▸ ⟨y.2, hy⟩, fun ⟨h, h'⟩ => ⟨⟨x, h⟩, h', rfl⟩⟩

theorem ker_le (P : Pair k n) : P.ker ≤ P.lat := fun _ h => (mem_ker.1 h).mem

theorem smul_mem_ker {s : 𝒪[k]} (hs : s ∈ maximalIdeal 𝒪[k]) (hx : x ∈ P.lat) : s • x ∈ P.ker := by
  have := (P.hasVal_fn ⟨x, hx⟩).smul s
  rw [(residue_eq_zero_iff s).2 hs, zero_mul] at this
  exact mem_ker.2 this

theorem ker_isLat (P : Pair k n) : P.ker.IsLattice k := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  haveI := P.isLat
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian 𝒪[k] P.lat := inferInstance
    exact (IsNoetherian.noetherian _).map _
  · rw [eq_top_iff, ← P.isLat.span_eq_top, Submodule.span_le]
    intro x hx
    rw [← q.inv_smul_smul x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (smul_mem_ker q.mem_max hx))

def vec (P : Pair k n) : n → k := P.exists_hasVal_one.choose

theorem hasVal_vec (P : Pair k n) : P.HasVal P.vec 1 := P.exists_hasVal_one.choose_spec

theorem hasVal_iff (he : P.HasVal e 1) :
    P.HasVal x a ↔ ∃ s : 𝒪[k], residue 𝒪[k] s = a ∧ x - s • e ∈ P.ker := by
  constructor
  · intro h
    obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
    exact ⟨s, rfl, mem_ker.2 (by simpa using h.sub (he.smul s))⟩
  · rintro ⟨s, rfl, h⟩
    simpa using (mem_ker.1 h).add (he.smul s)

theorem hasVal_one_iff (he : P.HasVal e 1) : P.HasVal x 1 ↔ x - e ∈ P.ker :=
  ⟨fun h => mem_ker.2 (by simpa using h.sub he), fun h => by simpa using (mem_ker.1 h).add he⟩

theorem sub_vec_mem (he : P.HasVal e 1) : e - P.vec ∈ P.ker := (hasVal_one_iff P.hasVal_vec).1 he

theorem lat_eq (he : P.HasVal e 1) : P.lat = P.ker ⊔ Submodule.span 𝒪[k] {e} := by
  refine le_antisymm (fun x hx => ?_) (sup_le P.ker_le ((Submodule.span_singleton_le_iff_mem _ _).2 he.mem))
  obtain ⟨s, -, h⟩ := (hasVal_iff he).1 (P.hasVal_fn ⟨x, hx⟩)
  have := Submodule.add_mem_sup h (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e))
  simpa using this

theorem ext_ker (hk : P.ker = Q.ker) (he : P.HasVal e 1) (he' : Q.HasVal e 1) : P = Q :=
  ext fun _ _ => by rw [hasVal_iff he, hasVal_iff he', hk]

end Pair

structure IsGlue (L : Submodule 𝒪[k] (n → k)) (e : n → k) : Prop where
  isLat : L.IsLattice k
  not_mem : e ∉ L
  smul_mem : ∀ s ∈ maximalIdeal 𝒪[k], s • e ∈ L

theorem isGlue_iff (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {e : n → k} :
    IsGlue L e ↔ L.IsLattice k ∧ e ∉ L ∧ q.1 • e ∈ L := by
  refine ⟨fun h => ⟨h.1, h.2, h.3 _ q.mem_max⟩, fun h => ⟨h.1, h.2.1, fun s hs => ?_⟩⟩
  obtain ⟨t, rfl⟩ := q.mem_max_iff.1 hs
  rw [mul_comm, mul_smul]
  exact L.smul_mem _ h.2.2

theorem Pair.isGlue {P : Pair k n} {e : n → k} (he : P.HasVal e 1) : IsGlue P.ker e :=
  ⟨P.ker_isLat, fun h => one_ne_zero (he.unique (Pair.mem_ker.1 h)), fun _ hs => Pair.smul_mem_ker hs he.mem⟩

theorem IsGlue.smul_mem_iff {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) {s : 𝒪[k]} :
    s • e ∈ L ↔ s ∈ maximalIdeal 𝒪[k] := by
  refine ⟨fun hs => ?_, h.smul_mem s⟩
  by_contra hn
  obtain ⟨u, rfl⟩ := notMem_maximalIdeal.1 hn
  apply h.not_mem
  simpa [smul_smul] using L.smul_mem ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) hs

theorem IsGlue.exists_pair {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) :
    ∃ P : Pair k n, P.ker = L ∧ P.HasVal e 1 := by
  let j : 𝒪[k] →ₗ[𝒪[k]] (n → k) ⧸ L := L.mkQ ∘ₗ LinearMap.toSpanSingleton 𝒪[k] _ e
  have hj : ∀ s, j s = 0 ↔ s ∈ maximalIdeal 𝒪[k] := fun s => by
    rw [← h.smul_mem_iff]
    exact Submodule.Quotient.mk_eq_zero L
  let ι : 𝓀[k] →ₗ[𝒪[k]] (n → k) ⧸ L := (maximalIdeal 𝒪[k]).liftQ j fun s hs => (hj s).2 hs
  have hι : ∀ s, ι (residue 𝒪[k] s) = L.mkQ (s • e) := fun s => rfl
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
    exact (residue_eq_zero_iff s).2 ((hj s).1 ha)
  let M := L ⊔ Submodule.span 𝒪[k] {e}
  have hM : ∀ x : M, (L.mkQ ∘ₗ M.subtype) x ∈ LinearMap.range ι := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨residue _ s, ?_⟩
    simp [hι, (Submodule.Quotient.mk_eq_zero L).2 hy]
  let f : M →ₗ[𝒪[k]] 𝓀[k] :=
    (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hM
  have hf : ∀ x : M, ι (f x) = L.mkQ x := fun x => by
    have := (LinearEquiv.ofInjective ι hinj).apply_symm_apply (LinearMap.codRestrict _ _ hM x)
    exact congrArg Subtype.val this
  have he : e ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self e)
  have hfe : f ⟨e, he⟩ = 1 := hinj (by rw [hf, ← map_one (residue 𝒪[k]), hι, one_smul])
  haveI := h.isLat
  have hlat : M.IsLattice k := Submodule.IsLattice.of_le_of_isLattice_of_fg k (M := L) le_sup_left
    (h.isLat.fg.sup (Submodule.fg_span_singleton e))
  refine ⟨⟨M, hlat, f, fun h0 => by simp [h0] at hfe⟩, ?_, he, hfe⟩
  ext x
  rw [Pair.mem_ker]
  constructor
  · rintro ⟨hx, h0⟩
    have := hf ⟨x, hx⟩
    rw [show f ⟨x, hx⟩ = 0 from h0, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero L).1 this.symm
  · intro hx
    refine ⟨Submodule.mem_sup_left hx, hinj ?_⟩
    rw [map_zero]
    exact (hf _).trans ((Submodule.Quotient.mk_eq_zero L).2 hx)

def glue {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) : Pair k n := h.exists_pair.choose

section
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}

@[simp] theorem glue_ker (h : IsGlue L e) : (glue h).ker = L := h.exists_pair.choose_spec.1

theorem glue_hasVal (h : IsGlue L e) : (glue h).HasVal e 1 := h.exists_pair.choose_spec.2

theorem glue_lat (h : IsGlue L e) : (glue h).lat = L ⊔ Submodule.span 𝒪[k] {e} := by
  rw [Pair.lat_eq (glue_hasVal h), glue_ker]

theorem eq_glue_iff (h : IsGlue L e) {P : Pair k n} : P = glue h ↔ P.ker = L ∧ P.HasVal e 1 :=
  ⟨fun hP => hP ▸ ⟨glue_ker h, glue_hasVal h⟩, fun hP => Pair.ext_ker (hP.1.trans (glue_ker h).symm) hP.2 (glue_hasVal h)⟩

end

variable (k) in

structure GluePair (n : Type*) where

  ker : Submodule 𝒪[k] (n → k)
  isLat : ker.IsLattice k

  cls : (n → k) ⧸ ker
  cls_ne : cls ≠ 0
  smul_cls : ∀ s ∈ maximalIdeal 𝒪[k], s • cls = 0

def Pair.toGlue (P : Pair k n) : GluePair k n where
  ker := P.ker
  isLat := P.ker_isLat
  cls := P.ker.mkQ P.vec
  cls_ne h := (Pair.isGlue P.hasVal_vec).not_mem ((Submodule.Quotient.mk_eq_zero _).1 h)
  smul_cls s hs := (Submodule.Quotient.mk_eq_zero _).2 (Pair.smul_mem_ker hs P.hasVal_vec.mem)

theorem Pair.toGlue_bijective : Function.Bijective (Pair.toGlue : Pair k n → GluePair k n) := by
  constructor
  · intro P Q h
    have hk : P.ker = Q.ker := congrArg GluePair.ker h
    have key : ∀ (G G' : GluePair k n) (x y : n → k), G = G' → G.cls = G.ker.mkQ x → G'.cls = G'.ker.mkQ y →
        x - y ∈ G'.ker := by
      rintro G _ x y rfl h1 h2
      exact (Submodule.Quotient.eq _).1 (h1.symm.trans h2)
    exact Pair.ext_ker hk P.hasVal_vec ((Pair.hasVal_one_iff Q.hasVal_vec).2 (key _ _ _ _ h rfl rfl))
  · rintro ⟨L, hL, c, hc, hs⟩
    obtain ⟨e, rfl⟩ := L.mkQ_surjective c
    have h : IsGlue L e := ⟨hL, fun h => hc ((Submodule.Quotient.mk_eq_zero _).2 h),
      fun s hs' => (Submodule.Quotient.mk_eq_zero _).1 (hs s hs')⟩
    obtain ⟨P, rfl, hP⟩ := h.exists_pair
    refine ⟨P, ?_⟩
    have : P.ker.mkQ P.vec = P.ker.mkQ e := ((Submodule.Quotient.eq _).2 (Pair.sub_vec_mem hP)).symm
    simp only [Pair.toGlue, this]

def Pair.glueEquiv : Pair k n ≃ GluePair k n := Equiv.ofBijective _ Pair.toGlue_bijective

namespace Pair

instance (P : Pair k n) : P.lat.IsLattice k := P.isLat
instance (P : Pair k n) : P.ker.IsLattice k := P.ker_isLat

instance : SMul 𝓀[k]ˣ (Pair k n) where
  smul c P := ⟨P.lat, P.isLat, (c : 𝓀[k]) • P.fn, smul_ne_zero c.ne_zero P.fn_ne⟩

@[simp] theorem dia_lat (c : 𝓀[k]ˣ) (P : Pair k n) : (c • P).lat = P.lat := rfl

theorem dia_hasVal {c : 𝓀[k]ˣ} {P : Pair k n} {x : n → k} {a : 𝓀[k]} :
    (c • P).HasVal x a ↔ P.HasVal x ((c⁻¹ : 𝓀[k]ˣ) * a) :=
  exists_congr fun _ => by
    change (c : 𝓀[k]) * _ = a ↔ _
    rw [Units.eq_inv_mul_iff_mul_eq]

instance : MulAction 𝓀[k]ˣ (Pair k n) where
  one_smul P := ext fun x a => by simp [dia_hasVal]
  mul_smul c d P := ext fun x a => by simp only [dia_hasVal, _root_.mul_inv_rev, Units.val_mul, mul_assoc]

@[simp] theorem dia_ker (c : 𝓀[k]ˣ) (P : Pair k n) : (c • P).ker = P.ker := by
  ext x
  simp [mem_ker, dia_hasVal]

theorem dia_hasVal_one {c : 𝓀[k]ˣ} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) {s : 𝒪[k]}
    (hs : residue 𝒪[k] s = (c⁻¹ : 𝓀[k]ˣ)) : (c • P).HasVal (s • e) 1 := by
  rw [dia_hasVal, ← hs]
  exact he.smul s

open Classical in

def ev (P : Pair k n) (x : n → k) : 𝓀[k] := if h : x ∈ P.lat then P.fn ⟨x, h⟩ else 0

theorem hasVal_ev {P : Pair k n} {x : n → k} (h : x ∈ P.lat) : P.HasVal x (P.ev x) := ⟨h, by simp [ev, h]⟩

theorem HasVal.ev_eq {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) : P.ev x = a :=
  (hasVal_ev h.mem).unique h

end Pair

def Red (L : Submodule 𝒪[k] (n → k)) : Type _ := L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)

namespace Red
variable (L : Submodule 𝒪[k] (n → k))

instance : AddCommGroup (Red L) :=
  inferInstanceAs (AddCommGroup (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
instance : Module 𝒪[k] (Red L) :=
  inferInstanceAs (Module 𝒪[k] (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
instance : Module 𝓀[k] (Red L) :=
  inferInstanceAs (Module (𝒪[k] ⧸ maximalIdeal 𝒪[k]) (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
instance : IsScalarTower 𝒪[k] 𝓀[k] (Red L) :=
  inferInstanceAs
    (IsScalarTower 𝒪[k] (𝒪[k] ⧸ maximalIdeal 𝒪[k]) (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))

def mk : L →ₗ[𝒪[k]] Red L := (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L).mkQ

theorem mk_surjective : Function.Surjective (mk L) := Submodule.mkQ_surjective _

variable {L}

theorem mk_eq_zero (q : Unif k) {x : L} : mk L x = 0 ↔ q.inv • (x : n → k) ∈ L := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  rw [q.2.maximalIdeal_eq, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    simp
  · intro h
    exact ⟨⟨_, h⟩, trivial, Subtype.ext (q.smul_inv_smul _)⟩

theorem residue_smul (s : 𝒪[k]) (x : Red L) : residue 𝒪[k] s • x = s • x := algebraMap_smul 𝓀[k] s x

def out (x : Red L) : L := (mk_surjective L x).choose

@[simp] theorem mk_out (x : Red L) : mk L x.out = x := (mk_surjective L x).choose_spec

instance [L.IsLattice k] : Module.Finite 𝓀[k] (Red L) :=
  haveI : Module.Finite 𝒪[k] (Red L) := Module.Finite.of_surjective _ (mk_surjective L)
  Module.Finite.of_restrictScalars_finite 𝒪[k] _ _

instance [L.IsLattice k] : Finite (Red L) := Module.finite_of_finite 𝓀[k]

instance [L.IsLattice k] : Finite (Module.Dual 𝓀[k] (Red L)) := Module.finite_of_finite 𝓀[k]

theorem finrank_eq [Fintype n] [L.IsLattice k] : Module.finrank 𝓀[k] (Red L) = Fintype.card n := by
  let e : TensorProduct 𝒪[k] 𝓀[k] L ≃ₗ[𝒪[k]] Red L := TensorProduct.quotTensorEquivQuotSMul L (maximalIdeal 𝒪[k])
  let e' : TensorProduct 𝒪[k] 𝓀[k] L ≃ₗ[𝓀[k]] Red L := e.extendScalarsOfSurjective residue_surjective
  rw [← e'.finrank_eq, Module.finrank_baseChange, Submodule.IsLattice.finrank_of_pi k L]

theorem card_eq [Fintype n] [L.IsLattice k] : Nat.card (Red L) = SplitWeil.resCard k ^ Fintype.card n := by
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[k]), finrank_eq]
  rfl

end Red

def Pair.red (P : Pair k n) : Module.Dual 𝓀[k] (Red P.lat) :=
  let f : Red P.lat →ₗ[𝒪[k]] 𝓀[k] :=
    (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] P.lat).liftQ P.fn (Submodule.smul_le.2 fun _ hs x _ =>
      (Pair.mem_ker.1 (Pair.smul_mem_ker hs x.2)).2)
  f.extendScalarsOfSurjective residue_surjective

@[simp] theorem Pair.red_mk (P : Pair k n) (x : P.lat) : P.red (Red.mk _ x) = P.fn x := rfl

theorem Pair.red_ne (P : Pair k n) : P.red ≠ 0 := fun h =>
  P.fn_ne (LinearMap.ext fun x => by rw [← P.red_mk, h]; rfl)

section
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]

def ofDual (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : Pair k n where
  lat := L
  isLat := hL
  fn := f.1.restrictScalars 𝒪[k] ∘ₗ Red.mk L
  fn_ne h := f.2 (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Red.mk_surjective L x
    exact LinearMap.congr_fun h y)

@[simp] theorem ofDual_lat (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : (ofDual L f).lat = L := rfl

theorem ofDual_hasVal (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) (x : L) :
    (ofDual L f).HasVal x (f.1 (Red.mk L x)) := ⟨x.2, rfl⟩

theorem Pair.ofDual_red (P : Pair k n) : ofDual P.lat ⟨P.red, P.red_ne⟩ = P := rfl

def latEquiv : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} ≃ {P : Pair k n // P.lat = L} :=
  Equiv.ofBijective (fun f => ⟨ofDual L f, rfl⟩) <| by
    constructor
    · intro f g h
      refine Subtype.ext (LinearMap.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := Red.mk_surjective L x
      have h' : ofDual L f = ofDual L g := congrArg Subtype.val h
      exact (ofDual_hasVal L f y).unique (h' ▸ ofDual_hasVal L g y)
    · rintro ⟨P, rfl⟩
      exact ⟨⟨P.red, P.red_ne⟩, rfl⟩

variable (q : Unif k)

theorem isGlue_inv_smul {x : L} (hx : Red.mk L x ≠ 0) : IsGlue L (q.inv • (x : n → k)) :=
  (isGlue_iff q).2 ⟨hL, fun h => hx ((Red.mk_eq_zero q).2 h), by simp⟩

def up (x : {x : Red L // x ≠ 0}) : Pair k n :=
  glue (isGlue_inv_smul L q (x := x.1.out) (by simpa using x.2))

@[simp] theorem up_ker (x : {x : Red L // x ≠ 0}) : (up L q x).ker = L := glue_ker _

theorem up_hasVal_iff (x : {x : Red L // x ≠ 0}) (y : L) :
    (up L q x).HasVal (q.inv • (y : n → k)) 1 ↔ Red.mk L y = x.1 := by
  rw [up, Pair.hasVal_one_iff (glue_hasVal _), glue_ker, ← smul_sub, ← Submodule.coe_sub, ← Red.mk_eq_zero q,
    map_sub, Red.mk_out, sub_eq_zero]


def kerEquiv : {x : Red L // x ≠ 0} ≃ {P : Pair k n // P.ker = L} :=
  Equiv.ofBijective (fun x => ⟨up L q x, up_ker L q x⟩) <| by
    constructor
    · intro x y h
      have h' : up L q x = up L q y := congrArg Subtype.val h
      have := (up_hasVal_iff L q x x.1.out).2 (Red.mk_out _)
      rw [h', up_hasVal_iff, Red.mk_out] at this
      exact Subtype.ext this
    · rintro ⟨P, rfl⟩
      let y : P.ker := ⟨q.1 • P.vec, Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem⟩
      have hy : Red.mk _ y ≠ 0 := fun h =>
        (Pair.isGlue P.hasVal_vec).not_mem (by simpa [y] using (Red.mk_eq_zero q).1 h)
      refine ⟨⟨_, hy⟩, Subtype.ext (Pair.ext_ker (e := P.vec) (up_ker _ _ _) ?_ P.hasVal_vec)⟩
      simpa [y] using (up_hasVal_iff P.ker q ⟨_, hy⟩ y).2 rfl

end

theorem finite_lat (L : Submodule 𝒪[k] (n → k)) : {P : Pair k n | P.lat = L}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : Pair k n | P.lat = L} with h | ⟨P, rfl⟩
  · simp [h]
  · exact Finite.of_equiv _ (latEquiv P.lat)

theorem finite_ker (L : Submodule 𝒪[k] (n → k)) : {P : Pair k n | P.ker = L}.Finite := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  rcases Set.eq_empty_or_nonempty {P : Pair k n | P.ker = L} with h | ⟨P, rfl⟩
  · simp [h]
  · exact Finite.of_equiv _ (kerEquiv P.ker q)

def withLat (L : Submodule 𝒪[k] (n → k)) : Finset (Pair k n) := (finite_lat L).toFinset

def withKer (L : Submodule 𝒪[k] (n → k)) : Finset (Pair k n) := (finite_ker L).toFinset

@[simp] theorem mem_withLat {L : Submodule 𝒪[k] (n → k)} {P : Pair k n} : P ∈ withLat L ↔ P.lat = L :=
  (finite_lat L).mem_toFinset

@[simp] theorem mem_withKer {L : Submodule 𝒪[k] (n → k)} {P : Pair k n} : P ∈ withKer L ↔ P.ker = L :=
  (finite_ker L).mem_toFinset

theorem sum_withLat {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withLat L, F P = ∑ f, F (ofDual L f) := by
  haveI : Fintype {P : Pair k n // P.lat = L} := Fintype.ofEquiv _ (latEquiv L)
  rw [Finset.sum_subtype (withLat L) (p := fun P => P.lat = L) (fun _ => mem_withLat)]
  exact ((latEquiv L).sum_comp fun P => F P.1).symm

theorem sum_withKer {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k)
    [Fintype {x : Red L // x ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withKer L, F P = ∑ x, F (up L q x) := by
  haveI : Fintype {P : Pair k n // P.ker = L} := Fintype.ofEquiv _ (kerEquiv L q)
  rw [Finset.sum_subtype (withKer L) (p := fun P => P.ker = L) (fun _ => mem_withKer)]
  exact ((kerEquiv L q).sum_comp fun P => F P.1).symm

def cross (q : Unif k) (P₁ P : Pair k n) : 𝓀[k] := P.ev (q.1 • P₁.vec)

theorem cross_hasVal (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) {e : n → k} (he : P₁.HasVal e 1) :
    P.HasVal (q.1 • e) (cross q P₁ P) := by
  have h1 : q.1 • P₁.vec ∈ P.lat := h ▸ Pair.smul_mem_ker q.mem_max P₁.hasVal_vec.mem
  have h2 : q.1 • (e - P₁.vec) ∈ P.ker := Pair.smul_mem_ker q.mem_max (h ▸ Pair.sub_vec_mem he)
  simpa [smul_sub, cross] using (Pair.mem_ker.1 h2).add (Pair.hasVal_ev h1)


theorem cross_up_ofDual (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (x : {x : Red L // x ≠ 0})
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : cross q (up L q x) (ofDual L f) = f.1 x.1 := by
  have h := cross_hasVal q (P := ofDual L f) (up_ker L q x).symm ((up_hasVal_iff _ q x x.1.out).2 (Red.mk_out _))
  rw [q.smul_inv_smul] at h
  rw [h.unique (ofDual_hasVal L f _), Red.mk_out]

theorem cross_dia_right (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q P₁ (c • P) = c * cross q P₁ P := by
  have h1 := Pair.dia_hasVal.1 (cross_hasVal q (P := c • P) h P₁.hasVal_vec)
  rw [← h1.unique (cross_hasVal q h P₁.hasVal_vec), Units.mul_inv_cancel_left]

theorem cross_dia_left (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q (c • P₁) P = (c⁻¹ : 𝓀[k]ˣ) * cross q P₁ P := by
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (c⁻¹ : 𝓀[k]ˣ)
  have h1 := cross_hasVal q (P₁ := c • P₁) (h.trans (Pair.dia_ker _ _).symm) (Pair.dia_hasVal_one P₁.hasVal_vec hs)
  rw [smul_comm] at h1
  rw [h1.unique ((cross_hasVal q h P₁.hasVal_vec).smul s), hs]

section Action
variable [Fintype n] [DecidableEq n]

theorem mem_smul_iff {g : GL n k} {L : Submodule 𝒪[k] (n → k)} {x : n → k} : x ∈ g • L ↔ g⁻¹ • x ∈ L := by
  refine (Submodule.mem_smul_pointwise_iff_exists x g L).trans ?_
  exact ⟨fun ⟨y, hy, h⟩ => by simpa [← h] using hy, fun h => ⟨_, h, smul_inv_smul _ _⟩⟩

instance isLattice_smul (g : GL n k) (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k] : (g • L).IsLattice k := by
  refine ⟨hL.fg.map _, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : g⁻¹ • x ∈ Submodule.span k (L : Set (n → k)) := hL.span_eq_top ▸ trivial
  have h : Submodule.span k (L : Set (n → k)) ≤
      (Submodule.span k ((g • L : Submodule 𝒪[k] (n → k)) : Set (n → k))).comap
        (DistribMulAction.toLinearMap k _ g) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (Submodule.smul_mem_pointwise_smul y g L hy)
  have h2 : g • g⁻¹ • x ∈ Submodule.span k ((g • L : Submodule 𝒪[k] (n → k)) : Set (n → k)) := h hx
  rwa [smul_inv_smul] at h2

abbrev latStab (L : Submodule 𝒪[k] (n → k)) : Subgroup (GL n k) := MulAction.stabilizer (GL n k) L

namespace Pair

instance : SMul (GL n k) (Pair k n) where
  smul g P :=
    { lat := g • P.lat
      isLat := inferInstance
      fn := P.fn ∘ₗ (DistribMulAction.toLinearMap 𝒪[k] _ g⁻¹).restrict fun _ hx => mem_smul_iff.1 hx
      fn_ne := fun h => by
        have h1 := LinearMap.congr_fun h ⟨g • P.vec, Submodule.smul_mem_pointwise_smul _ g _ P.hasVal_vec.mem⟩
        have h2 : P.HasVal (g⁻¹ • g • P.vec) 0 := ⟨_, h1⟩
        rw [inv_smul_smul] at h2
        exact one_ne_zero (P.hasVal_vec.unique h2) }

@[simp] theorem smul_lat (g : GL n k) (P : Pair k n) : (g • P).lat = g • P.lat := rfl

theorem smul_hasVal {g : GL n k} {P : Pair k n} {x : n → k} {a : 𝓀[k]} :
    (g • P).HasVal x a ↔ P.HasVal (g⁻¹ • x) a :=
  ⟨fun ⟨h, h'⟩ => ⟨mem_smul_iff.1 h, h'⟩, fun ⟨h, h'⟩ => ⟨mem_smul_iff.2 h, h'⟩⟩

instance : MulAction (GL n k) (Pair k n) where
  one_smul P := ext fun x a => by simp [smul_hasVal]
  mul_smul g h P := ext fun x a => by simp only [smul_hasVal, _root_.mul_inv_rev, mul_smul]

instance : SMulCommClass (GL n k) 𝓀[k]ˣ (Pair k n) where
  smul_comm g c P := ext fun x a => by simp only [smul_hasVal, dia_hasVal]

theorem HasVal.gl_smul {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) (g : GL n k) :
    (g • P).HasVal (g • x) a := smul_hasVal.2 (by simpa using h)

@[simp] theorem smul_ker (g : GL n k) (P : Pair k n) : (g • P).ker = g • P.ker := by
  ext x
  rw [mem_ker, smul_hasVal, mem_smul_iff, mem_ker]

theorem smul_eq_iff {g : GL n k} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) :
    g • P = P ↔ g • P.ker = P.ker ∧ g • e - e ∈ P.ker := by
  rw [← hasVal_one_iff he]
  exact ⟨fun h => ⟨by rw [← smul_ker, h], by simpa [h] using he.gl_smul g⟩,
    fun h => ext_ker ((smul_ker g P).trans h.1) (he.gl_smul g) h.2⟩

end Pair

theorem cross_smul (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (g : GL n k) :
    cross q (g • P₁) (g • P) = cross q P₁ P := by
  have h1 := cross_hasVal q (P₁ := g • P₁) (P := g • P) (by simp [h]) (P₁.hasVal_vec.gl_smul g)
  rw [← smul_comm g] at h1
  exact h1.unique ((cross_hasVal q h P₁.hasVal_vec).gl_smul g)

theorem exists_gl_of_equiv {L L' : Submodule 𝒪[k] (n → k)} [L.IsLattice k] [L'.IsLattice k] (e : L ≃ₗ[𝒪[k]] L') :
    ∃ g : GL n k, ∀ x : L, g • (x : n → k) = e x := by
  let b := Module.Free.chooseBasis 𝒪[k] L
  let E : (n → k) ≃ₗ[k] (n → k) := (b.extendOfIsLattice k).equiv ((b.map e).extendOfIsLattice k) (Equiv.refl _)
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv E), ?_⟩
  have : (E.toLinearMap.restrictScalars 𝒪[k]) ∘ₗ L.subtype = L'.subtype ∘ₗ e.toLinearMap := by
    refine b.ext fun i => ?_
    have := (b.extendOfIsLattice k).equiv_apply i ((b.map e).extendOfIsLattice k) (Equiv.refl _)
    simpa [E] using this
  intro x
  refine Eq.trans ?_ (LinearMap.congr_fun this x)
  change LinearMap.toMatrix' E.toLinearMap *ᵥ (x : n → k) = E x
  rw [LinearMap.toMatrix'_mulVec]
  rfl

omit [Fintype n] [DecidableEq n] in

theorem Pair.exists_split (P : Pair k n) :
    ∃ (K : Submodule 𝒪[k] P.lat) (e : (K × 𝒪[k]) ≃ₗ[𝒪[k]] P.lat), ∀ z, P.fn (e z) = residue 𝒪[k] z.2 := by
  obtain ⟨F, hF⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  have hF' : ∀ x, residue 𝒪[k] (F x) = P.fn x := fun x => LinearMap.congr_fun hF x
  have hu : IsUnit (F ⟨P.vec, P.hasVal_vec.mem⟩) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, hF', P.hasVal_vec.2]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ : ∃ v, F v = 1 :=
    ⟨(u⁻¹ : 𝒪[k]ˣ).val • ⟨P.vec, P.hasVal_vec.mem⟩, by rw [map_smul, ← hu, smul_eq_mul, Units.inv_mul]⟩
  let j := (LinearMap.ker F).subtype.coprod (LinearMap.toSpanSingleton 𝒪[k] _ v)
  have hj : ∀ z, F (j z) = z.2 := fun z => by
    have := z.1.2
    rw [LinearMap.mem_ker] at this
    simp [j, hv, this]
  refine ⟨LinearMap.ker F, LinearEquiv.ofBijective j ⟨?_, fun x => ?_⟩, fun z => by rw [← hF', ← hj]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, s⟩ h
    have hs : s = 0 := by simpa [h] using (hj (y, s)).symm
    subst hs
    simpa [j] using h
  · exact ⟨(⟨x - F x • v, by simp [hv]⟩, F x), by simp [j]⟩

instance : MulAction.IsPretransitive (GL n k) (Pair k n) where
  exists_smul_eq P Q := by
    obtain ⟨K, e, he⟩ := P.exists_split
    obtain ⟨K', e', he'⟩ := Q.exists_split
    have h1 := e.finrank_eq
    have h2 := e'.finrank_eq
    rw [Module.finrank_prod, Submodule.IsLattice.finrank_of_pi k] at h1 h2
    let d : K ≃ₗ[𝒪[k]] K' := LinearEquiv.ofFinrankEq _ _ (by omega)
    let t : P.lat ≃ₗ[𝒪[k]] Q.lat := e.symm ≪≫ₗ d.prodCongr (LinearEquiv.refl _ _) ≪≫ₗ e'
    have ht : ∀ x, Q.fn (t x) = P.fn x := fun x => by
      obtain ⟨z, rfl⟩ := e.surjective x
      simp [t, he, he']
    obtain ⟨g, hg⟩ := exists_gl_of_equiv t
    refine ⟨g, Pair.ext fun x a => ?_⟩
    rw [Pair.smul_hasVal]
    constructor
    · rintro ⟨h, rfl⟩
      have := Q.hasVal_fn (t ⟨_, h⟩)
      rwa [← hg, ht, smul_inv_smul] at this
    · rintro ⟨h, rfl⟩
      obtain ⟨y, hy⟩ := t.surjective ⟨x, h⟩
      have hx : x = g • (y : n → k) := by rw [hg, hy]
      rw [← hy, ht, hx, inv_smul_smul]
      exact P.hasVal_fn y

end Action

section Std
variable [Fintype n]

variable (k n) in

def stdLat : Submodule 𝒪[k] (n → k) := LinearMap.range ((Algebra.linearMap 𝒪[k] k).compLeft n)

omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_stdLat {x : n → k} : x ∈ stdLat k n ↔ ∀ i, x i ∈ 𝒪[k] :=
  ⟨fun ⟨y, hy⟩ i => hy ▸ (y i).2, fun h => ⟨fun i => ⟨x i, h i⟩, rfl⟩⟩

instance : (stdLat k n).IsLattice k := by
  classical
  refine ⟨by rw [stdLat, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _, ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun k n).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  refine mem_stdLat.2 fun j => ?_
  rw [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

variable (k) in

def stdPair (i : n) : Pair k n where
  lat := stdLat k n
  isLat := inferInstance
  fn :=
    { toFun := fun x => residue 𝒪[k] ⟨x.1 i, mem_stdLat.1 x.2 i⟩
      map_add' := fun x y => by rw [← map_add]; rfl
      map_smul' := fun s x => by
        rw [RingHom.id_apply, Algebra.smul_def, ResidueField.algebraMap_eq, ← map_mul]; rfl }
  fn_ne h := by
    have := LinearMap.congr_fun h ⟨fun _ => 1, mem_stdLat.2 fun _ => one_mem _⟩
    exact one_ne_zero ((map_one (residue 𝒪[k])).symm.trans this)

theorem stdPair_hasVal {i : n} {x : n → k} {a : 𝓀[k]} :
    (stdPair k i).HasVal x a ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], residue 𝒪[k] ⟨x i, h i⟩ = a :=
  ⟨fun ⟨h, h'⟩ => ⟨mem_stdLat.1 h, h'⟩, fun ⟨h, h'⟩ => ⟨mem_stdLat.2 h, h'⟩⟩

instance [Nonempty n] : Nonempty (Pair k n) := ⟨stdPair k (Classical.arbitrary n)⟩

end Std

end GlobalTheory.LatPair
end
end

section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

section Forms

variable (k n) in

abbrev Form (M : Type*) : Type _ := Pair k n → M

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def sumOp (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) : Module.End ℂ (Form k n M) where
  toFun φ P := ∑ Q ∈ S P, w P Q • φ Q
  map_add' φ φ' := by
    ext P
    simp [Finset.sum_add_distrib]
  map_smul' c φ := by
    ext P
    simp [Finset.smul_sum, smul_comm c]

def dia : 𝓀[k]ˣ →* Module.End ℂ (Form k n M) where
  toFun c := LinearMap.funLeft ℂ M fun P => c • P
  map_one' := by
    ext φ P
    simp
  map_mul' c d := by
    ext φ P
    simp [mul_comm c d, mul_smul]

@[simp] theorem dia_apply (c : 𝓀[k]ˣ) (φ : Form k n M) (P : Pair k n) : dia c φ P = φ (c • P) := rfl

def Nm : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, dia c

variable (k n M) in

def Mram : Submodule ℂ (Form k n M) := LinearMap.ker Nm

def trLat (L : Submodule 𝒪[k] (n → k)) : Form k n M →ₗ[ℂ] M := ∑ P ∈ withLat L, LinearMap.proj P

def trKer (L : Submodule 𝒪[k] (n → k)) : Form k n M →ₗ[ℂ] M := ∑ P ∈ withKer L, LinearMap.proj P

def tr : Module.End ℂ (Form k n M) := LinearMap.pi fun P => trLat P.lat

def tr' : Module.End ℂ (Form k n M) := LinearMap.pi fun P => trKer P.ker

open Classical in

def Da (q : Unif k) (a : 𝓀[k]) : Module.End ℂ (Form k n M) :=
  sumOp (fun P₁ => (withLat P₁.ker).filter fun P => cross q P₁ P = a) fun _ _ => 1

def D (q : Unif k) : Module.End ℂ (Form k n M) := Da q 1

open Classical in

def U (q : Unif k) : Module.End ℂ (Form k n M) :=
  sumOp (fun P => (withKer P.lat).filter fun P₁ => cross q P₁ P = 1) fun _ _ => 1

def Gs (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, χ c • dia c

def GsStar (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, χ (-(c : 𝓀[k])) • dia c⁻¹

def FF (q : Unif k) (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  sumOp (fun P₁ => withLat P₁.ker) fun P₁ P => χ (cross q P₁ P)

def FFStar (q : Unif k) (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  sumOp (fun P => withKer P.lat) fun P P₁ => χ (-cross q P₁ P)

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)

theorem sumOp_apply (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (P : Pair k n) :
    sumOp S w φ P = ∑ Q ∈ S P, w P Q • φ Q := rfl

theorem Nm_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) : Nm φ P = ∑ c : 𝓀[k]ˣ, φ (c • P) := by
  simp only [Nm, LinearMap.sum_apply, Finset.sum_apply, dia_apply]
  congr!

theorem mem_Mram [Fintype 𝓀[k]ˣ] : φ ∈ Mram k n M ↔ ∀ P, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := by
  simp only [Mram, LinearMap.mem_ker, funext_iff, Nm_apply, Pi.zero_apply]

theorem Gs_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) : Gs χ φ P = ∑ c : 𝓀[k]ˣ, χ c • φ (c • P) := by
  simp only [Gs, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, dia_apply]
  congr!

theorem GsStar_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) :
    GsStar χ φ P = ∑ c : 𝓀[k]ˣ, χ (-(c : 𝓀[k])) • φ (c⁻¹ • P) := by
  simp only [GsStar, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, dia_apply]
  congr!

theorem trLat_apply (L : Submodule 𝒪[k] (n → k)) : trLat L φ = ∑ P ∈ withLat L, φ P := by simp [trLat]

theorem trKer_apply (L : Submodule 𝒪[k] (n → k)) : trKer L φ = ∑ P ∈ withKer L, φ P := by simp [trKer]

theorem tr_apply (P : Pair k n) : tr φ P = ∑ Q ∈ withLat P.lat, φ Q := trLat_apply φ _

theorem tr'_apply (P : Pair k n) : tr' φ P = ∑ Q ∈ withKer P.ker, φ Q := trKer_apply φ _

open Classical in

theorem Da_apply (a : 𝓀[k]) (P₁ : Pair k n) :
    Da q a φ P₁ = ∑ P ∈ withLat P₁.ker with cross q P₁ P = a, φ P := by simp [Da, sumOp_apply]

open Classical in

theorem D_apply (P₁ : Pair k n) : D q φ P₁ = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, φ P := Da_apply q φ 1 P₁

open Classical in

theorem U_apply (P : Pair k n) : U q φ P = ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 1, φ P₁ := by
  simp [U, sumOp_apply]

theorem FF_apply (P₁ : Pair k n) : FF q χ φ P₁ = ∑ P ∈ withLat P₁.ker, χ (cross q P₁ P) • φ P := rfl

theorem FFStar_apply (P : Pair k n) : FFStar q χ φ P = ∑ P₁ ∈ withKer P.lat, χ (-cross q P₁ P) • φ P₁ := rfl

section Formulas
variable (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]

theorem FF_up [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (x : {x : Red L // x ≠ 0}) :
    FF q χ φ (up L q x) = ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, χ (f.1 x.1) • φ (ofDual L f) := by
  simp only [FF_apply, up_ker, sum_withLat, cross_up_ofDual]

theorem FFStar_ofDual [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    FFStar q χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L q x) := by
  simp only [FFStar_apply, ofDual_lat, sum_withKer L q, cross_up_ofDual]

end Formulas

def cntIp (φ φ' : Form k n ℂ) : ℂ := ∑ᶠ P, φ P * (starRingEnd ℂ) (φ' P)

def IsAdj (A B : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ φ' : Form k n ℂ, (Function.support φ).Finite → (Function.support φ').Finite → cntIp (A φ) φ' = cntIp φ (B φ')


theorem dia_smul_eq_iff {c : 𝓀[k]ˣ} {P : Pair k n} : c • P = P ↔ c = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := Pair.dia_hasVal.1 (h.symm ▸ P.hasVal_vec : (c • P).HasVal P.vec 1)
  have h2 := this.unique P.hasVal_vec
  simpa using h2

section Equivariance
variable [Fintype n] [DecidableEq n]

theorem sum_withLat_smul {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withLat (g • L), F P = ∑ P ∈ withLat L, F (g • P) :=
  (Finset.sum_equiv (MulAction.toPerm g) (fun P => by simp) fun _ _ => rfl).symm

theorem sum_withKer_smul {A : Type*} [AddCommMonoid A] (g : GL n k) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withKer (g • L), F P = ∑ P ∈ withKer L, F (g • P) :=
  (Finset.sum_equiv (MulAction.toPerm g) (fun P => by simp) fun _ _ => rfl).symm

def transl : Representation ℂ (GL n k) (Form k n M) where
  toFun g := LinearMap.funLeft ℂ M fun P => g⁻¹ • P
  map_one' := by
    ext φ P
    simp
  map_mul' g h := by
    ext φ P
    simp [mul_smul]

@[simp] theorem transl_apply (g : GL n k) (P : Pair k n) : transl g φ P = φ (g⁻¹ • P) := rfl

variable (π : Representation ℂ (GL n k) M)

def EqForm : Submodule ℂ (Form k n M) where
  carrier := {φ | ∀ (g : GL n k) P, φ (g • P) = π g (φ P)}
  add_mem' h h' g P := by simp [h g P, h' g P]
  zero_mem' g P := by simp
  smul_mem' c φ h g P := by simp [h g P]

def levelVec (P₀ : Pair k n) : Submodule ℂ M where
  carrier := {v | ∀ g : GL n k, g • P₀ = P₀ → π g v = v}
  add_mem' h h' g hg := by simp [h g hg, h' g hg]
  zero_mem' g _ := by simp
  smul_mem' c v h g hg := by simp [h g hg]

def formOf (P₀ : Pair k n) (v : levelVec π P₀) : Form k n M := fun P =>
  π (MulAction.exists_smul_eq (GL n k) P₀ P).choose v

theorem formOf_smul (P₀ : Pair k n) (v : levelVec π P₀) (g : GL n k) : formOf π P₀ v (g • P₀) = π g v := by
  have h := (MulAction.exists_smul_eq (GL n k) P₀ (g • P₀)).choose_spec
  rw [formOf]
  generalize (MulAction.exists_smul_eq (GL n k) P₀ (g • P₀)).choose = g' at h
  have := v.2 (g⁻¹ * g') (by rw [mul_smul, h, inv_smul_smul])
  rw [← mul_inv_cancel_left g g', map_mul, Module.End.mul_apply, this]

theorem formOf_mem (P₀ : Pair k n) (v : levelVec π P₀) : formOf π P₀ v ∈ EqForm π := fun g P => by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P₀ P
  rw [smul_smul, formOf_smul, formOf_smul, map_mul, Module.End.mul_apply]

def evalEquiv (P₀ : Pair k n) : EqForm π ≃ₗ[ℂ] levelVec π P₀ where
  toFun φ := ⟨φ.1 P₀, fun g hg => by rw [← φ.2 g P₀, hg]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨formOf π P₀ v, formOf_mem π P₀ v⟩
  left_inv φ := Subtype.ext (funext fun P => by
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P₀ P
    exact (formOf_smul π P₀ _ h).trans (φ.2 h P₀).symm)
  right_inv v := Subtype.ext (by simpa using formOf_smul π P₀ v 1)

theorem map_mem_EqForm {T : Module.End ℂ (Form k n M)}
    (h1 : ∀ (g : GL n k) φ P, T φ (g • P) = T (fun Q => φ (g • Q)) P)
    (h2 : ∀ (g : GL n k) (φ : Form k n M) P, T (fun Q => π g (φ Q)) P = π g (T φ P))
    {φ : Form k n M} (h : φ ∈ EqForm π) : T φ ∈ EqForm π := fun g P => by
  rw [h1, ← h2]
  exact congrArg (T · P) (funext (h g))

variable (g : GL n k) (P : Pair k n)

theorem dia_smul (c : 𝓀[k]ˣ) : dia c φ (g • P) = dia c (fun Q => φ (g • Q)) P := by
  simp only [dia_apply, smul_comm g c]

theorem U_smul : U q φ (g • P) = U q (fun Q => φ (g • Q)) P := by
  classical
  simp only [U_apply, Finset.sum_filter, Pair.smul_lat, sum_withKer_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withKer.1 hQ).symm]

theorem FF_smul : FF q χ φ (g • P) = FF q χ (fun Q => φ (g • Q)) P := by
  simp only [FF_apply, Pair.smul_ker, sum_withLat_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withLat.1 hQ)]

theorem FFStar_smul : FFStar q χ φ (g • P) = FFStar q χ (fun Q => φ (g • Q)) P := by
  simp only [FFStar_apply, Pair.smul_lat, sum_withKer_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withKer.1 hQ).symm]

variable {π φ}

theorem dia_mem_EqForm (c : 𝓀[k]ˣ) (h : φ ∈ EqForm π) : dia c φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => dia_smul φ g P c) (fun _ _ _ => rfl) h

theorem U_mem_EqForm (h : φ ∈ EqForm π) : U q φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => U_smul q φ g P) (fun _ _ _ => by simp [U_apply]) h

theorem FF_mem_EqForm (h : φ ∈ EqForm π) : FF q χ φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => FF_smul q χ φ g P) (fun _ _ _ => by simp [FF_apply]) h

theorem FFStar_mem_EqForm (h : φ ∈ EqForm π) : FFStar q χ φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => FFStar_smul q χ φ g P) (fun _ _ _ => by simp [FFStar_apply]) h

end Equivariance
end Forms

section Character
open SplitWeil

theorem apply_int_eq_one {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (x : 𝒪[k]) : ψ x = 1 :=
  (hψ x).2 (by simpa using (Valuation.mem_integer_iff _ _).1 x.2) x le_rfl

theorem apply_inv_mul_congr {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) {s t : 𝒪[k]}
    (h : residue 𝒪[k] s = residue 𝒪[k] t) : ψ (q.inv * s) = ψ (q.inv * t) := by
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, h, sub_self]))
  have : q.inv * s = q.inv * t + u := by
    have hu' : (s : k) = t + q.1 * u := by exact_mod_cast congrArg Subtype.val (sub_eq_iff_eq_add'.1 hu)
    rw [hu', mul_add, Unif.inv, inv_mul_cancel_left₀ q.ne_zero]
  rw [this, AddChar.map_add_eq_mul, apply_int_eq_one hψ, mul_one]

def resChar (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (q : Unif k) : AddChar 𝓀[k] ℂ where
  toFun a := ψ (q.inv * ((residue_surjective (R := 𝒪[k]) a).choose : 𝒪[k]))
  map_zero_eq_one' := by
    rw [apply_inv_mul_congr hψ q (t := 0) (by rw [(residue_surjective (R := 𝒪[k]) 0).choose_spec, map_zero])]
    simp
  map_add_eq_mul' a b := by
    rw [apply_inv_mul_congr hψ q
      (t := (residue_surjective (R := 𝒪[k]) a).choose + (residue_surjective (R := 𝒪[k]) b).choose)
      (by rw [map_add, (residue_surjective (R := 𝒪[k]) _).choose_spec, (residue_surjective (R := 𝒪[k]) _).choose_spec,
        (residue_surjective (R := 𝒪[k]) _).choose_spec])]
    simp [mul_add, AddChar.map_add_eq_mul]

theorem resChar_residue {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (s : 𝒪[k]) :
    resChar ψ hψ q (residue 𝒪[k] s) = ψ (q.inv * s) :=
  congrArg (fun z : Circle => (z : ℂ)) (apply_inv_mul_congr hψ q (residue_surjective (R := 𝒪[k]) _).choose_spec)

theorem conj_resChar {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) (a : 𝓀[k]) :
    (starRingEnd ℂ) (resChar ψ hψ q a) = resChar ψ hψ q (-a) := by
  obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
  rw [← map_neg, resChar_residue, resChar_residue, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
  simp

theorem resChar_ne_one {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) : resChar ψ hψ q ≠ 1 := by
  intro h
  have h0 : valuation k (q.1 : k) ≠ 0 := (Valuation.ne_zero_iff _).2 q.ne_zero
  have h1 : valuation k q.inv ≤ valuation k ((1 : kˣ) : k) := (hψ q.inv).1 fun y hy => by
    have hy' : (q.1 : k) * y ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_mul]
      rw [Unif.inv, map_inv₀] at hy
      exact (mul_le_mul_right hy _).trans_eq (mul_inv_cancel₀ h0)
    have := resChar_residue hψ q ⟨_, hy'⟩
    rw [h, AddChar.one_apply, Unif.inv, inv_mul_cancel_left₀ q.ne_zero] at this
    exact Circle.ext this.symm
  have h2 : q.inv ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by simpa using h1)
  exact q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero)))

theorem hasConductor_mulShift {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (u : 𝒪[k]ˣ) :
    HasConductor (ψ.mulShift ((u : 𝒪[k]) : k)) 1 := fun x => by
  have hv : ∀ w : 𝒪[k]ˣ, ∀ y : k, valuation k (((w : 𝒪[k]) : k) * y) ≤ valuation k y := fun w y => by
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (w : 𝒪[k]).2)
  rw [← hψ x]
  refine ⟨fun h y hy => ?_, fun h y hy => h _ ((hv u y).trans hy)⟩
  have := h _ ((hv u⁻¹ y).trans hy)
  rwa [AddChar.mulShift_apply, ← mul_assoc, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, one_mul] at this

end Character

section Kernel
variable [Fintype n']

open Classical in

def latInd (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) (x : Matrix n n' k) : ℂ :=
  if ∀ y ∈ S, x *ᵥ y ∈ L then 1 else 0

def Maps (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) : Prop :=
  ∃ h : ∀ y ∈ P.lat, x *ᵥ y ∈ Q.lat, ∀ y : P.lat, Q.fn ⟨x *ᵥ y, h y y.2⟩ = P.fn y

open Classical in

def phiOne (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) : ℂ := if Maps P Q x then 1 else 0

variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}

theorem maps_iff_hasVal : Maps P Q x ↔ ∀ y a, P.HasVal y a → Q.HasVal (x *ᵥ y) a :=
  ⟨fun ⟨h, h'⟩ y _ ⟨hy, ha⟩ => ⟨h y hy, ha ▸ h' ⟨y, hy⟩⟩,
    fun h => ⟨fun y hy => (h y _ (P.hasVal_fn ⟨y, hy⟩)).mem, fun y => (h y _ (P.hasVal_fn y)).2⟩⟩

theorem maps_iff_glue {e : n' → k} {e' : n → k} (he : P.HasVal e 1) (he' : Q.HasVal e' 1) :
    Maps P Q x ↔ (∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker) ∧ x *ᵥ e - e' ∈ Q.ker := by
  rw [maps_iff_hasVal, ← Pair.hasVal_one_iff he']
  refine ⟨fun h => ⟨fun y hy => Pair.mem_ker.2 (h _ _ (Pair.mem_ker.1 hy)), h _ _ he⟩, fun h y a hy => ?_⟩
  obtain ⟨s, rfl, hs⟩ := (Pair.hasVal_iff he).1 hy
  refine (Pair.hasVal_iff h.2).2 ⟨s, rfl, ?_⟩
  simpa only [mulVec_sub, mulVec_smul] using h.1 _ hs

theorem maps_dia (c : 𝓀[k]ˣ) : Maps (c • P) (c • Q) x ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal]
  exact ⟨fun h y a => by simpa using h y (c * a), fun h y a => h y _⟩

theorem phiOne_dia (c : 𝓀[k]ˣ) : phiOne (c • P) (c • Q) = phiOne P Q := by
  ext x
  classical
  exact if_congr (maps_dia c) rfl rfl

variable [DecidableEq n'] [Fintype n] [DecidableEq n]

theorem maps_smul (g : GL n' k) (h : GL n k) : Maps (g • P) (h • Q) x ↔ Maps P Q ((h⁻¹ : GL n k).val * x * g.val) := by
  simp only [maps_iff_hasVal, Pair.smul_hasVal, ← mulVec_mulVec]
  refine ⟨fun H y a hy => H (g • y) a (by simpa using hy), fun H y a hy => ?_⟩
  have := H _ a hy
  rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this

theorem phiOne_smul (g : GL n' k) (h : GL n k) :
    phiOne (g • P) (h • Q) x = phiOne P Q ((h⁻¹ : GL n k).val * x * g.val) := by
  classical
  exact if_congr (maps_smul g h) rfl rfl

theorem latInd_smul (g : GL n' k) (h : GL n k) (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) :
    latInd (g • S) (h • L) x = latInd S L ((h⁻¹ : GL n k).val * x * g.val) := by
  have : (∀ y ∈ g • S, x *ᵥ y ∈ h • L) ↔ ∀ y ∈ S, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y ∈ L := by
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  classical
  exact if_congr this rfl rfl

end Kernel

section Glued
variable {c : ℕ}

variable (k n) in

def inX (c : ℕ) : (n → k) →ₗ[𝒪[k]] (n ⊕ Fin c → k) where
  toFun x := Sum.elim x 0
  map_add' x y := by ext (i | i) <;> simp
  map_smul' s x := by ext (i | i) <;> simp

variable (k n) in

def avec (c p : ℕ) : n ⊕ Fin c → k := Sum.elim 0 fun i => if i.val + 1 = p then 1 else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem sum_smul_avec (z : Fin c → k) : ∑ i : Fin c, z i • avec k n c (i.val + 1) = Sum.elim (0 : n → k) z := by
  ext (j | j) <;> simp [avec, Fin.val_inj]

def gluedLat (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {q.inv • avec k n c p + inX k n c f} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, 1 ≤ i ∧ i < p ∧ i ≤ c ∧ y = avec k n c i} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, p < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}

def gluedS (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {q.inv • avec k n c 1 + inX k n c f} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, 2 ≤ i ∧ i ≤ c ∧ y = q.inv • avec k n c i}

theorem gluedLat_one (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    gluedLat q c 1 L f = gluedS q c L f := by
  have : {y | ∃ i, 1 ≤ i ∧ i < 1 ∧ i ≤ c ∧ y = avec k n c i} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, h1, h2, -⟩
    omega
  rw [gluedLat, this, Submodule.span_empty, sup_bot_eq]
  rfl

theorem mem_gluedLat {q : Unif k} {p : ℕ} {L : Submodule 𝒪[k] (n → k)} {f : n → k} {y : n ⊕ Fin c → k} :
    y ∈ gluedLat q c p L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val + 1 < p → y (Sum.inr i) ∈ 𝒪[k]) ∧ (i.val + 1 = p → y (Sum.inr i) = q.inv * s) ∧
        (p < i.val + 1 → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by
  let T : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
    { carrier := {y | ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
        (i.val + 1 < p → y (Sum.inr i) ∈ 𝒪[k]) ∧ (i.val + 1 = p → y (Sum.inr i) = q.inv * s) ∧
          (p < i.val + 1 → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k])}
      zero_mem' := ⟨0, by simp, fun i => by simp⟩
      add_mem' := by
        rintro y z ⟨s, hs, h⟩ ⟨t, ht, h'⟩
        refine ⟨s + t, ?_, fun i => ⟨fun hi => add_mem ((h i).1 hi) ((h' i).1 hi), fun hi => ?_, fun hi => ?_⟩⟩
        · convert add_mem hs ht using 1
          rw [Pi.add_comp, add_smul]
          abel
        · simp [(h i).2.1 hi, (h' i).2.1 hi, mul_add]
        · simpa [mul_add] using add_mem ((h i).2.2 hi) ((h' i).2.2 hi)
      smul_mem' := by
        rintro t y ⟨s, hs, h⟩
        refine ⟨t * s, ?_, fun i => ⟨fun hi => mul_mem t.2 ((h i).1 hi), fun hi => ?_, fun hi => ?_⟩⟩
        · convert L.smul_mem t hs using 1
          rw [smul_sub, mul_smul]
          rfl
        · change (t : k) * y _ = _
          simp [(h i).2.1 hi, mul_left_comm]
        · change (q.1 : k) * ((t : k) * y _) ∈ _
          rw [mul_left_comm]
          exact mul_mem t.2 ((h i).2.2 hi) }
  have hq : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  constructor
  · refine fun hy => (?_ : gluedLat q c p L f ≤ T) hy
    refine sup_le (sup_le (sup_le ?_ (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩
    · rintro _ rfl
      refine ⟨1, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · convert L.zero_mem
        ext j
        simp [inX, avec]
      · simp [inX, avec, hi.ne]
      · simp [inX, avec, hi]
      · simp [inX, avec, hi.ne']
    · rintro _ ⟨j, -, hj, -, rfl⟩
      refine ⟨0, by simp [avec], fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · simp only [avec, Sum.elim_inr]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · simp [avec, show i.val + 1 ≠ j by omega]
    · rintro _ ⟨j, hj, -, rfl⟩
      refine ⟨0, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · convert L.zero_mem
        ext j
        simp [avec]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · by_cases h : i.val + 1 = j <;> simp [avec, h, hq]
  · rintro ⟨s, hs, h⟩
    have hy : y = inX k n c (y ∘ Sum.inl - s • f) + s • (q.inv • avec k n c p + inX k n c f) +
        ∑ i : Fin c, (if i.val + 1 = p then 0 else y (Sum.inr i)) • avec k n c (i.val + 1) := by
      rw [sum_smul_avec]
      ext (j | j)
      · simp [inX, avec]
      · have hs' : ∀ z : k, s • z = (s : k) * z := fun _ => rfl
        by_cases hj : j.val + 1 = p
        · simp [inX, avec, Fin.val_inj, hj, (h j).2.1 hj, hs', mul_comm]
        · simp [inX, avec, Fin.val_inj, hj]
    rw [hy]
    refine add_mem (add_mem ?_ ?_) (sum_mem fun i _ => ?_)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, hs, rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))
    · rcases lt_trichotomy (i.val + 1) p with hi | hi | hi
      · rw [if_neg hi.ne]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ (⟨_, (h i).1 hi⟩ : 𝒪[k])
          (Submodule.subset_span ⟨_, by omega, hi, i.2, rfl⟩)))
      · simp [hi]
      · rw [if_neg hi.ne']
        have := Submodule.smul_mem _ (⟨_, (h i).2.2 hi⟩ : 𝒪[k]) (Submodule.subset_span (R := 𝒪[k])
          (s := {y | ∃ i, p < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}) ⟨_, hi, i.2, rfl⟩)
        refine Submodule.mem_sup_right ?_
        convert this using 1
        change _ = ((q.1 : k) * y (Sum.inr i)) • q.inv • avec k n c (i.val + 1)
        rw [smul_smul, mul_right_comm, hq, one_mul]

theorem gluedLat_congr (q : Unif k) (c p : ℕ) {L : Submodule 𝒪[k] (n → k)} {f f' : n → k} (h : f - f' ∈ L) :
    gluedLat q c p L f = gluedLat q c p L f' := by
  ext y
  simp only [mem_gluedLat]
  refine exists_congr fun s => and_congr_left' ?_
  rw [← L.add_mem_iff_left (L.smul_mem s h), smul_sub, sub_add_sub_cancel]

theorem inX_mem_gluedLat {q : Unif k} {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) {L : Submodule 𝒪[k] (n → k)} {f x : n → k} :
    inX k n c x ∈ gluedLat q c p L f ↔ x ∈ L := by
  rw [mem_gluedLat]
  constructor
  · rintro ⟨s, hs, h⟩
    have h0 := (h ⟨p - 1, by omega⟩).2.1 (by simp; omega)
    have : s = 0 := by simpa [inX, Unif.inv, q.ne_zero] using h0
    simpa [this, inX] using hs
  · exact fun hx => ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩

instance gluedLat_isLattice (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k] (f : n → k) :
    (gluedLat q c p L f).IsLattice k := by
  refine ⟨(((hL.fg.map _).sup (Submodule.fg_span_singleton _)).sup (Submodule.fg_span ?_)).sup
    (Submodule.fg_span ?_), ?_⟩
  · exact ((Set.finite_le_nat c).image (avec k n c)).subset fun _ ⟨i, _, _, h, e⟩ => ⟨i, h, e.symm⟩
  · exact ((Set.finite_le_nat c).image (q.inv • avec k n c ·)).subset fun _ ⟨i, _, h, e⟩ => ⟨i, h, e.symm⟩
  · set W := Submodule.span k (gluedLat q c p L f : Set (n ⊕ Fin c → k))
    have hX : ∀ x, inX k n c x ∈ W := fun x => by
      have hx : x ∈ Submodule.span k (L : Set (n → k)) := hL.span_eq_top ▸ trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Submodule.subset_span (mem_gluedLat.2 ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx =>
        convert W.smul_mem a hx using 1
        ext (i | i) <;> simp [inX]
    have hA : ∀ i : Fin c, avec k n c (i.val + 1) ∈ W := fun i => by
      by_cases hi : i.val + 1 = p
      · have h1 : q.inv • avec k n c p + inX k n c f ∈ W := Submodule.subset_span (Submodule.mem_sup_left
          (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
        have h2 := W.smul_mem (q.1 : k) ((W.add_mem_iff_left (hX f)).1 h1)
        rwa [smul_smul, Unif.inv, mul_inv_cancel₀ q.ne_zero, one_smul, ← hi] at h2
      · refine Submodule.subset_span (mem_gluedLat.2 ⟨0, by simp [avec], fun j => ⟨fun _ => ?_, fun hj => ?_, fun _ => ?_⟩⟩)
        · by_cases h : j = i <;> simp [avec, Fin.val_inj, h]
        · simp [avec, show j.val ≠ i.val by omega]
        · by_cases h : j = i <;> simp [avec, Fin.val_inj, h]
    refine eq_top_iff.2 fun y _ => ?_
    have hy : y = inX k n c (y ∘ Sum.inl) + ∑ i : Fin c, y (Sum.inr i) • avec k n c (i.val + 1) := by
      ext (j | j) <;> simp [inX, avec, Fin.val_inj]
    rw [hy]
    exact add_mem (hX _) (sum_mem fun i _ => W.smul_mem _ (hA i))

instance gluedS_isLattice (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (f : n → k) :
    (gluedS q c L f).IsLattice k := gluedLat_one q c L f ▸ inferInstance

def Pair.glued (P : Pair k n) (q : Unif k) (c p : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) := gluedLat q c p P.ker P.vec

instance (P : Pair k n) (q : Unif k) (c p : ℕ) : (P.glued q c p).IsLattice k := gluedLat_isLattice _ _ _ _ _

variable [Fintype n] [DecidableEq n]

theorem embX_smul_gluedLat (g : GL n k) (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.embX c g • gluedLat q c p L f = gluedLat q c p (g • L) (g • f) := by
  ext y
  have h : (RootEx.embX c g)⁻¹ • y = Sum.elim (g⁻¹ • (y ∘ Sum.inl)) (y ∘ Sum.inr) := by
    rw [← map_inv]
    change fromBlocks (g⁻¹ : GL n k).val 0 0 1 *ᵥ y = _
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, one_mulVec, add_zero, zero_add]
    rfl
  simp only [mem_smul_iff, h, mem_gluedLat, Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply, smul_sub,
    smul_comm g⁻¹, inv_smul_smul]

end Glued

section Spherical
variable [Fintype n] [DecidableEq n]

theorem exists_smul_lat (L L' : Submodule 𝒪[k] (n → k)) [L.IsLattice k] [L'.IsLattice k] :
    ∃ g : GL n k, g • L = L' := by
  let e : L ≃ₗ[𝒪[k]] L' := LinearEquiv.ofFinrankEq _ _ (by
    rw [Submodule.IsLattice.finrank_of_pi k, Submodule.IsLattice.finrank_of_pi k])
  obtain ⟨g, hg⟩ := exists_gl_of_equiv e
  refine ⟨g, Submodule.ext fun x => mem_smul_iff.trans ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← smul_inv_smul g x, hg ⟨_, h⟩]
    exact (e _).2
  · obtain ⟨y, hy⟩ := e.surjective ⟨x, h⟩
    have hx : x = g • (y : n → k) := by rw [hg, hy]
    rw [hx, inv_smul_smul]
    exact y.2

variable {A : Type*} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL n k) A)

def sphVecs (L₀ : Submodule 𝒪[k] (n → k)) : Submodule ℂ A where
  carrier := {v | ∀ g ∈ latStab L₀, σ g v = v}
  add_mem' h h' g hg := by simp [h g hg, h' g hg]
  zero_mem' g _ := by simp
  smul_mem' c v h g hg := by simp [h g hg]

def vecAt {L₀ : Submodule 𝒪[k] (n → k)} [L₀.IsLattice k] (v : sphVecs σ L₀) (L : Submodule 𝒪[k] (n → k))
    [L.IsLattice k] : A := σ (exists_smul_lat L₀ L).choose v

variable {L₀ : Submodule 𝒪[k] (n → k)} [L₀.IsLattice k] (v : sphVecs σ L₀)

end Spherical

section Examples

example [Fintype n] [DecidableEq n] (P : Pair k n) : phiOne P P 1 = 1 :=
  if_pos (maps_iff_hasVal.2 fun y a h => by simpa using h)

example [Fintype n'] (P : Pair k n') (Q : Pair k n) : phiOne P Q 0 = 0 :=
  if_neg fun h => by
    have h1 := maps_iff_hasVal.1 h _ _ P.hasVal_vec
    rw [zero_mulVec] at h1
    exact one_ne_zero (h1.unique (Pair.mem_ker.1 (zero_mem _)))

example [Fintype n] (i : n) (x : n → k) :
    x ∈ (stdPair k i).ker ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], (⟨x i, h i⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
  simp only [Pair.mem_ker, stdPair_hasVal, residue_eq_zero_iff]

theorem scalar_smul_eq [Fintype n] [DecidableEq n] (g : GL n k) (s : 𝒪[k]ˣ) (hg : ∀ x : n → k, g • x = (s : 𝒪[k]) • x)
    (P : Pair k n) : g • P = (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ • P := by
  refine Pair.ext fun x a => ?_
  obtain ⟨y, rfl⟩ : ∃ y, x = g • y := ⟨g⁻¹ • x, (smul_inv_smul g x).symm⟩
  rw [Pair.smul_hasVal, inv_smul_smul, Pair.dia_hasVal, inv_inv, hg]
  refine ⟨fun h => h.smul _, fun h => ?_⟩
  have := h.smul (s⁻¹ : 𝒪[k]ˣ)
  rw [smul_smul, Units.inv_mul, one_smul] at this
  convert this using 1
  change a = _ * (residue 𝒪[k] s * a)
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]


example (P : Pair k n) (q : Unif k) (x : n → k) : inX k n 0 x ∈ P.glued q 0 1 ↔ x ∈ P.lat := by
  rw [Pair.glued, mem_gluedLat, Pair.mem_lat_iff]
  simp [inX, Pair.hasVal_iff P.hasVal_vec]

example (r : ℕ) : Nonempty (GluePair k (Fin (r + 1))) := ⟨(stdPair k 0).toGlue⟩

end Examples

end GlobalTheory.LatPair
end
end
