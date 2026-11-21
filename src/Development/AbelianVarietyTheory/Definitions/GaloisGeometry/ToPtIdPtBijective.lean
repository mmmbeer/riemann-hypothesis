import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

section
set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u v' u' v'' u''

section Complex

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def OmF (q : ℕ) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (Om R (F.obj T) q)
  map φ := ModuleCat.ofHom (pOm F q φ)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_id F x)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_comp F φ ψ x)

def dOmNat (q : ℕ) : OmF F q ⟶ OmF F (q + 1) where
  app T := ModuleCat.ofHom (dOm R (F.obj T) q)
  naturality _ _ φ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ (pOm_dOm F φ x).symm)

abbrev Term (a q : ℕ) : Type (max u v) := CatH.Cn (OmF F q) a

abbrev dH (a q : ℕ) : Term F a q →ₗ[R] Term F (a + 1) q := CatH.d (OmF F q) a

def dV (a q : ℕ) : Term F a q →ₗ[R] Term F a (q + 1) :=
  (CatH.Mor.ofNatTrans (dOmNat F q)).pullC a

theorem dV_apply {a q : ℕ} (c : Term F a q) (s : ComposableArrows C a) :
    dV F a q c s = dOm R (F.obj (s.obj (Fin.last a))) q (c s) := rfl

abbrev Bidegree (n : ℕ) : Type := {p : ℕ × ℕ // p.1 + p.2 = n}

abbrev Tot (n : ℕ) : Type (max u v) := ∀ p : Bidegree n, Term F p.1.1 p.1.2

def totH (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, q), h⟩ => dH F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n)

def totV (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, q + 1), h⟩ => (-1 : ℤ) ^ a • (dV F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n))

def dTot (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) := totH F n + totV F n

section
variable {F} {n : ℕ} (c : Tot F n)

@[simp] theorem totH_zero {q : ℕ} (h : 0 + q = n + 1) : totH F n c ⟨(0, q), h⟩ = 0 := rfl

@[simp] theorem totH_succ {a q : ℕ} (h : a + 1 + q = n + 1) :
    totH F n c ⟨(a + 1, q), h⟩ = dH F a q (c ⟨(a, q), by omega⟩) := rfl

@[simp] theorem totV_zero {a : ℕ} (h : a + 0 = n + 1) : totV F n c ⟨(a, 0), h⟩ = 0 := rfl

@[simp] theorem totV_succ {a q : ℕ} (h : a + (q + 1) = n + 1) :
    totV F n c ⟨(a, q + 1), h⟩ = (-1 : ℤ) ^ a • dV F a q (c ⟨(a, q), by omega⟩) := rfl

theorem dTot_apply (p : Bidegree (n + 1)) : dTot F n c p = totH F n c p + totV F n c p := rfl

end

def ZTot (n : ℕ) : Submodule R (Tot F n) := LinearMap.ker (dTot F n)

def BTot : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dTot F n)

def Hyp (n : ℕ) : Type (max u v) := ZTot F n ⧸ (BTot F n).submoduleOf (ZTot F n)

instance (n : ℕ) : AddCommGroup (Hyp F n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (n : ℕ) : Module R (Hyp F n) := inferInstanceAs (Module R (_ ⧸ _))

def Hyp.mk (n : ℕ) : ZTot F n →ₗ[R] Hyp F n := Submodule.mkQ _

theorem Hyp.mk_surjective (n : ℕ) : Function.Surjective (Hyp.mk F n) := Submodule.mkQ_surjective _

variable {F} in

theorem Hyp.mk_eq_zero {n : ℕ} {c : ZTot F n} : Hyp.mk F n c = 0 ↔ c.1 ∈ BTot F n :=
  Submodule.Quotient.mk_eq_zero _

def TotF (p n : ℕ) : Submodule R (Tot F n) where
  carrier := {c | ∀ b : Bidegree n, b.1.2 < p → c b = 0}
  add_mem' hc hc' b hb := by rw [Pi.add_apply, hc b hb, hc' b hb, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r c hc b hb := by rw [Pi.smul_apply, hc b hb, smul_zero]

theorem TotF_anti {p p' : ℕ} (h : p ≤ p') (n : ℕ) : TotF F p' n ≤ TotF F p n :=
  fun _ hc b hb ↦ hc b (hb.trans_le h)

theorem TotF_zero (n : ℕ) : TotF F 0 n = ⊤ :=
  eq_top_iff.2 fun _ _ _ hb ↦ absurd hb (Nat.not_lt_zero _)

theorem TotF_eq_bot {p n : ℕ} (h : n < p) : TotF F p n = ⊥ :=
  eq_bot_iff.2 fun _ hc ↦ funext fun b ↦ hc b (by have := b.2; omega)

def ZF (p n : ℕ) : Submodule R (Tot F n) := TotF F p n ⊓ ZTot F n

def BF (p : ℕ) : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => (TotF F p n).map (dTot F n)

theorem BF_le_BTot (p : ℕ) : ∀ n : ℕ, BF F p n ≤ BTot F n
  | 0 => le_rfl
  | _ + 1 => LinearMap.map_le_range

theorem BF_anti {p p' : ℕ} (h : p ≤ p') : ∀ n : ℕ, BF F p' n ≤ BF F p n
  | 0 => le_rfl
  | n + 1 => Submodule.map_mono (TotF_anti F h n)

def HypF (p n : ℕ) : Type (max u v) := ZF F p n ⧸ (BF F p n).submoduleOf (ZF F p n)

instance (p n : ℕ) : AddCommGroup (HypF F p n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (p n : ℕ) : Module R (HypF F p n) := inferInstanceAs (Module R (_ ⧸ _))

def HypF.mk (p n : ℕ) : ZF F p n →ₗ[R] HypF F p n := Submodule.mkQ _

theorem HypF.mk_surjective (p n : ℕ) : Function.Surjective (HypF.mk F p n) :=
  Submodule.mkQ_surjective _

variable {F} in

theorem HypF.mk_eq_zero {p n : ℕ} {c : ZF F p n} : HypF.mk F p n c = 0 ↔ c.1 ∈ BF F p n :=
  Submodule.Quotient.mk_eq_zero _

def HypF.toHyp (p n : ℕ) : HypF F p n →ₗ[R] Hyp F n :=
  Submodule.mapQ _ _ (Submodule.inclusion inf_le_right) fun _ hc ↦ BF_le_BTot F p n hc

def HypF.incl {p p' : ℕ} (h : p ≤ p') (n : ℕ) : HypF F p' n →ₗ[R] HypF F p n :=
  Submodule.mapQ _ _ (Submodule.inclusion (inf_le_inf_right _ (TotF_anti F h n)))
    fun _ hc ↦ BF_anti F h n hc

def Hyp.fil (p n : ℕ) : Submodule R (Hyp F n) := LinearMap.range (HypF.toHyp F p n)

variable {F} in

theorem Hyp.mem_fil {p n : ℕ} {x : Hyp F n} :
    x ∈ Hyp.fil F p n ↔ ∃ c : ZTot F n, c.1 ∈ TotF F p n ∧ Hyp.mk F n c = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n y
    exact ⟨⟨c.1, c.2.2⟩, c.2.1, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨HypF.mk F p n ⟨c.1, hc, c.2⟩, rfl⟩

theorem Hyp.fil_zero (n : ℕ) : Hyp.fil F 0 n = ⊤ := eq_top_iff.2 fun x _ ↦ by
  obtain ⟨c, rfl⟩ := Hyp.mk_surjective F n x
  exact Hyp.mem_fil.2 ⟨c, by rw [TotF_zero]; trivial, rfl⟩

theorem Hyp.fil_eq_bot {p n : ℕ} (h : n < p) : Hyp.fil F p n = ⊥ := eq_bot_iff.2 fun x hx ↦ by
  obtain ⟨c, hc, rfl⟩ := Hyp.mem_fil.1 hx
  rw [TotF_eq_bot F h] at hc
  rw [show c = 0 from Subtype.ext hc, map_zero]; rfl

theorem dH_lead {a p n : ℕ} (h : a + p = n) (c : ZF F p n) : dH F a p (c.1 ⟨(a, p), h⟩) = 0 := by
  have e := congrFun (show dTot F n c.1 = 0 from c.2.2) ⟨(a + 1, p), by omega⟩
  have hV : totV F n c.1 ⟨(a + 1, p), by omega⟩ = 0 := by
    rcases p with _ | p
    · rfl
    · rw [totV_succ, c.2.1 _ (Nat.lt_succ_self p), map_zero, smul_zero]
  rwa [dTot_apply, hV, add_zero] at e

def leadZ {a p n : ℕ} (h : a + p = n) : ZF F p n →ₗ[R] LinearMap.ker (CatH.d (OmF F p) a) :=
  ((LinearMap.proj (⟨(a, p), h⟩ : Bidegree n)) ∘ₗ (ZF F p n).subtype).codRestrict _ (dH_lead F h)

end Complex

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

def omMor (q : ℕ) : CatH.Mor (OmF F q) (OmF F' q) σ where
  G := m.G
  τ T := qOm m q T
  nat φ x := qOm_pOm m φ x

abbrev pullTerm (a q : ℕ) : Term F a q →ₛₗ[σ] Term F' a q := (omMor m q).pullC a

theorem dH_pullTerm {a q : ℕ} (c : Term F a q) :
    dH F' a q (pullTerm m a q c) = pullTerm m (a + 1) q (dH F a q c) := (omMor m q).d_pullC a c

theorem dV_pullTerm {a q : ℕ} (c : Term F a q) :
    dV F' a q (pullTerm m a q c) = pullTerm m a (q + 1) (dV F a q c) :=
  funext fun s ↦ ((semiHom_coef m _).mOm_dOm (c (s ⋙ m.G))).symm

def pullTot (n : ℕ) : Tot F n →ₛₗ[σ] Tot F' n where
  toFun c b := pullTerm m _ _ (c b)
  map_add' c c' := funext fun b ↦ map_add _ (c b) (c' b)
  map_smul' r c := funext fun b ↦ map_smulₛₗ (pullTerm m _ _) r (c b)

theorem pullTot_apply {n : ℕ} (c : Tot F n) (b : Bidegree n) :
    pullTot m n c b = pullTerm m _ _ (c b) := rfl

theorem dTot_pullTot {n : ℕ} (c : Tot F n) :
    dTot F' n (pullTot m n c) = pullTot m (n + 1) (dTot F n c) := by
  funext ⟨(a, q), h⟩
  rw [pullTot_apply, dTot_apply, dTot_apply, map_add]
  congr 1
  · rcases a with _ | a
    · exact (map_zero _).symm
    · exact dH_pullTerm m _
  · rcases q with _ | q
    · exact (map_zero _).symm
    · rw [totV_succ, totV_succ, map_zsmul, pullTot_apply, dV_pullTerm]

theorem pullTot_mem_ZTot {n : ℕ} {c : Tot F n} (hc : c ∈ ZTot F n) : pullTot m n c ∈ ZTot F' n := by
  change dTot F' n _ = 0
  rw [dTot_pullTot, show dTot F n c = 0 from hc, map_zero]

theorem pullTot_mem_TotF {p n : ℕ} {c : Tot F n} (hc : c ∈ TotF F p n) :
    pullTot m n c ∈ TotF F' p n := fun b hb ↦ by rw [pullTot_apply, hc b hb, map_zero]

theorem pullTot_mem_BTot : ∀ {n : ℕ} {c : Tot F n}, c ∈ BTot F n → pullTot m n c ∈ BTot F' n
  | 0, c, hc => by rw [show c = 0 from hc, map_zero]; exact zero_mem _
  | _ + 1, _, ⟨e, he⟩ => ⟨_, (dTot_pullTot m e).trans (congrArg _ he)⟩

theorem pullTot_mem_BF {p : ℕ} : ∀ {n : ℕ} {c : Tot F n}, c ∈ BF F p n → pullTot m n c ∈ BF F' p n
  | 0, c, hc => by rw [show c = 0 from hc, map_zero]; exact zero_mem _
  | _ + 1, _, ⟨e, h, he⟩ => ⟨_, pullTot_mem_TotF m h, (dTot_pullTot m e).trans (congrArg _ he)⟩

def pullZ (n : ℕ) : ZTot F n →ₛₗ[σ] ZTot F' n :=
  ((pullTot m n).domRestrict _).codRestrict _ fun c ↦ pullTot_mem_ZTot m c.2

def pullZF (p n : ℕ) : ZF F p n →ₛₗ[σ] ZF F' p n :=
  ((pullTot m n).domRestrict _).codRestrict _ fun c ↦
    ⟨pullTot_mem_TotF m c.2.1, pullTot_mem_ZTot m c.2.2⟩

def Hyp.pull (n : ℕ) : Hyp F n →ₛₗ[σ] Hyp F' n :=
  Submodule.mapQ _ _ (pullZ m n) fun _ hc ↦ pullTot_mem_BTot m hc

def HypF.pull (p n : ℕ) : HypF F p n →ₛₗ[σ] HypF F' p n :=
  Submodule.mapQ _ _ (pullZF m p n) fun _ hc ↦ pullTot_mem_BF m hc



theorem pullTot_comp (m' : CoefMap τ F' F'') {n : ℕ} (c : Tot F n) :
    pullTot (m.comp m') n c = pullTot m' n (pullTot m n c) :=
  funext fun b ↦ funext fun s ↦
    (SemiHom.mOm_mOm (semiHom_coef m _) (semiHom_coef m' _) _ (fun _ ↦ rfl)
      (c b (s ⋙ m'.G ⋙ m.G))).symm

theorem Hyp.pull_comp (m' : CoefMap τ F' F'') {n : ℕ} (x : Hyp F n) :
    Hyp.pull (m.comp m') n x = Hyp.pull m' n (Hyp.pull m n x) := by
  obtain ⟨c, rfl⟩ := Hyp.mk_surjective F n x
  exact congrArg (Hyp.mk F'' n) (Subtype.ext (pullTot_comp m m' c.1))

theorem HypF.pull_comp (m' : CoefMap τ F' F'') {p n : ℕ} (x : HypF F p n) :
    HypF.pull (m.comp m') p n x = HypF.pull m' p n (HypF.pull m p n x) := by
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n x
  exact congrArg (HypF.mk F'' p n) (Subtype.ext (pullTot_comp m m' c.1))

end Pull

end GlobalTheory.HodgeCoh
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

theorem eq_of_zsmul_add {A : Type*} [AddCommGroup A] {x y : A} (h : (1 : ℤ) • x + (-1 : ℤ) • y = 0) :
    x = y := by
  rw [one_smul, neg_one_smul, add_neg_eq_zero] at h; exact h

theorem zsmul_add_cancel {A : Type*} [AddCommGroup A] (x : A) : (1 : ℤ) • x + (-1 : ℤ) • x = 0 := by
  rw [one_smul, neg_one_smul, add_neg_cancel]

section Zero

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem map_cochain_congr (M : C ⥤ ModuleCat.{0} R) (f : CatH.Cn M 0) {t t' : ComposableArrows C 0}
    (h : t = t') {Y : C} (u : t.obj (Fin.last 0) ⟶ Y) (u' : t'.obj (Fin.last 0) ⟶ Y) (hu : HEq u u') :
    (M.map u).hom (f t) = (M.map u').hom (f t') := by
  subst h
  rw [eq_of_heq hu]

theorem compat_of_d_eq_zero (M : C ⥤ ModuleCat.{0} R) {f : CatH.Cn M 0} (hf : CatH.d M 0 f = 0)
    {T T' : C} (φ : T ⟶ T') :
    (M.map φ).hom (f (ComposableArrows.mk₀ T)) = f (ComposableArrows.mk₀ T') := by
  let s := ComposableArrows.mk₁ φ
  have h0 : (M.map (CatH.toLast 0 s)).hom (f (CatH.face 0 s)) = f (ComposableArrows.mk₀ T') :=
    (map_cochain_congr M f (t := CatH.face 0 s) (t' := ComposableArrows.mk₀ T')
      (ComposableArrows.ext₀ rfl) (CatH.toLast 0 s) (𝟙 T') HEq.rfl).trans
      (congrArg (fun g : M.obj T' ⟶ M.obj T' ↦ g.hom (f (ComposableArrows.mk₀ T'))) (M.map_id T'))
  have h1 : (M.map (CatH.toLast 1 s)).hom (f (CatH.face 1 s)) =
      (M.map φ).hom (f (ComposableArrows.mk₀ T)) :=
    map_cochain_congr M f (t := CatH.face 1 s) (t' := ComposableArrows.mk₀ T)
      (ComposableArrows.ext₀ rfl) (CatH.toLast 1 s) φ HEq.rfl
  have e : ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (M.map (CatH.toLast i s)).hom (f (CatH.face i s)) = 0 :=
    congrFun hf s
  rw [Fin.sum_univ_two, h0, h1] at e
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at e
  exact (eq_of_zsmul_add e).symm

variable (F : C ⥤ CommAlgCat.{0} R)

theorem BF_self : ∀ n : ℕ, BF F n n = ⊥
  | 0 => rfl
  | n + 1 => by
    change (TotF F (n + 1) n).map _ = ⊥
    rw [TotF_eq_bot F (Nat.lt_succ_self n), Submodule.map_bot]

theorem HypF.toHyp_zero_bijective (n : ℕ) : Function.Bijective (HypF.toHyp F 0 n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_,
    LinearMap.range_eq_top.1 (Hyp.fil_zero F n)⟩
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F 0 n x
  have h : c.1 ∈ BTot F n := Hyp.mk_eq_zero.1 hx
  refine HypF.mk_eq_zero.2 ?_
  rcases n with _ | n
  · exact h
  · obtain ⟨e, he⟩ := h
    exact ⟨e, by rw [TotF_zero]; trivial, he⟩

def ofTop (n : ℕ) : Term F 0 n →ₗ[R] Tot F n :=
  LinearMap.single R (fun b : Bidegree n ↦ Term F b.1.1 b.1.2) ⟨(0, n), zero_add n⟩

variable {F}

theorem ofTop_same {n : ℕ} (c : Term F 0 n) (h : 0 + n = n) : ofTop F n c ⟨(0, n), h⟩ = c :=
  Pi.single_eq_same (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2) _ _

theorem ofTop_mem_TotF {n : ℕ} (c : Term F 0 n) : ofTop F n c ∈ TotF F n n := fun b hb ↦
  Pi.single_eq_of_ne (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2)
    (fun e ↦ by rw [e] at hb; exact lt_irrefl _ hb) _

theorem eq_ofTop {n : ℕ} {c : Tot F n} (hc : c ∈ TotF F n n) :
    c = ofTop F n (c ⟨(0, n), zero_add n⟩) := by
  funext ⟨(a, q), h⟩
  rcases a with _ | a
  · obtain rfl : q = n := by simpa using h
    exact (ofTop_same _ _).symm
  · have hq : q < n := by dsimp only at h; omega
    rw [hc _ hq, ofTop_mem_TotF _ _ hq]

theorem ofTop_mem_ZF {n : ℕ} {c : Term F 0 n} (h1 : dH F 0 n c = 0) (h2 : dV F 0 n c = 0) :
    ofTop F n c ∈ ZF F n n := by
  refine ⟨ofTop_mem_TotF c, funext fun ⟨(a, q), h⟩ ↦ ?_⟩
  dsimp only at h
  have hH : totH F n (ofTop F n c) ⟨(a, q), h⟩ = 0 := by
    rcases a with _ | _ | a
    · rfl
    · obtain rfl : q = n := by omega
      rw [totH_succ, ofTop_same, h1]
    · rw [totH_succ, ofTop_mem_TotF c _ (by dsimp only; omega), map_zero]
  have hV : totV F n (ofTop F n c) ⟨(a, q), h⟩ = 0 := by
    rcases q with _ | q
    · rfl
    rcases a with _ | a
    · obtain rfl : q = n := by omega
      rw [totV_succ, ofTop_same, h2, smul_zero]
    · rw [totV_succ, ofTop_mem_TotF c _ (by dsimp only; omega), map_zero, smul_zero]
  rw [dTot_apply, hH, hV, add_zero]; rfl

theorem dTot_top {n : ℕ} (c : Tot F n) (h : 0 + (n + 1) = n + 1) :
    dTot F n c ⟨(0, n + 1), h⟩ = dV F 0 n (c ⟨(0, n), zero_add n⟩) := by
  rw [dTot_apply, totH_zero, totV_succ, zero_add, pow_zero, one_smul]

end Zero

section Cone

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

def coneTerm (q : ℕ) : Om R B q →ₗ[R] Term F 0 q :=
  LinearMap.pi fun s ↦ (SemiHom.of_algHom (e (s.obj (Fin.last 0)))).mOm q


include he in

theorem dH_coneTerm {q : ℕ} (ω : Om R B q) : dH F 0 q (coneTerm e q ω) = 0 := by
  funext s
  have k : ∀ i : Fin 2, ((OmF F q).map (CatH.toLast i s)).hom (coneTerm e q ω (CatH.face i s)) =
      (SemiHom.of_algHom (e (s.obj (Fin.last 1)))).mOm q ω := fun i ↦
    SemiHom.mOm_mOm _ (semiHom_mp F (CatH.toLast i s)) _ (he _) ω
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    ((OmF F q).map (CatH.toLast i s)).hom (coneTerm e q ω (CatH.face i s)) = 0
  rw [Fin.sum_univ_two, k, k]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  exact zsmul_add_cancel _

theorem dV_coneTerm {q : ℕ} (ω : Om R B q) :
    dV F 0 q (coneTerm e q ω) = coneTerm e (q + 1) (dOm R B q ω) :=
  funext fun _ ↦ (SemiHom.mOm_dOm _ ω).symm

def coneZ (n : ℕ) : LinearMap.ker (dOm R B n) →ₗ[R] ZF F n n :=
  ((ofTop F n ∘ₗ coneTerm e n).domRestrict _).codRestrict _ fun ω ↦
    ofTop_mem_ZF (dH_coneTerm e he ω.1)
      (by rw [dV_coneTerm]; exact (congrArg (coneTerm e (n + 1)) ω.2).trans (map_zero _))

def coneF (n : ℕ) : LinearMap.ker (dOm R B n) →ₗ[R] HypF F n n := HypF.mk F n n ∘ₗ coneZ e he n

def coneCl (n : ℕ) : LinearMap.ker (dOm R B n) →ₗ[R] Hyp F n := HypF.toHyp F n n ∘ₗ coneF e he n

theorem coneCl_mem_fil {n : ℕ} (ω : LinearMap.ker (dOm R B n)) : coneCl e he n ω ∈ Hyp.fil F n n :=
  ⟨coneF e he n ω, rfl⟩

theorem coneCl_dOm {n : ℕ} (η : Om R B n) : coneCl e he (n + 1) ⟨dOm R B n η, dOm_dOm η⟩ = 0 := by
  refine Hyp.mk_eq_zero.2 ⟨ofTop F n (coneTerm e n η), ?_⟩
  have hm : dTot F n (ofTop F n (coneTerm e n η)) ∈ TotF F (n + 1) (n + 1) := by
    rintro ⟨⟨a, q⟩, h⟩ hq
    dsimp only at h hq
    have hH : totH F n (ofTop F n (coneTerm e n η)) ⟨(a, q), h⟩ = 0 := by
      rcases a with _ | _ | a
      · rfl
      · obtain rfl : q = n := by omega
        rw [totH_succ, ofTop_same, dH_coneTerm e he]
      · rw [totH_succ, ofTop_mem_TotF _ _ (by dsimp only; omega), map_zero]
    have hV : totV F n (ofTop F n (coneTerm e n η)) ⟨(a, q), h⟩ = 0 := by
      rcases q with _ | q
      · rfl
      · rw [totV_succ, ofTop_mem_TotF _ _ (by dsimp only; omega), map_zero, smul_zero]
    rw [dTot_apply, hH, hV, add_zero]
  rw [eq_ofTop hm, dTot_top, ofTop_same, dV_coneTerm]
  rfl

variable {T₀ : C} (hb : Function.Bijective (e T₀))

def backOm (q : ℕ) : Om R (F.obj T₀) q →ₗ[R] Om R B q :=
  (SemiHom.of_algHom (AlgEquiv.ofBijective _ hb).symm.toAlgHom).mOm q

theorem backOm_coneTerm {q : ℕ} (ω : Om R B q) :
    backOm e hb q (coneTerm e q ω (ComposableArrows.mk₀ T₀)) = ω :=
  (SemiHom.mOm_mOm (SemiHom.of_algHom (e T₀)) _ (SemiHom.of_algHom (AlgHom.id R B))
    (fun b ↦ (AlgEquiv.ofBijective _ hb).symm_apply_apply b) ω).trans
    (SemiHom.mOm_id _ (fun _ ↦ rfl) ω)

include hb in

theorem coneCl_eq_zero_iff {n : ℕ} (ω : LinearMap.ker (dOm R B (n + 1))) :
    coneCl e he (n + 1) ω = 0 ↔ ∃ η, dOm R B n η = ω.1 := by
  refine ⟨fun h ↦ ?_, fun ⟨η, hη⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := Hyp.mk_eq_zero.1 h
    have h1 := congrFun hc ⟨(0, n + 1), zero_add _⟩
    rw [dTot_top] at h1
    have h2 := congrFun (h1.trans (ofTop_same (coneTerm e (n + 1) ω.1) _)) (ComposableArrows.mk₀ T₀)
    refine ⟨backOm e hb n (c ⟨(0, n), zero_add n⟩ (ComposableArrows.mk₀ T₀)), ?_⟩
    rw [← backOm_coneTerm e hb ω.1, ← h2]
    exact (SemiHom.mOm_dOm _ _).symm
  · rw [show ω = ⟨dOm R B n η, dOm_dOm η⟩ from Subtype.ext hη.symm, coneCl_dOm]

include hb in

theorem coneF_bijective (h : Limits.IsInitial T₀) (n : ℕ) : Function.Bijective (coneF e he n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun ω hω ↦ ?_, fun x ↦ ?_⟩
  · have h1 : ofTop F n (coneTerm e n ω.1) ∈ BF F n n := HypF.mk_eq_zero.1 hω
    rw [BF_self] at h1
    have h2 := (ofTop_same (coneTerm e n ω.1) (zero_add n)).symm.trans
      (congrFun (show ofTop F n (coneTerm e n ω.1) = 0 from h1) _)
    refine Subtype.ext ?_
    rw [← backOm_coneTerm e hb ω.1, h2]
    exact map_zero _
  · obtain ⟨c, rfl⟩ := HypF.mk_surjective F n n x
    have h1 := dH_lead F (zero_add n) c
    have h2 := (dTot_top c.1 (zero_add _)).symm.trans
      (congrFun (show dTot F n c.1 = 0 from c.2.2) _)
    refine ⟨⟨backOm e hb n (c.1 ⟨(0, n), zero_add n⟩ (ComposableArrows.mk₀ T₀)), ?_⟩, ?_⟩
    · refine (SemiHom.mOm_dOm _ _).symm.trans ?_
      have h3 : dOm R (F.obj T₀) n (c.1 ⟨(0, n), zero_add n⟩ (ComposableArrows.mk₀ T₀)) = 0 :=
        congrFun h2 (ComposableArrows.mk₀ T₀)
      exact (congrArg (backOm e hb (n + 1)) h3).trans (map_zero _)
    · refine congrArg (HypF.mk F n n) (Subtype.ext ?_)
      refine (congrArg (ofTop F n) (funext fun s ↦ ?_)).trans (eq_ofTop c.2.1).symm
      obtain ⟨T, rfl⟩ := s.mk₀_surjective
      refine Eq.trans ?_ (compat_of_d_eq_zero (OmF F n) h1 (h.to T))
      exact SemiHom.mOm_mOm _ (SemiHom.of_algHom (e T)) (semiHom_mp F (h.to T))
        (fun b ↦ (he (h.to T) _).symm.trans
          (congrArg (mp F (h.to T)) ((AlgEquiv.ofBijective _ hb).apply_symm_apply b))) _

include hb in

theorem coneCl_zero_bijective (h : Limits.IsInitial T₀) : Function.Bijective (coneCl e he 0) :=
  (HypF.toHyp_zero_bijective F 0).comp (coneF_bijective e he hb h 0)

end Cone

section Low

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def fn0 (B : Type) [CommRing B] [Algebra R B] : Om R B 0 ≃ₗ[R] B :=
  (exteriorPower.zeroEquiv B Ω[B⁄R]).restrictScalars R

def fm1 (B : Type) [CommRing B] [Algebra R B] : Om R B 1 ≃ₗ[R] Ω[B⁄R] :=
  (exteriorPower.oneEquiv B Ω[B⁄R]).restrictScalars R

def toTot1 : Tot F 1 →ₗ[R] Tot1 F where
  toFun c := (fun _ T' φ ↦ fn0 (F.obj T') (c ⟨(1, 0), rfl⟩ (ComposableArrows.mk₁ φ)),
    fun T ↦ fm1 (F.obj T) (c ⟨(0, 1), rfl⟩ (ComposableArrows.mk₀ T)))
  map_add' _ _ := Tot1.ext (fun _ T' _ ↦ map_add (fn0 (F.obj T')) _ _)
    fun T ↦ map_add (fm1 (F.obj T)) _ _
  map_smul' _ _ := Tot1.ext (fun _ _ _ ↦ LinearEquiv.map_smul _ _ _) fun _ ↦ LinearEquiv.map_smul _ _ _

def toTot2 : Tot F 2 →ₗ[R] Tot2 F where
  toFun c := (fun _ _ T'' φ ψ ↦ fn0 (F.obj T'') (c ⟨(2, 0), rfl⟩ (ComposableArrows.mk₂ φ ψ)),
    fun _ T' φ ↦ fm1 (F.obj T') (c ⟨(1, 1), rfl⟩ (ComposableArrows.mk₁ φ)),
    fun T ↦ c ⟨(0, 2), rfl⟩ (ComposableArrows.mk₀ T))
  map_add' _ _ := Tot2.ext (fun _ _ T'' _ _ ↦ map_add (fn0 (F.obj T'')) _ _)
    (fun _ T' _ ↦ map_add (fm1 (F.obj T')) _ _) fun _ ↦ rfl
  map_smul' _ _ := Tot2.ext (fun _ _ _ _ _ ↦ LinearEquiv.map_smul _ _ _)
    (fun _ _ _ ↦ LinearEquiv.map_smul _ _ _) fun _ ↦ rfl

end Low

end GlobalTheory.HodgeCoh
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

variable {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k''] {X X' X'' : Scheme.{0}}

def resAlg (σ : k →+* k') (B : CommAlgCat.{0} k') : CommAlgCat.{0} k :=
  letI : Algebra k B := Algebra.compHom B σ
  CommAlgCat.of k B


def resHom (σ : k →+* k') {B B' : CommAlgCat.{0} k'} (f : B ⟶ B') : resAlg σ B ⟶ resAlg σ B' :=
  letI : Algebra k B := Algebra.compHom B σ
  letI : Algebra k B' := Algebra.compHom B' σ
  CommAlgCat.ofHom { (f.hom : B →+* B') with commutes' := fun r ↦ f.hom.commutes (σ r) }

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := Spec.map_comp _ _

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem eq_of_spMap_eq {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := congrArg CommRingCat.Hom.hom (Spec.map_injective h)

structure AffPt (s : X ⟶ Sp k) : Type 1 where

  B : CommAlgCat.{0} k

  x : Sp B ⟶ X

  w : x ≫ s = spMap (algebraMap k B)

namespace AffPt

variable {s : X ⟶ Sp k}

instance : Category.{0} (AffPt s) where
  Hom T T' := {φ : T.B ⟶ T'.B // spMap (φ.hom : T.B →+* T'.B) ≫ T.x = T'.x}
  id T := ⟨𝟙 _, by
    rw [show spMap ((𝟙 T.B : T.B ⟶ T.B).hom : T.B →+* T.B) = 𝟙 _ from spMap_id' _, Category.id_comp]⟩
  comp {T T' T''} φ ψ := ⟨φ.1 ≫ ψ.1, by
    have e : ((φ.1 ≫ ψ.1).hom : T.B →+* T''.B) =
        (ψ.1.hom : T'.B →+* T''.B).comp (φ.1.hom : T.B →+* T'.B) := rfl
    rw [e, spMap_comp', Category.assoc, φ.2, ψ.2]⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[ext] theorem hom_ext {T T' : AffPt s} {φ ψ : T ⟶ T'} (h : φ.1 = ψ.1) : φ = ψ := Subtype.ext h

end AffPt

def OPt (s : X ⟶ Sp k) : AffPt s ⥤ CommAlgCat.{0} k where
  obj T := T.B
  map φ := φ.1
  map_id _ := rfl
  map_comp _ _ := rfl

section Coef

variable {s : X ⟶ Sp k} {σ : k →+* k'} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} k'}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap ((algebraMap k' (F.obj T)).comp σ))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')

def ptFun : C ⥤ AffPt s where
  obj T := ⟨resAlg σ (F.obj T), x T, hx T⟩
  map a := ⟨resHom σ (F.map a), hc a⟩
  map_id T := AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun b ↦ mp_id F T b))
  map_comp a b := AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun c ↦ mp_comp F a b c))

def ptCoef : CoefMap σ (OPt s) F where
  G := ptFun x hx hc
  α T := RingHom.id (F.obj T)
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem pull_ptCoef_congr {x' : ∀ T : C, Sp (F.obj T) ⟶ X}
    (hx' : ∀ T, x' T ≫ s = spMap ((algebraMap k' (F.obj T)).comp σ))
    (hc' : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x' T = x' T')
    (e : ∀ T, x T = x' T) (n : ℕ) :
    Hyp.pull (ptCoef x hx hc) n = Hyp.pull (ptCoef x' hx' hc') n := by
  obtain rfl : x = x' := funext e
  rfl

end Coef

abbrev HdR (s : X ⟶ Sp k) (n : ℕ) : Type 1 := Hyp (OPt s) n

abbrev HdRF (s : X ⟶ Sp k) (p n : ℕ) : Type 1 := HypF (OPt s) p n

abbrev HdR.fil (s : X ⟶ Sp k) (p n : ℕ) : Submodule k (HdR s n) := Hyp.fil (OPt s) p n

abbrev HdRF.toHdR (s : X ⟶ Sp k) (p n : ℕ) : HdRF s p n →ₗ[k] HdR s n := HypF.toHyp (OPt s) p n

section Pull

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {s'' : X'' ⟶ Sp k''} {σ : k →+* k'} {τ : k' →+* k''}

theorem comp_w {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (T : AffPt s') :
    (T.x ≫ φ) ≫ s = spMap ((algebraMap k' T.B).comp σ) := by
  rw [Category.assoc, h, ← Category.assoc, T.w, spMap_comp']

def pullCoef {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OPt s) (OPt s') :=
  ptCoef (F := OPt s') (fun T ↦ T.x ≫ φ) (comp_w h) fun _ _ a ↦
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) a.2)

def HdR.pullSemi {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (n : ℕ) : HdR s n →ₛₗ[σ] HdR s' n :=
  Hyp.pull (pullCoef h) n

theorem over_id {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') : f ≫ s = s' ≫ spMap (RingHom.id k) := by
  rw [hf, spMap_id', Category.comp_id]

def HdR.pull {s' : X' ⟶ Sp k} {f : X' ⟶ X} (hf : f ≫ s = s') (n : ℕ) : HdR s n →ₗ[k] HdR s' n :=
  HdR.pullSemi (over_id hf) n

theorem ptCoef_comp {φ : X' ⟶ X} {ψ : X'' ⟶ X'} (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (hx : ∀ T : AffPt s'', ((T.x ≫ ψ) ≫ φ) ≫ s =
      spMap ((algebraMap k'' T.B).comp (τ.comp σ)))
    (hc : ∀ ⦃T T' : AffPt s''⦄ (a : T ⟶ T'),
      spMap (mp (OPt s'') a : (OPt s'').obj T →+* (OPt s'').obj T') ≫ (T.x ≫ ψ) ≫ φ = (T'.x ≫ ψ) ≫ φ) :
    ptCoef (F := OPt s'') (fun T ↦ (T.x ≫ ψ) ≫ φ) hx hc = (pullCoef h).comp (pullCoef h') := rfl

theorem HdR.pullSemi_comp {φ : X' ⟶ X} {ψ : X'' ⟶ X'} (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (n : ℕ) (c : HdR s n) :
    HdR.pullSemi h'' n c = HdR.pullSemi h' n (HdR.pullSemi h n c) := by
  have hx : ∀ T : AffPt s'', ((T.x ≫ ψ) ≫ φ) ≫ s = spMap ((algebraMap k'' T.B).comp (τ.comp σ)) :=
    fun T ↦ (Category.assoc _ _ _).trans (comp_w h'' T)
  have hc : ∀ ⦃T T' : AffPt s''⦄ (a : T ⟶ T'),
      spMap (mp (OPt s'') a : (OPt s'').obj T →+* (OPt s'').obj T') ≫ (T.x ≫ ψ) ≫ φ = (T'.x ≫ ψ) ≫ φ :=
    fun _ _ a ↦ by
      simp only [← Category.assoc]
      exact congrArg (fun y ↦ (y ≫ ψ) ≫ φ) a.2
  refine (LinearMap.congr_fun (pull_ptCoef_congr (F := OPt s'') (σ := τ.comp σ)
    (fun T ↦ T.x ≫ ψ ≫ φ) (comp_w h'')
    (fun _ _ a ↦ (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ψ ≫ φ) a.2))
    (x' := fun T ↦ (T.x ≫ ψ) ≫ φ) hx hc (fun T ↦ (Category.assoc _ _ _).symm) n) c).trans ?_
  exact (congrArg (fun m ↦ Hyp.pull m n c) (ptCoef_comp h h' hx hc)).trans
    (Hyp.pull_comp (pullCoef h) (pullCoef h') c)

theorem HdR.pull_comp {s' : X' ⟶ Sp k} {s'' : X'' ⟶ Sp k} {f : X' ⟶ X} {g : X'' ⟶ X'}
    (hf : f ≫ s = s') (hg : g ≫ s' = s'') (n : ℕ) (c : HdR s n) :
    HdR.pull (f := g ≫ f) (by rw [Category.assoc, hf, hg]) n c = HdR.pull hg n (HdR.pull hf n c) :=
  HdR.pullSemi_comp (over_id hf) (over_id hg) _ n c



def HdRF.pullSemi {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (p n : ℕ) : HdRF s p n →ₛₗ[σ] HdRF s' p n :=
  HypF.pull (pullCoef h) p n


end Pull

section Aff

variable (s : X ⟶ Sp k)

def affCoef : CoefMap (RingHom.id k) (OPt s) (OAff s) :=
  ptCoef (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)

def HdR.toAff (n : ℕ) : HdR s n →ₗ[k] Hyp (OAff s) n := Hyp.pull (affCoef s) n


end Aff

section Fil

variable (s : X ⟶ Sp k)

theorem HdR.fil_zero (n : ℕ) : HdR.fil s 0 n = ⊤ := Hyp.fil_zero _ n

theorem HdR.fil_succ (n : ℕ) : HdR.fil s (n + 1) n = ⊥ := Hyp.fil_eq_bot _ (Nat.lt_succ_self n)

end Fil

section Affine

variable (k) (B : Type) [CommRing B] [Algebra k B]

def idPt : AffPt (algStr k B) := ⟨CommAlgCat.of k B, 𝟙 _, Category.id_comp _⟩

variable {k B}

def toPt (T : AffPt (algStr k B)) : B →ₐ[k] T.B :=
  { (Spec.preimage T.x).hom with
    commutes' := fun r ↦ by
      have e : spMap (((Spec.preimage T.x).hom).comp (algebraMap k B)) = spMap (algebraMap k T.B) := by
        rw [spMap_comp', ← T.w]
        exact congrArg (· ≫ algStr k B) (Spec.map_preimage T.x)
      exact congrArg (fun g : k →+* T.B ↦ g r) (eq_of_spMap_eq e) }

theorem spMap_toPt (T : AffPt (algStr k B)) : spMap (toPt T : B →+* T.B) = T.x := Spec.map_preimage T.x

theorem toPt_comp ⦃T T' : AffPt (algStr k B)⦄ (φ : T ⟶ T') (b : B) :
    mp (OPt (algStr k B)) φ (toPt T b) = toPt T' b := by
  have e : spMap (((φ.1.hom : T.B →+* T'.B)).comp (toPt T : B →+* T.B)) = spMap (toPt T' : B →+* T'.B) := by
    rw [spMap_comp', spMap_toPt, spMap_toPt]; exact φ.2
  exact congrArg (fun g : B →+* T'.B ↦ g b) (eq_of_spMap_eq e)

def idPt_isInitial : Limits.IsInitial (idPt k B) :=
  Limits.IsInitial.ofUniqueHom (fun T ↦ ⟨CommAlgCat.ofHom (toPt T), (Category.comp_id _).trans (spMap_toPt T)⟩)
    fun T φ ↦ AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective (eq_of_spMap_eq
      (((Category.comp_id _).symm.trans φ.2).trans (spMap_toPt T).symm))))

theorem toPt_idPt (b : B) : toPt (idPt k B) b = b := by
  have e : spMap (toPt (idPt k B) : B →+* (idPt k B).B) = spMap (RingHom.id B) :=
    (spMap_toPt _).trans (spMap_id' B).symm
  exact congrArg (fun g : B →+* B ↦ g b) (@eq_of_spMap_eq B (idPt k B).B _ _ (toPt (idPt k B)) (RingHom.id B) e)

theorem toPt_idPt_bijective : Function.Bijective (toPt (idPt k B)) :=
  Function.bijective_iff_has_inverse.2 ⟨fun b ↦ b, fun b ↦ toPt_idPt b, fun b ↦ toPt_idPt b⟩

def HdR.ofForm (n : ℕ) : LinearMap.ker (dOm k B n) →ₗ[k] HdR (algStr k B) n :=
  coneCl (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) n

theorem HdR.ofForm_mem_fil {n : ℕ} (ω : LinearMap.ker (dOm k B n)) :
    HdR.ofForm n ω ∈ HdR.fil (algStr k B) n n :=
  coneCl_mem_fil (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) ω

theorem HdR.ofForm_eq_zero_iff {n : ℕ} (ω : LinearMap.ker (dOm k B (n + 1))) :
    HdR.ofForm (n + 1) ω = 0 ↔ ∃ η, dOm k B n η = ω.1 :=
  coneCl_eq_zero_iff (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) (T₀ := idPt k B) toPt_idPt_bijective ω

def HdR.affZeroEquiv : LinearMap.ker (dOm k B 0) ≃ₗ[k] HdR (algStr k B) 0 :=
  LinearEquiv.ofBijective (HdR.ofForm 0) (coneCl_zero_bijective (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B))
    (fun T ↦ toPt T) (fun _ _ φ b ↦ toPt_comp φ b) (T₀ := idPt k B) toPt_idPt_bijective idPt_isInitial)

variable (k) in

theorem dOm_zero_self (x : Om k k 0) : dOm k k 0 x = 0 := by
  refine Subtype.ext ?_
  rw [coe_dOm, coe_eq_algebraMap_zeroEquiv x, dDR_algebraMap]
  have : D k k (exteriorPower.zeroEquiv k Ω[k⁄k] x) = 0 := by
    rw [← Algebra.algebraMap_self_apply (exteriorPower.zeroEquiv k Ω[k⁄k] x)]
    exact (D k k).map_algebraMap _
  rw [this, map_zero]; rfl

variable (k) in

def HdR.pointEquiv : k ≃ₗ[k] HdR (algStr k k) 0 :=
  (fn0 k).symm ≪≫ₗ (LinearEquiv.ofTop _ (eq_top_iff.2 fun x _ ↦ LinearMap.mem_ker.2 (dOm_zero_self k x))).symm ≪≫ₗ
    HdR.affZeroEquiv

open Polynomial in
variable (k) in

def tdtForm : LinearMap.ker (dOm k k[X] 1) :=
  ⟨⟨ι1 ((Polynomial.X : k[X]) • D k k[X] Polynomial.X), ι_mem _⟩, by
    rw [LinearMap.mem_ker, ← dOne_eq_dOm, dOne_line]⟩

open Polynomial in

theorem HdR.ofForm_tdt_ne_zero [Nontrivial k] (h2 : (2 : k) = 0) : HdR.ofForm 1 (tdtForm k) ≠ 0 := by
  rw [Ne, HdR.ofForm_eq_zero_iff]
  rintro ⟨η, hη⟩
  have e1 := congrArg Subtype.val hη
  rw [coe_dOm, coe_eq_algebraMap_zeroEquiv η, dDR_algebraMap] at e1
  have e2 := ExteriorAlgebra.ι_inj k[X] _ _ |>.1 e1
  have f3 := congrArg (polynomialEquiv k) e2
  simp only [Derivation.coeFn_coe, map_smul, polynomialEquiv_D, derivative_X, smul_eq_mul,
    mul_one] at f3
  have := congrArg (coeff · 1) f3
  simp only [coeff_derivative, coeff_X_one] at this
  have hc := this
  rw [show ((1 : ℕ) : k) + 1 = 2 by norm_num, h2, mul_zero] at hc
  exact zero_ne_one hc

end Affine

example (s : X ⟶ Sp k) : Module k (HdR s 5) := inferInstance

example (s : X ⟶ Sp k) : HdR.fil s 2 1 = ⊥ := HdR.fil_succ s 1

example : Nontrivial (HdR (algStr ℤ ℤ) 0) := (HdR.pointEquiv ℤ).symm.toEquiv.nontrivial

example : HdR.fil (algStr (ZMod 2) (Polynomial (ZMod 2))) 1 1 ≠ ⊥ := fun h ↦
  HdR.ofForm_tdt_ne_zero (k := ZMod 2) rfl
    ((Submodule.mem_bot _).1 (h ▸ HdR.ofForm_mem_fil (tdtForm (ZMod 2))))

end GlobalTheory.HodgeCoh
end
end
