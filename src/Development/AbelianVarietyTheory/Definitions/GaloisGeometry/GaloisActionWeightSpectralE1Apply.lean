import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Gysin

open GlobalTheory.EtC

theorem Ht.cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem Ht.cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem Ht.cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (hn : n = n') (hi : i = i') (hn' : n' = n'')
    (hi' : i' = i'') (x : Ht q E n i) : (x.cast hn hi).cast hn' hi' = x.cast (hn.trans hn') (hi.trans hi') := by
  subst hn; subst hi; subst hn'; subst hi'; rfl

theorem cup_cast_left {q : ℕ} {E : Spc} {n i n' i' m j : ℤ} (hn : n = n') (hi : i = i') (a : Ht q E n i)
    (b : Ht q E m j) :
    cup q (a.cast hn hi) b = (cup q a b).cast (by rw [hn]) (by rw [hi]) := by
  subst hn; subst hi; rfl

def pairing (q : ℕ) {X : Scheme.{0}} (d : ℕ) (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) {n i : ℤ}
    (a : Ht q (sch.obj X) n i) (b : Ht q (sch.obj X) (2 * d - n) (d - i)) : ZMod q :=
  t ((cup q a b).cast (by ring) (by ring))

def IsPerfect (q : ℕ) {X : Scheme.{0}} (d : ℕ) (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) : Prop :=
  ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = pairing q d t a b

def IsTranspose (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
    (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ)
    (γ : Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))) : Prop :=
  ∀ (a : Ht q (sch.obj Z) b i) (y : Ht q (sch.obj X) (2 * dZ - b) (dZ - i)),
    tX ((cup q (γ a) y).cast (by ring) (by ring)) = tZ ((cup q a (pull _ (sch.map f) _ _ y)).cast (by ring) (by ring))

def pushWith (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
    (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ) :
    Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  pick (IsTranspose q f dZ dX tZ tX b i)

abbrev TrFam : Type 1 := ∀ (q : ℕ) (X : Scheme.{0}) (d : ℕ), Ht q (sch.obj X) (2 * d) d →+ ZMod q

def one0 (q : ℕ) (X : Scheme.{0}) : Ht q (sch.obj X) (2 * ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) :=
  (one q (sch.obj X)).cast (by simp) (by simp)

def IsSection {Y X : Scheme.{0}} (f : Y ⟶ X) (L : cech f ⟶ ofCat (glCat 1)) (s : Γ(Y, ⊤)) : Prop :=
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (a b : U ⟶ Y) (h : ∀ j, ![a, b] j ≫ f = x),
    b.appTop.hom s = (lineUnit L (cechPt f 1 x ![a, b] h) : Γ(U, ⊤)) * a.appTop.hom s

def IsZeroScheme {D Y X : Scheme.{0}} (ι : D ⟶ X) (f : Y ⟶ X) (s : Γ(Y, ⊤)) : Prop :=
  ∀ (U : Scheme.{0}) (g : U ⟶ Y), (∃ h : U ⟶ D, h ≫ ι = g ≫ f) ↔ g.appTop.hom s = 0

def IsTraceFam (T : TrFam) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k],
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (d : ℕ) [SmoothOfRelativeDimension d p], IsPerfect q d (T q X d)) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsIso p],
      T q X 0 (one0 q X) = 1) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X X₁ X₂ : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (d : ℕ) [SmoothOfRelativeDimension d p] (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X), IsIso (coprod.desc j₁ j₂) →
      ∀ y, T q X d y = T q X₁ d (pull _ (sch.map j₁) _ _ y) + T q X₂ d (pull _ (sch.map j₂) _ _ y)) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X D Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (d : ℕ) [SmoothOfRelativeDimension (d + 1) p] (ι : D ⟶ X) [IsClosedImmersion ι]
      [SmoothOfRelativeDimension d (ι ≫ p)] (f : Y ⟶ X) [Etale f] [Surjective f] (L : cech f ⟶ ofCat (glCat 1))
      (s : Γ(Y, ⊤)), IsSection f L s → IsZeroScheme ι f s → ∀ c : Ht q (sch.obj X) 2 1,
      pull _ (cechAug f) _ _ c = c1 q L → ∀ y : Ht q (sch.obj X) (2 * d) d,
      T q X (d + 1) ((cup q c y).cast (by push_cast; ring) (by push_cast; ring)) = T q D d (pull _ (sch.map ι) _ _ y)) ∧
    (∀ (Q q : ℕ) [NeZero Q] [NeZero q] (hqQ : q ∣ Q), IsUnit (Q : k) → ∀ {X : Scheme.{0}}
      (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
      (y : Ht Q (sch.obj X) (2 * d) d), T q X d (red Q q (sch.obj X) _ _ y) = ZMod.castHom hqQ (ZMod q) (T Q X d y))

def tr : TrFam := pick IsTraceFam

def gysin (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (b i : ℤ) :
    Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  pushWith q f dZ dX (tr q Z dZ) (tr q X dX) b i

section API

variable {q : ℕ}

theorem Ht.cast_self {E : Spc} {n i : ℤ} (hn : n = n) (hi : i = i) (x : Ht q E n i) : x.cast hn hi = x := rfl

theorem cup_cast_right {E : Spc} {n i m j m' j' : ℤ} (hm : m = m') (hj : j = j') (a : Ht q E n i)
    (b : Ht q E m j) :
    cup q a (b.cast hm hj) = (cup q a b).cast (by rw [hm]) (by rw [hj]) := by
  subst hm; subst hj; rfl

def Ht.castHom {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : Ht q E n i →+ Ht q E n' i' where
  toFun x := x.cast hn hi
  map_zero' := Ht.cast_zero hn hi
  map_add' := Ht.cast_add hn hi

theorem Ht.castHom_apply {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    Ht.castHom hn hi x = x.cast hn hi := rfl

variable {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
  (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ)

private theorem hm : 2 * (dX : ℤ) - (b + 2 * ((dX : ℤ) - dZ)) = 2 * dZ - b := by ring
private theorem hj : (dX : ℤ) - (i + ((dX : ℤ) - dZ)) = dZ - i := by ring

def form (a : Ht q (sch.obj Z) b i) :
    Ht q (sch.obj X) (2 * dX - (b + 2 * ((dX : ℤ) - dZ))) (dX - (i + ((dX : ℤ) - dZ))) →+ ZMod q :=
  ((tZ.comp (Ht.castHom (by ring) (by ring))).comp (cup q a)).comp
    ((pull _ (sch.map f) _ _).comp (Ht.castHom (hm dZ dX b) (hj dZ dX i)))

theorem form_add (a a' : Ht q (sch.obj Z) b i) : form f dZ dX tZ b i (a + a') = form f dZ dX tZ b i a + form f dZ dX tZ b i a' := by
  ext y
  simp only [form, AddMonoidHom.comp_apply, map_add, AddMonoidHom.add_apply]

variable {f dZ dX tZ tX b i}

theorem pairing_add {d : ℕ} (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) {n j : ℤ} (c c' : Ht q (sch.obj X) n j)
    (y : Ht q (sch.obj X) (2 * d - n) (d - j)) : pairing q d t (c + c') y = pairing q d t c y + pairing q d t c' y := by
  simp only [pairing, map_add, AddMonoidHom.add_apply, Ht.cast_add]

theorem pairing_zero {d : ℕ} (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) {n j : ℤ}
    (y : Ht q (sch.obj X) (2 * d - n) (d - j)) : pairing q d t (0 : Ht q (sch.obj X) n j) y = 0 := by
  simp only [pairing, map_zero, AddMonoidHom.zero_apply, Ht.cast_zero]

theorem pairing_iff (a : Ht q (sch.obj Z) b i) (c : Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))) :
    (∀ y, form f dZ dX tZ b i a y = pairing q dX tX c y) ↔
      ∀ y : Ht q (sch.obj X) (2 * dZ - b) (dZ - i),
        tX ((cup q c y).cast (by ring) (by ring)) = tZ ((cup q a (pull _ (sch.map f) _ _ y)).cast (by ring) (by ring)) := by
  constructor
  · intro h y
    have := h (y.cast (hm dZ dX b).symm (hj dZ dX i).symm)
    simp only [form, pairing, AddMonoidHom.comp_apply, Ht.castHom_apply, Ht.cast_cast, Ht.cast_self,
      cup_cast_right] at this
    exact this.symm
  · intro h y
    have := h (y.cast (hm dZ dX b) (hj dZ dX i))
    simp only [form, pairing, AddMonoidHom.comp_apply, Ht.castHom_apply, cup_cast_right, Ht.cast_cast] at this ⊢
    exact this.symm


theorem IsTranspose.unique (hX : IsPerfect q dX tX) {γ γ' : Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))}
    (h : IsTranspose q f dZ dX tZ tX b i γ) (h' : IsTranspose q f dZ dX tZ tX b i γ') : γ = γ' := by
  ext a
  obtain ⟨c, _, hu⟩ := hX _ _ (form f dZ dX tZ b i a)
  exact (hu _ ((pairing_iff a (γ a)).2 (h a))).trans (hu _ ((pairing_iff a (γ' a)).2 (h' a))).symm




end API

theorem tr_spec (h : ∃ T, IsTraceFam T) : IsTraceFam tr := pick_spec h



example : ¬ IsTraceFam 0 := by
  intro h
  have h2 : IsUnit ((2 : ℕ) : AlgebraicClosure ℚ) := isUnit_iff_ne_zero.2 (by norm_num)
  have := (h (AlgebraicClosure ℚ)).2.1 2 h2 (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
  simp at this

section Adic
variable (l : ℕ) [Fact l.Prime]

def gysinHl {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (b i : ℤ) :
    Hl l (sch.obj Z) b i →ₗ[ℤ_[l]] Hl l (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  pick fun g => ∀ (x : Hl l (sch.obj Z) b i) (k : ℕ), (g x).1 k = gysin (l ^ k) f dZ dX b i (x.1 k)

example {ι : Type} [LinearOrder ι] {X : Scheme.{0}} (I : ι → X.IdealSheafData) (s : ℕ) (j : Fin (s + 2)) (d : ℕ)
    (hs : s + 1 ≤ d) (b i : ℤ) :
    Ht (l ^ 2) (sch.obj (GlobalTheory.Strata.Ystr I (s + 1))) b i →+ Ht (l ^ 2) (sch.obj (GlobalTheory.Strata.Ystr I s)) (b + 2) (i + 1) :=
  (Ht.castHom (by push_cast [Nat.cast_sub hs, Nat.cast_sub (Nat.le_of_succ_le hs)]; ring)
      (by push_cast [Nat.cast_sub hs, Nat.cast_sub (Nat.le_of_succ_le hs)]; ring)).comp
    (gysin (l ^ 2) (GlobalTheory.Strata.δ I s j) (d - (s + 1)) (d - s) b i)

end Adic

end GlobalTheory.EtC.Gysin

end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def castHQ {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : HQ l E n i ≃ₗ[ℚ_[l]] HQ l E n' i' := by
  subst hn; subst hi; exact LinearEquiv.refl _ _

@[simp] theorem castHQ_refl {E : Spc} {n i : ℤ} (x : HQ l E n i) : castHQ l (E := E) (rfl : n = n) (rfl : i = i) x = x := rfl

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def idx (m : ℕ) (a : ℤ) : Finset ℕ := (Finset.range m).filter fun s => -a ≤ (s : ℤ) ∧ a + 2 * (s : ℤ) < m

def str (a : ℤ) (s : ℕ) : ℕ := (a + 2 * (s : ℤ)).toNat

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

abbrev Summand (a b w : ℤ) (s : ℕ) : Type 1 := HQ l (sch.obj (Ystr J (str a s))) (b - 2 * s) (w - s)

abbrev E1 (a b w : ℤ) : Type 1 := ∀ s : idx (Fintype.card ι) a, Summand l J a b w s

def castStr {t t' : ℕ} {n i n' i' : ℤ} (ht : t = t') (hn : n = n') (hi : i = i') :
    HQ l (sch.obj (Ystr J t)) n i ≃ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J t')) n' i' := by
  subst ht; subst hn; subst hi; exact LinearEquiv.refl _ _

@[simp] theorem castStr_refl {t : ℕ} {n i : ℤ} (x : HQ l (sch.obj (Ystr J t)) n i) :
    castStr l J (rfl : t = t) (rfl : n = n) (rfl : i = i) x = x := rfl

def res (t : ℕ) (n i : ℤ) : HQ l (sch.obj (Ystr J t)) n i →ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J (t + 1))) n i :=
  ∑ j : Fin (t + 2), ((-1 : ℚ_[l]) ^ (j : ℕ)) • pullHQ l (sch.map (δ J t j)) n i

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

theorem str_N (a : ℤ) (s : ℕ) : str a (s + 1) = str (a + 2) s := by
  unfold str; congr 1; push_cast; ring

def prj {a b w : ℤ} (s : ℕ) (h : s ∈ idx (Fintype.card ι) a) : E1 l J a b w →ₗ[ℚ_[l]] Summand l J a b w s :=
  LinearMap.proj (R := ℚ_[l]) (φ := fun s : idx (Fintype.card ι) a => Summand l J a b w s) ⟨s, h⟩

def nId (a b w : ℤ) (s : ℕ) : Summand l J a b w (s + 1) ≃ₗ[ℚ_[l]] Summand l J (a + 2) (b - 2) (w - 1) s :=
  castStr l J (str_N a s) (by push_cast; ring) (by push_cast; ring)

def N (a b w : ℤ) : E1 l J a b w →ₗ[ℚ_[l]] E1 l J (a + 2) (b - 2) (w - 1) :=
  LinearMap.pi fun s' =>
    if h : s'.1 + 1 ∈ idx (Fintype.card ι) a then (nId l J a b w s'.1).toLinearMap ∘ₗ prj l J (s'.1 + 1) h else 0

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

example : idx 2 (-1) = {1} ∧ idx 2 0 = {0} ∧ idx 2 1 = {0} ∧ idx 2 2 = ∅ ∧ idx 2 (-2) = ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

example (n i : ℤ) : res l J 0 n i = pullHQ l (sch.map (δ J 0 0)) n i - pullHQ l (sch.map (δ J 0 1)) n i := by
  simp [res, Fin.sum_univ_two, sub_eq_add_neg]

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

abbrev geomπ : GlobalTheory.Et.geom Ω p ⟶ V := pullback.fst _ _

abbrev geomFam : ι → (GlobalTheory.Et.geom Ω p).IdealSheafData := GlobalTheory.Strata.pull I (geomπ Ω p)

def galS (σ : Ω ≃ₐ[k] Ω) (S : Finset ι) : GlobalTheory.Strata.Y (geomFam Ω p I) S ⟶ GlobalTheory.Strata.Y (geomFam Ω p I) S :=
  (pullIso I (geomπ Ω p) S).hom ≫
    pullback.map (geomπ Ω p) (Yι I S) (geomπ Ω p) (Yι I S) (GlobalTheory.Et.galMap Ω p σ) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, GlobalTheory.Et.galMap_fst]) (by simp) ≫
    (pullIso I (geomπ Ω p) S).inv

@[reassoc (attr := simp)]
theorem galS_Yι (σ : Ω ≃ₐ[k] Ω) (S : Finset ι) :
    galS Ω p I σ S ≫ Yι (geomFam Ω p I) S = Yι (geomFam Ω p I) S ≫ GlobalTheory.Et.galMap Ω p σ := by
  show _ ≫ Yι (GlobalTheory.Strata.pull I (geomπ Ω p)) S = Yι (GlobalTheory.Strata.pull I (geomπ Ω p)) S ≫ _
  rw [← pullIso_hom_fst I (geomπ Ω p) S]
  simp only [galS, Category.assoc, Iso.inv_hom_id_assoc, pullback.map, pullback.lift_fst]

theorem galS_one (S : Finset ι) : galS Ω p I 1 S = 𝟙 _ :=
  (cancel_mono (Yι (geomFam Ω p I) S)).1 (by rw [galS_Yι, galMap_one, Category.comp_id, Category.id_comp])

theorem galS_mul (σ τ : Ω ≃ₐ[k] Ω) (S : Finset ι) : galS Ω p I (σ * τ) S = galS Ω p I σ S ≫ galS Ω p I τ S :=
  (cancel_mono (Yι (geomFam Ω p I) S)).1 (by simp [galMap_mul])

def galStr (σ : Ω ≃ₐ[k] Ω) (t : ℕ) : Ystr (geomFam Ω p I) t ⟶ Ystr (geomFam Ω p I) t :=
  Sigma.desc fun S : Idx ι t => galS Ω p I σ S.1 ≫ inj _ S

@[reassoc (attr := simp)]
theorem inj_galStr (σ : Ω ≃ₐ[k] Ω) {t : ℕ} (S : Idx ι t) :
    inj _ S ≫ galStr Ω p I σ t = galS Ω p I σ S.1 ≫ inj _ S := Sigma.ι_desc _ _

theorem galStr_one (t : ℕ) : galStr Ω p I 1 t = 𝟙 _ :=
  Ystr_hom_ext _ fun S => by rw [inj_galStr, galS_one, Category.id_comp, Category.comp_id]

theorem galStr_mul (σ τ : Ω ≃ₐ[k] Ω) (t : ℕ) : galStr Ω p I (σ * τ) t = galStr Ω p I σ t ≫ galStr Ω p I τ t :=
  Ystr_hom_ext _ fun S => by simp [galS_mul]

@[reassoc]
theorem galStr_Ystrπ (σ : Ω ≃ₐ[k] Ω) (t : ℕ) :
    galStr Ω p I σ t ≫ Ystrπ _ t = Ystrπ _ t ≫ GlobalTheory.Et.galMap Ω p σ :=
  Ystr_hom_ext _ fun S => by simp

@[reassoc]
theorem δ_galStr (σ : Ω ≃ₐ[k] Ω) (t : ℕ) (j : Fin (t + 2)) :
    δ _ t j ≫ galStr Ω p I σ t = galStr Ω p I σ (t + 1) ≫ δ _ t j :=
  Ystr_hom_ext _ fun S => by
    simp only [inj_δ_assoc, inj_galStr, inj_galStr_assoc, Category.assoc, inj_δ]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (cancel_mono (Yι _ _)).1 (by simp)

variable (a b w : ℤ)

def galoisActionWeightSpectralE1 : Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (E1 l (geomFam Ω p I) a b w) where
  toFun σ := LinearMap.pi fun s => pullHQ l (sch.map (galStr Ω p I σ (str a s))) _ _ ∘ₗ LinearMap.proj s
  map_one' := by
    refine LinearMap.ext fun x => funext fun s => ?_
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, galStr_one, CategoryTheory.Functor.map_id, pullHQ_map_id, LinearMap.id_apply, Module.End.one_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun x => funext fun s => ?_
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, galStr_mul, Functor.map_comp, pullHQ_map_comp, Module.End.mul_apply]

end Galois

end GlobalTheory.EtC.WSS
end
end
