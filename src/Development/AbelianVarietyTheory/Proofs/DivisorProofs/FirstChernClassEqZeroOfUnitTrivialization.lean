import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddi

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.PStep
open GlobalTheory.EtC

abbrev P (M : ℕ) (A : Type) [CommRing A] : Spc := pullback (trivV M (sp A)) (PGL.pr M)

theorem comp_trivV (M : ℕ) {E E' : Spc} (f : E ⟶ E') : f ≫ trivV M E' = trivV M E := by
  ext n U x
  rfl

def TU (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] : Type :=
  {v : Um M B // p v.1}

theorem TU.comp_aux {M : ℕ} {B : Type} [CommRing B] (x y z : Fin M → B) (u u' : Bˣ) (h1 : x = (u : B) • y)
    (h2 : y = (u' : B) • z) : x = ((u' * u : Bˣ) : B) • z := by
  subst h1 h2
  rw [smul_smul, Units.val_mul, mul_comm]

instance (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] :
    SmallCategory (TU M p B) where
  Hom v w := {u : Bˣ // v.1.1 = (u : B) • w.1.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, TU.comp_aux _ _ _ _ _ f.2 g.2⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def TU.map (M : ℕ) {p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop}
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v))
    {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) : TU M p B ⥤ TU M p C where
  obj v := ⟨(Um.map M f).obj v.1, hp f _ v.2⟩
  map {v w} u := ⟨Units.map (f : B →* C) u.1, by
    funext i
    have h := congrArg f (congrFun u.2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h
    exact h⟩
  map_id v := Subtype.ext (map_one (Units.map (f : B →* C)))
  map_comp u u' := Subtype.ext (map_mul (Units.map (f : B →* C)) _ _)

def tuCat (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop)
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v)) :
    CommRingCat.{0} ⥤ Cat.{0,0} where
  obj B := Cat.of (TU M p B)
  map f := (TU.map M hp f.hom).toCatHom
  map_id B := rfl
  map_comp f g := rfl

def TU.toUm (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] :
    TU M p B ⥤ Um M B where
  obj v := v.1
  map {v w} u := ⟨(1, u.1), by simpa using u.2⟩
  map_id v := rfl
  map_comp u u' := Subtype.ext (Prod.ext (mul_one 1).symm rfl)

def tuToPgl (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop)
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v)) :
    tuCat M p hp ⟶ pglCat M where
  app B := (TU.toUm M p B).toCatHom
  naturality B C f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w u => heq_of_eq ?_)
    exact Subtype.ext (Prod.ext (map_one (Matrix.GeneralLinearGroup.map f.hom)).symm rfl)

theorem tuToPgl_pr (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop)
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v)) :
    ofCatMap (tuToPgl M p hp) ≫ PGL.pr M = trivV M (ofCat (tuCat M p hp)) := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

def toP {M : ℕ} {C : CommRingCat.{0} ⥤ Cat.{0,0}} (ρ : C ⟶ pglCat M) (hρ : ofCatMap ρ ≫ PGL.pr M = trivV M (ofCat C))
    (A : Type) [CommRing A] : ofCat C ⨯ sp A ⟶ P M A :=
  pullback.lift prod.snd (prod.fst ≫ ofCatMap ρ) (by
    rw [comp_trivV]
    exact ((comp_trivV M (prod.fst : ofCat C ⨯ sp A ⟶ _)).symm.trans (congrArg _ hρ.symm)).trans (Category.assoc _ _ _).symm)

def lastU (N : ℕ) : ∀ {B : Type} [CommRing B], (Fin (N + 1) → B) → Prop := fun v => IsUnit (v (Fin.last N))

theorem lastU_map (N : ℕ) {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin (N + 1) → B) :
    lastU N v → lastU N (f ∘ v) := fun h => h.map f

def headU (N : ℕ) : ∀ {B : Type} [CommRing B], (Fin (N + 1) → B) → Prop :=
  fun v => Ideal.span (Set.range fun k : Fin N => v k.castSucc) = ⊤

theorem headU_map (N : ℕ) {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin (N + 1) → B) :
    headU N v → headU N (f ∘ v) := by
  intro h
  change Ideal.span (Set.range fun k : Fin N => f (v k.castSucc)) = ⊤
  rw [show (fun k : Fin N => f (v k.castSucc)) = f ∘ (fun k : Fin N => v k.castSucc) from rfl, Set.range_comp,
    ← Ideal.map_span, h, Ideal.map_top]

def trivialCondition (M : ℕ) : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop := fun _ => True

theorem allU_map (M : ℕ) {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B) :
    trivialCondition M v → trivialCondition M (f ∘ v) := fun _ => trivial

abbrev W1 (N : ℕ) (A : Type) [CommRing A] : Spc := ofCat (tuCat (N + 1) (lastU N) (lastU_map N)) ⨯ sp A

abbrev W2 (N : ℕ) (A : Type) [CommRing A] : Spc := ofCat (tuCat (N + 1) (headU N) (headU_map N)) ⨯ sp A

def w1 (N : ℕ) (A : Type) [CommRing A] : W1 N A ⟶ P (N + 1) A := toP (tuToPgl _ _ _) (tuToPgl_pr _ _ _) A

def w2 (N : ℕ) (A : Type) [CommRing A] : W2 N A ⟶ P (N + 1) A := toP (tuToPgl _ _ _) (tuToPgl_pr _ _ _) A

def headNat (N : ℕ) : tuCat (N + 1) (headU N) (headU_map N) ⟶ tuCat N (trivialCondition N) (allU_map N) where
  app B := Functor.toCatHom
    { obj := fun v => ⟨⟨fun k => v.1.1 k.castSucc, v.2⟩, trivial⟩
      map := fun {v w} u => ⟨u.1, funext fun k => congrFun u.2 k.castSucc⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  naturality _ _ _ := rfl

theorem headNat_pr (N : ℕ) : ofCatMap (headNat N ≫ tuToPgl N (trivialCondition N) (allU_map N)) ≫ PGL.pr N =
    trivV N (ofCat (tuCat (N + 1) (headU N) (headU_map N))) := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

def r (N : ℕ) (A : Type) [CommRing A] : W2 N A ⟶ P N A := toP _ (headNat_pr N) A

end GlobalTheory.EtC.PStep

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.PStep

noncomputable section
namespace GlobalTheory.EtC.ChartChern
open CochainComplex CochainComplex.HomComplex GlobalTheory.EtC.ClsSpec GlobalTheory.EtC.ChernSpec

set_option backward.isDefEq.respectTransparency false

theorem firstChernClass_eq_zero_of_unit_trivialization (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (s : ∀ U : Scheme.{0}, Sx E 0 U → (Γ(U, ⊤))ˣ)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 0 U), s V (x.res g) = umap g (s U x))
    (hL : ∀ (U : Scheme.{0}) (x : Sx E 1 U), s U (x.face 1) = lineUnit L x * s U (x.face 0)) :
    c1 q L = 0 := by
  obtain ⟨γ, hγ, h0, h1, h2s⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  have h2 := face_forms q L γ.1 h2s
  have hq0 : ∀ (U : Scheme.{0}) (_ : Sx E 0 U), IsUnit (q : Γ(U, ⊤)) := fun U x ↦ hE U ⟨x⟩
  have e2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
  rw [← hγ, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ 1 (by norm_num)]
  rcases kumT_cases q with ht | ht
  ·
    obtain ⟨a, ha_res, ha_d, ha⟩ := exists_d_family ht (p := 0) hq0 s hs
    obtain ⟨b, hb_res, hb⟩ := exists_two_family ht (p := 1) (fun U y ↦ hq0 U (y.face 0))
      (fun U y ↦ lineUnit L y) (fun U y ↦ s U (y.face 0)) (fun V U g y ↦ lineUnit_res L g y)
      (fun V U g y ↦ by rw [← face_res, hs])
    obtain ⟨β₀, hβ₀, hβ₀'⟩ := exists_single (E := E) (I := res _ (tw q 1)) (n := 1) 0 1 (by simp)
      (fun U x ↦ -a U x) (fun V U g x ↦ by rw [← ha_res]; exact map_neg _ _)
    obtain ⟨β₁, hβ₁, hβ₁'⟩ := exists_single (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp)
      b hb_res
    have K0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U),
        ev (δ 1 2 (β₀ + β₁)) 0 2 (by simp) U x = ev γ.1 0 2 (by simp) U x := by
      intro U x
      rw [CupSpec.ev_δ_zero (by norm_num) _ U 1 2 (by simp) (by simp) x, h0, ClsSpec.ev_add, hβ₀,
        hβ₁' 0 1 (by simp) U x (by norm_num), add_zero]
      have hd := ha_d U x
      simp only [Sec.map] at hd ⊢
      rw [map_neg, hd, neg_zero]
    have K1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
        w ^ q = s U (x.face 0) →
        ev (δ 1 2 (β₀ + β₁)) 1 1 (by simp) U x = ev γ.1 1 1 (by simp) U x := by
      intro U x v w hv hw
      have hvw : (v * w) ^ q = s U (x.face 1) := by rw [mul_pow, hv, hw, hL]
      rw [CupSpec.ev_δ_succ (by norm_num) _ U 0 0 1 (by simp) (by simp) x, h1 U x v hv,
        ClsSpec.ev_add, hβ₀' 1 0 (by simp) U x (by norm_num), hβ₁, smap_add, smap_zero, zero_add]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ClsSpec.ev_add, hβ₀, hβ₁',
        Fin.succ_zero_eq_one, ne_eq, zero_ne_one, not_false_eq_true]
      rw [hb U x v w hv hw, ha U _ w hw, ha U _ (v * w) hvw, e2]
      simp only [smap_add, smap_sub, add_zero, one_smul, Fin.val_zero, Fin.val_one,
        pow_zero, pow_one, neg_smul, neg_neg]
      abel
    have K1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev (δ 1 2 (β₀ + β₁)) 1 1 (by simp) U x = ev γ.1 1 1 (by simp) U x := by
      intro U x
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq0 U (x.face 0)) (lineUnit L x))
        (root_loc (hq0 U (x.face 0)) (s U (x.face 0)))) ?_
      rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      rw [CupSpec.ev_res, CupSpec.ev_res]
      exact K1' V (x.res g) v w (by rw [hv, lineUnit_res]) (by rw [hw, ← face_res, hs])
    have K2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w z : (Γ(U, ⊤))ˣ),
        v ^ q = lineUnit L (x.face 2) → w ^ q = lineUnit L (x.face 0) →
        z ^ q = s U ((x.face 0).face 0) →
        ev (δ 1 2 (β₀ + β₁)) 2 0 (by simp) U x = ev γ.1 2 0 (by simp) U x := by
      intro U x v w z hv hw hz
      have f10 : (x.face 1).face 0 = (x.face 0).face 0 :=
        face_face x 1 0 0 0 (SimplexCategory.δ_comp_δ (i := 0) (j := 0) le_rfl)
      have f20 : (x.face 2).face 0 = (x.face 0).face 1 :=
        face_face x 2 0 0 1 (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide))
      have hvw : (v * w) ^ q = lineUnit L (x.face 1) := by rw [mul_pow, hv, hw, lineUnit_face]
      have hz1 : z ^ q = s U ((x.face 1).face 0) := by rw [f10, hz]
      have hwz : (w * z) ^ q = s U ((x.face 2).face 0) := by rw [mul_pow, hw, hz, f20, hL]
      rw [CupSpec.ev_δ_succ (by norm_num) _ U 1 (-1) 0 (by simp) (by simp) x, h2 U x v w hv hw]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ClsSpec.ev_add, hβ₀', hβ₁,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, ne_eq, one_ne_zero, not_false_eq_true]
      rw [hb U _ w z hw hz, hb U _ (v * w) z hvw hz1, hb U _ v (w * z) hv hwz, e2, mul_assoc]
      simp only [zero_add, add_zero, one_smul, Fin.val_zero, Fin.val_one, Fin.val_two,
        pow_zero, pow_one, neg_smul]
      simp only [even_two, Even.neg_one_pow, one_smul]
      rw [hβ₀' 2 (-1) (by simp) U x (by norm_num), hβ₁' 2 (-1) (by simp) U x (by norm_num), add_zero,
        smap_zero, zero_add]
      abel
    have K2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U),
        ev (δ 1 2 (β₀ + β₁)) 2 0 (by simp) U x = ev γ.1 2 0 (by simp) U x := by
      intro U x
      have hU := hq0 U ((x.face 0).face 0)
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2)))
        (root_loc hU (lineUnit L (x.face 0)))) (root_loc hU (s U ((x.face 0).face 0)))) ?_
      rintro V g ⟨⟨⟨v, hv⟩, ⟨w, hw⟩⟩, ⟨z, hz⟩⟩
      rw [CupSpec.ev_res, CupSpec.ev_res]
      exact K2' V (x.res g) v w z (by rw [hv, ← face_res, lineUnit_res])
        (by rw [hw, ← face_res, lineUnit_res]) (by rw [hz, ← face_res, ← face_res, hs])
    refine ⟨β₀ + β₁, CupSpec.ev_ext _ _ fun p t ht' U x ↦ ?_⟩
    rcases p with _ | _ | _ | p
    · obtain rfl : t = 2 := by omega
      exact K0 U x
    · obtain rfl : t = 1 := by omega
      exact K1 U x
    · obtain rfl : t = 0 := by omega
      exact K2 U x
    · exact ChernSpec.sec_neg _ t (by omega) _ _
  ·
    have Z1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), (0 : Sec ((res _ (tw q 1)).X 1) U) =
        ev γ.1 1 1 (by simp) U x := by
      intro U x
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (root_loc (hq0 U (x.face 0)) (lineUnit L x)) ?_
      rintro V g ⟨v, hv⟩
      rw [CupSpec.ev_res, res_zero, h1 V (x.res g) v (by rw [hv, lineUnit_res]), ht]
      simp only [Pi.zero_apply, smap_zero]
    have Z2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U), (0 : Sec ((res _ (tw q 1)).X 0) U) =
        ev γ.1 2 0 (by simp) U x := by
      intro U x
      have hU := hq0 U ((x.face 0).face 0)
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2)))
        (root_loc hU (lineUnit L (x.face 0)))) ?_
      rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      rw [CupSpec.ev_res, res_zero, h2 V (x.res g) v w (by rw [hv, ← face_res, lineUnit_res])
        (by rw [hw, ← face_res, lineUnit_res]), ht]
      simp only [Pi.zero_apply, add_zero, sub_zero]
    refine ⟨0, ?_⟩
    rw [δ_zero]
    refine CupSpec.ev_ext _ _ fun p t ht' U x ↦ ?_
    rw [CupSpec.ev_zero]
    rcases p with _ | _ | _ | p
    · obtain rfl : t = 2 := by omega
      exact (h0 U x).symm
    · obtain rfl : t = 1 := by omega
      exact Z1 U x
    · obtain rfl : t = 0 := by omega
      exact Z2 U x
    · exact ChernSpec.sec_neg _ t (by omega) _ _

def vtx {N : ℕ} {U : Scheme.{0}} (x : Sx (ofCat (tuCat (N + 1) (lastU N) (lastU_map N))) 0 U) :
    TU (N + 1) (lastU N) Γ(U, ⊤) :=
  (show ComposableArrows (TU (N + 1) (lastU N) Γ(U, ⊤)) 0 from x).obj 0

end GlobalTheory.EtC.ChartChern

end
end
