import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

noncomputable section

namespace GlobalTheory.Frames.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Ring

variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]

abbrev Var : Type := (Σ τ : J, Fin (m τ) × Fin (m τ)) ⊕ J ⊕ Bool

def genMat (τ : J) : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Var m) R) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl ⟨τ, i, j⟩)

def rel : Ideal (MvPolynomial (Var m) R) :=
  Ideal.span (Set.range (fun τ : J => (genMat m R τ).det * MvPolynomial.X (Sum.inr (Sum.inl τ)) - 1) ∪
    {MvPolynomial.X (Sum.inr (Sum.inr true)) * MvPolynomial.X (Sum.inr (Sum.inr false)) - 1})

abbrev GlRing : Type := MvPolynomial (Var m) R ⧸ rel m R

def glπ : R →ₐ[K] GlRing m R := (Ideal.Quotient.mkₐ K (rel m R)).comp (IsScalarTower.toAlgHom K R _)

def glX (τ : J) : Matrix (Fin (m τ)) (Fin (m τ)) (GlRing m R) := (genMat m R τ).map (Ideal.Quotient.mk (rel m R))

theorem unit_rel : Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr true))) *
    Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr false))) = 1 := by
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (rel m R)), Ideal.Quotient.eq]
  unfold rel
  exact Ideal.subset_span (Set.mem_union_right _ rfl)

theorem det_rel (τ : J) : (glX m R τ).det *
    Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inl τ))) = 1 := by
  unfold glX
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_mul, ← map_one (Ideal.Quotient.mk (rel m R)),
    Ideal.Quotient.eq]
  unfold rel
  exact Ideal.subset_span (Set.mem_union_left _ ⟨τ, rfl⟩)

def glS : (GlRing m R)ˣ := Units.mkOfMulEqOne _ _ (unit_rel m R)


variable {m R}

theorem FrameRing.injective {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) : Function.Injective π := by
  intro r₁ r₂ hr
  obtain ⟨k, ⟨hk, -, -⟩, -⟩ := h.2 R (AlgHom.id K R) (fun _ => 1) 1 (fun _ => by simp)
  have e₁ := AlgHom.congr_fun hk r₁
  have e₂ := AlgHom.congr_fun hk r₂
  rw [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
  rw [← e₁, ← e₂, hr]


theorem FrameRing.triRing {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) :
    let I : Ideal A := Ideal.span {x | ∃ τ i j, i < j ∧ x = X τ i j}
    TriRing m ((Ideal.Quotient.mkₐ K I).comp π) (fun τ => (X τ).map (Ideal.Quotient.mk I))
      (Units.map (Ideal.Quotient.mk I).toMonoidHom s) := by
  intro I
  have hX : ∀ τ i j, i < j → Ideal.Quotient.mk I (X τ i j) = 0 := fun τ i j hij =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨τ, i, j, hij, rfl⟩)
  refine ⟨fun τ i => ?_, fun τ i j hij => hX τ i j hij, ?_⟩
  ·
    have hd : IsUnit ((X τ).map (Ideal.Quotient.mk I)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (h.1 τ).map _
    rw [Matrix.det_of_isLowerTriangular _ (by intro i j hij; exact hX τ i j hij)] at hd
    exact IsUnit.prod_univ_iff.1 hd i
  · intro T _ _ ψ g a hd hl
    have hg : ∀ τ, IsUnit (g τ).det := fun τ => by
      rw [Matrix.det_of_isLowerTriangular _ (by intro i j hij; exact hl τ i j hij)]
      exact IsUnit.prod_univ_iff.2 (hd τ)
    obtain ⟨k, ⟨hk1, hk2, hk3⟩, hku⟩ := h.2 T ψ g a hg
    have hkX : ∀ τ i j, k (X τ i j) = g τ i j := fun τ i j => congrFun (congrFun (hk2 τ) i) j
    have hle : I ≤ RingHom.ker (k : A →+* T) := by
      apply Ideal.span_le.2
      rintro _ ⟨τ, i, j, hij, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact (hkX τ i j).trans (hl τ i j hij)
    have hI : ∀ x ∈ I, k x = 0 := fun x hx => RingHom.mem_ker.1 (hle hx)
    refine ⟨Ideal.Quotient.liftₐ I k hI, ⟨?_, fun τ => ?_, hk3⟩, ?_⟩
    · ext r
      exact AlgHom.congr_fun hk1 r
    · ext i j
      exact hkX τ i j
    · rintro k' ⟨h1, h2, h3⟩
      apply Ideal.Quotient.algHom_ext
      rw [Ideal.Quotient.liftₐ_comp]
      apply hku
      refine ⟨?_, fun τ => ?_, h3⟩
      · rw [AlgHom.comp_assoc]
        exact h1
      · ext i j
        exact congrFun (congrFun (h2 τ) i) j

end Ring

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_id (S : Type) [CommRing S] : spMap (RingHom.id S) = 𝟙 (Sp S) := Spec.map_id _


theorem chart_le {S T : Type} [CommRing S] [CommRing T] (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (pm : Gx x' ⟶ Gx x)
    (h : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : p ∈ ⋂ k, ⇑(snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) := hp
  have e : ∀ q, (snd (Over.mk x) Xo.univ.t.G).left (pm q) = (snd (Over.mk x') Xo.univ.t.G).left q := fun q => by
    rw [← h]
    rfl
  show pm p ∈ ⋂ k, ⇑(snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  rw [Set.mem_preimage, e]
  exact Set.mem_iInter.1 hp' k

theorem scal_one {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  unfold scal Out.liftFun
  simp only [map_one]


theorem frBor_iff {S : Type} [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) :
    FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  unfold FrBor FrChg SecBC
  simp only [spMap_id]
  constructor
  · rintro ⟨hx, hu, hs⟩
    choose cf hcf using hu
    exact ⟨fun τ => Matrix.of (cf τ), fun τ i => (hcf τ i).1, fun τ i j hij => (hcf τ i).2.1 j hij, hx,
      fun τ i => (hcf τ i).2.2, hs⟩
  · rintro ⟨g, hd, hl, hx, hu, hs⟩
    exact ⟨hx, fun τ i => ⟨g τ i, hd τ i, fun j hij => hl τ i j hij, hu τ i⟩, hs⟩

theorem appLE_id_apply (X : Scheme.{0}) (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (z : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom z = z := by
  show ((𝟙 X : X ⟶ X).appLE U ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) le_rfl).hom z = z
  rw [Scheme.Hom.appLE_eq_app]
  simp
  rfl

theorem secBC_id_iff {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s s' : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s s' ↔ ∀ i, s'.f i = scal x a i * s.f i := by
  have hid : (fst (Over.mk x) Xo.univ.t.G).left ≫ spMap (RingHom.id S) = (fst (Over.mk x) Xo.univ.t.G).left := by
    rw [spMap_id]
    exact Category.comp_id _

  have hpm : ∀ pm : Gx x ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left →
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ≫ spMap (RingHom.id S) →
      pm = 𝟙 _ := by
    intro pm h₁ h₂
    rw [hid] at h₂
    exact pullback.hom_ext (h₂.trans (Category.id_comp _).symm) (h₁.trans (Category.id_comp _).symm)
  constructor
  · rintro ⟨pm, h₁, h₂, h₃⟩ i
    obtain rfl := hpm pm h₁ h₂
    exact ((appLE_id_apply _ _ _ _).symm.trans (h₃ i le_rfl)).symm
  · intro hs
    refine ⟨𝟙 _, Category.id_comp _, (Category.id_comp _).trans hid.symm, fun i h => ?_⟩
    exact (appLE_id_apply _ _ _ _).trans (hs i).symm

private theorem secBC_unique_of_secGen {S : Type} [CommRing S] (x x' : Sp S ⟶ Xo.X) (hx : x' = x) {a b : S}
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (ha : SecBC (RingHom.id S) a x x' s s')
    (hb : SecBC (RingHom.id S) b x x' s s') (hgen : SecGen x s) : a = b := by
  subst x'
  rw [secBC_id_iff] at ha hb
  exact (hgen s').unique ha hb

theorem frChg_unique {S : Type} [CommRing S] [Algebra c.F S]
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a a' : S} {y y' : FrPt Xo c S}
    (h : FrChg g a y y') (h' : FrChg g' a' y y') : g = g' ∧ a = a' := by
  unfold FrChg at h h'
  obtain ⟨hx, hu, hs⟩ := h
  obtain ⟨-, hu', hs'⟩ := h'
  refine ⟨funext fun τ => Matrix.ext fun i j => congrFun ((y.basis τ _ (by rw [← hx]; exact y'.tan τ i)
    (y'.eig τ i)).unique (hu τ i) (hu' τ i)) j, secBC_unique_of_secGen y.x y'.x hx y.s y'.s hs hs' y.gen⟩

private theorem exists_secBC_of_secGen {S : Type} [CommRing S] (x x' : Sp S ⟶ Xo.X) (hx : x' = x)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (hgen : SecGen x s) :
    ∃ a, SecBC (RingHom.id S) a x x' s s' := by
  subst x'
  obtain ⟨a, ha, -⟩ := hgen s'
  exact ⟨a, (secBC_id_iff x a s s').2 ha⟩

theorem exists_frChg {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (h : y'.x = y.x) :
    ∃ g a, FrChg g a y y' := by
  choose g hg using fun τ i => (y.basis τ (y'.u τ i) (by rw [← h]; exact y'.tan τ i) (y'.eig τ i)).exists
  obtain ⟨a, ha⟩ := exists_secBC_of_secGen y.x y'.x h y.s y'.s y.gen
  refine ⟨fun τ => Matrix.of (g τ), a, ?_⟩
  unfold FrChg
  exact ⟨h, fun τ i => hg τ i, ha⟩

theorem scal_mul {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  unfold scal Out.liftFun
  simp only [map_mul]

private theorem isUnit_of_secBC_of_secGen {S : Type} [CommRing S] (x x' : Sp S ⟶ Xo.X) (hx : x' = x) {a : S}
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (hs : SecBC (RingHom.id S) a x x' s s')
    (hgen : SecGen x s) (hgen' : SecGen x' s') : IsUnit a := by
  subst x'
  rw [secBC_id_iff] at hs
  obtain ⟨b, hb, -⟩ := hgen' s
  have h₁ : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
    calc s.f i = scal x b i * s'.f i := hb i
      _ = scal x b i * (scal x a i * s.f i) := by rw [hs i]
      _ = scal x (b * a) i * s.f i := by rw [scal_mul, _root_.mul_assoc]
  have h₂ : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, _root_.one_mul]
  exact IsUnit.of_mul_eq_one_right b ((hgen s).unique h₁ h₂)

theorem FrChg.isUnit {S : Type} [CommRing S] [Algebra c.F S]
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S} {y y' : FrPt Xo c S}
    (h : FrChg g a y y') : IsUnit a := by
  unfold FrChg at h
  exact isUnit_of_secBC_of_secGen y.x y'.x h.1 y.s y'.s h.2.2 y.gen y'.gen

end Geo

end GlobalTheory.Frames.Model
