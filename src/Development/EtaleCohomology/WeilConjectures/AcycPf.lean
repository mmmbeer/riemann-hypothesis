import Development.EtaleCohomology.WeilConjectures.FermatCount
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
import Development.EtaleCohomology.KummerTheory.InjSlice

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)

namespace LateralTheory.EWeil.ArtinCut

def Van (q : ℕ) (D : CommRingCat.{0}) (n : ℤ) : Prop := ∀ i : ℤ, Subsingleton (Ht q (sch.obj (Spec D)) n i)

def Const (d : ℕ) : Prop := ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ (A : Type) [CommRing A] [Algebra Ω A] [Algebra.FiniteType Ω A], ringKrullDim A ≤ d →
  ∀ n : ℤ, (d : ℤ) < n → Van q (CommRingCat.of A) n

def IsStalk {A S : CommRingCat.{0}} (f : A ⟶ S) (p : PrimeSpectrum A) : Prop :=
  IE f ∧ SH S ∧ ∀ a : A, a ∈ p.asIdeal ↔ ¬ IsUnit (f.hom a)

instance (X : Scheme.{0}) : HasSheafify X.smallEtaleTopology AddCommGrpCat.{1} := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := by
  have : EssentiallySmall.{1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

instance (X : Scheme.{0}) : HasExt.{1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{1}) := inferInstance

abbrev Sm (A : CommRingCat.{0}) : Type 2 := Sheaf (Spec A).smallEtaleTopology AddCommGrpCat.{1}

def StalkZero {A : CommRingCat.{0}} (F : Sm A) (p : PrimeSpectrum A) : Prop :=
  ∀ (V : (Spec A).Etale) (v : V.left), V.hom v = p → ∀ s : F.obj.obj (op V),
    ∃ (W : (Spec A).Etale) (g : W ⟶ V) (w : W.left), g.left w = v ∧ (F.obj.map g.op).hom s = 0

def SmallCd (q : ℕ) (A : CommRingCat.{0}) (δ : PrimeSpectrum A → ℕ∞) : Prop :=
  ∀ F : Sm A, (∀ (V : (Spec A).Etale) (s : F.obj.obj (op V)), q • s = 0) → ∀ a : ℕ,
    (∀ p, (a : ℕ∞) < δ p → StalkZero F p) → ∀ n : ℕ, a < n → Subsingleton (Sheaf.H.{1} F n)

def Fibre : Prop := ∀ (Ω : Type) [Field Ω] (e : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin e) Ω)),
  ∃ (a c : ℕ) (y : MvPolynomial (Fin a) Ω →ₐ[Ω] MvPolynomial (Fin e) Ω), a + c = e ∧ Order.coheight p ≤ a ∧
    (∀ g, y g ∈ p.asIdeal → g = 0) ∧
    ∀ (K : Type) [Field K] (κ : MvPolynomial (Fin a) Ω →+* K), Function.Injective κ →
    ∀ (D : CommRingCat.{0}) (u : CommRingCat.of (MvPolynomial (Fin e) Ω) ⟶ D) (v : CommRingCat.of K ⟶ D),
      IsPushout (CommRingCat.ofHom y.toRingHom) (CommRingCat.ofHom κ) u v → ringKrullDim D ≤ c

def Leray : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) →
  ∀ (δ : PrimeSpectrum A → ℕ∞) (d : ℕ), SmallCd q A δ →
  (∀ (p : PrimeSpectrum A) (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D), IsStalk f p → IsPushout β f u v →
    ∀ m : ℕ, (d : ℕ∞) < m + δ p → Van q D m) →
  ∀ n : ℤ, (d : ℤ) < n → Van q B n

def Low : Prop := Base → Const 0 ∧ Const 1

def Step : Prop := Base → ∀ e : ℕ, 1 ≤ e → (∀ b ≤ e, Const b) → Const (e + 1)

def Final : Prop := (Base → ∀ d, Const d) → Artin

theorem goal_of (h1 : Low) (h2 : Step) (h3 : Final) : Artin := by
  refine h3 fun hb d => ?_
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, ih with
    | 0, _ => exact (h1 hb).1
    | 1, _ => exact (h1 hb).2
    | e + 2, ih => exact h2 hb (e + 1) (by omega) fun b hb' => ih b (by omega)

end LateralTheory.EWeil.ArtinCut

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)
open LateralTheory.EWeil.ArtinCut

namespace LateralTheory.EWeil.LerayCut

universe u v w

abbrev gam {C : Type u} [Category.{v} C] [Preadditive C] (U : C) : C ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (op U)

abbrev gamCx {C : Type u} [Category.{v} C] [Preadditive C] (U : C) (K : CochainComplex C ℕ) :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((gam U).mapHomologicalComplex _).obj K

abbrev unitSh (A : CommRingCat.{0}) : Sm A :=
  (constantSheaf (Spec A).smallEtaleTopology AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ))

def Hyper : Prop := ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasExt.{w} C] (U : C) (K : CochainComplex C ℕ) (d : ℕ),
  (∀ s n : ℕ, 0 < n → Subsingleton (Abelian.Ext U (K.X s) n)) →
  (∀ j m : ℕ, d < j + m → Subsingleton (Abelian.Ext U (K.homology m) j)) →
  ∀ n : ℕ, d < n → Subsingleton ((gamCx U K).homology n)

def ZeroSheaf : Prop := ∀ (A : CommRingCat.{0}) (F : Sm A), (∀ p : PrimeSpectrum A, StalkZero F p) →
  ∀ n : ℕ, Subsingleton (Sheaf.H.{1} F n)

def Push : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) → ∀ i : ℤ,
  ∃ K : CochainComplex (Sm A) ℕ,
    (∀ s n : ℕ, 0 < n → Subsingleton (Sheaf.H.{1} (K.X s) n)) ∧
    (∀ (m : ℕ) (V : (Spec A).Etale) (x : (K.homology m).obj.obj (op V)), q • x = 0) ∧
    (∀ (p : PrimeSpectrum A) (m : ℕ), (∀ (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D),
        IsStalk f p → IsPushout β f u v → Van q D m) → StalkZero (K.homology m) p) ∧
    ∀ n : ℕ, Nonempty (Ht q (sch.obj (Spec B)) n i ≃ (gamCx (unitSh A) K).homology n)

example (A : CommRingCat.{0}) (F : Sm A) (n : ℕ) : Sheaf.H.{1} F n = Abelian.Ext (unitSh A) F n := rfl

lemma enat_lt_add_of_sub_lt (d m : ℕ) (x : ℕ∞) (hm : m ≤ d) (h : ((d - m : ℕ) : ℕ∞) < x) : (d : ℕ∞) < (m : ℕ∞) + x := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe x =>
    have : d - m < x := by exact_mod_cast h
    exact_mod_cast (by omega : d < m + x)

lemma enat_lt_add_of_lt (d m : ℕ) (x : ℕ∞) (hm : d < m) : (d : ℕ∞) < (m : ℕ∞) + x :=
  lt_of_lt_of_le (by exact_mod_cast hm) le_self_add

theorem goal_of (hH : Hyper.{2, 1, 1}) (hZ : ZeroSheaf) (hP : Push) : LateralTheory.EWeil.ArtinCut.Leray := by
  intro base q _ A B β hq δ d hsm hst n hn i
  obtain ⟨K, hacy, htor, hstalk, hiso⟩ := hP base q β hq i
  have hn0 : (0 : ℤ) ≤ n := by omega
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  have hdN : d < N := by omega
  obtain ⟨e⟩ := hiso N
  have key : Subsingleton ((gamCx (unitSh A) K).homology N) := by
    refine hH (Sm A) (unitSh A) K d (fun s k hk => hacy s k hk) ?_ N hdN
    intro j m hjm
    by_cases hm : m ≤ d
    · refine hsm (K.homology m) (htor m) (d - m) ?_ j (by omega)
      intro p hp
      exact hstalk p m (fun S D f u v hf hpo => hst p S D f u v hf hpo m (enat_lt_add_of_sub_lt d m _ hm hp))
    · refine hZ A (K.homology m) (fun p => ?_) j
      exact hstalk p m (fun S D f u v hf hpo => hst p S D f u v hf hpo m (enat_lt_add_of_lt d m _ (by omega)))
  exact e.subsingleton

end LateralTheory.EWeil.LerayCut
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut

namespace LateralTheory.EWeil.PushPf

abbrev bmap {A B : CommRingCat.{0}} (β : A ⟶ B) {W' W : (Spec A).Etale} (g : W' ⟶ W) :
    pullback W'.hom (Spec.map β) ⟶ pullback W.hom (Spec.map β) :=
  pullback.map _ _ _ _ g.left (𝟙 _) (𝟙 _) (by simp [MorphismProperty.Over.w g]) (by simp)

def LocCls (q : ℕ) {A B : CommRingCat.{0}} (β : A ⟶ B) (i : ℤ) (F : Sm A) (m : ℕ) : Prop :=
  ∀ (V : (Spec A).Etale) (s : F.obj.obj (op V)) (v : V.left),
    ∃ (W : (Spec A).Etale) (g : W ⟶ V) (w : W.left), g.left w = v ∧
      ∃ c : Ht q (sch.obj (pullback W.hom (Spec.map β))) (m : ℤ) i,
        ∀ (W' : (Spec A).Etale) (g' : W' ⟶ W) (w' : W'.left), g'.left w' = w →
          pull _ (sch.map (bmap β g')) _ _ c = 0 →
          ∃ (W'' : (Spec A).Etale) (g'' : W'' ⟶ W') (w'' : W''.left), g''.left w'' = w' ∧
            (F.obj.map (g'' ≫ g' ≫ g).op).hom s = 0

end LateralTheory.EWeil.PushPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut LateralTheory.EWeil.PushPf

namespace LateralTheory.EWeil.PushCxTPf

def tot {A B : CommRingCat.{0}} (β : A ⟶ B) : (Spec A).Etale ⥤ Scheme.{0} :=
  MorphismProperty.Over.forget _ _ _ ⋙ Over.pullback (Spec.map β) ⋙ Over.forget _

def pushP {R : Type} [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R) :
    ((Spec A).Etale)ᵒᵖ ⥤ AddCommGrpCat.{1} :=
  (tot β).op ⋙ F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} R)) AddCommGrpCat.{1}

example {R : Type} [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R) (V : (Spec A).Etale) :
  (pushP β F).obj (op V) = AddCommGrpCat.of (F.obj.obj (op (pullback V.hom (Spec.map β)))) := rfl

def SheafP : Prop := ∀ (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) (F : Shv R),
  Presheaf.IsSheaf (Spec A).smallEtaleTopology (pushP β F)

def pushF (hS : SheafP) (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) : Shv R ⥤ Sm A where
  obj F := ⟨pushP β F, hS R β F⟩
  map φ := ⟨Functor.whiskerRight (Functor.whiskerLeft (tot β).op φ.hom) (forget₂ _ _)⟩

instance (hS : SheafP) (R : Type) [CommRing R] {A B : CommRingCat.{0}} (β : A ⟶ B) : (pushF hS R β).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

def Kc (hS : SheafP) (q : ℕ) {A B : CommRingCat.{0}} (β : A ⟶ B) (i : ℤ) : CochainComplex (Sm A) ℕ :=
  ((pushF hS (ZMod q) β).mapHomologicalComplex _).obj
    ((res (ZMod q) (tw q i)).restriction ComplexShape.embeddingUpNat)

def Loc : Prop := Base → LateralTheory.KummerTheory.Dict → ∀ (hS : SheafP) (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B),
  IsUnit (q : A) → ∀ (i : ℤ) (m : ℕ), LocCls q β i ((Kc hS q β i).homology m) m

end LateralTheory.EWeil.PushCxTPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut LateralTheory.EWeil.PushPf LateralTheory.EWeil.PushCxTPf

namespace LateralTheory.EWeil.AcycPf

def incl (S : Scheme.{0}) : S.Etale ⥤ Over S := MorphismProperty.Over.forget _ _ _

def RestrInj : Prop := ∀ (R : Type) [CommRing R] (S : Scheme.{0})
  (G : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))) [Injective G],
  ∃ h : Presheaf.IsSheaf S.smallEtaleTopology ((incl S).op ⋙ G.val),
    Injective (⟨_, h⟩ : Sheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R)))

end LateralTheory.EWeil.AcycPf
end
end
