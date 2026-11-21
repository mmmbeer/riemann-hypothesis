import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EDual

def Base : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧
  B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ DivisorPicardCompatibility ∧ B6h1 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ D1 ∧ E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6

abbrev pt (k : Type) [Field k] : Scheme.{0} := Spec (CommRingCat.of k)

abbrev ptMap {k : Type} [Field k] (σ : k ≃+* k) : pt k ⟶ pt k := Spec.map (CommRingCat.ofHom σ.toRingHom)

structure SP (k : Type) [Field k] (d : ℕ) where
  X : Scheme.{0}
  p : X ⟶ pt k
  proper : IsProper p
  smooth : SmoothOfRelativeDimension d p

structure Cpt (k : Type) [Field k] (d : ℕ) where
  X : Scheme.{0}
  Z : Scheme.{0}
  U : Scheme.{0}
  p : X ⟶ pt k
  ι : Z ⟶ X
  j : U ⟶ X
  proper : IsProper p
  closed : IsClosedImmersion ι
  opn : IsOpenImmersion j
  compl : IsCompl (Set.range ι) (Set.range j)
  smooth : SmoothOfRelativeDimension d (j ≫ p)

def Cpt.Q {k : Type} [Field k] {d : ℕ} (C : Cpt k d) : Spc := pushout (sch.map C.ι) (sch.map (C.ι ≫ C.p))

def Cpt.q {k : Type} [Field k] {d : ℕ} (C : Cpt k d) : C.Q ⟶ sch.obj (pt k) :=
  pushout.desc (sch.map C.p) (𝟙 _) (by rw [Category.comp_id, Functor.map_comp])

structure Cpt.Hom {k : Type} [Field k] {d : ℕ} (C' C : Cpt k d) where
  σ : k ≃+* k
  f : C'.X ⟶ C.X
  z : C'.Z ⟶ C.Z
  u : C'.U ⟶ C.U
  hp : f ≫ C.p = C'.p ≫ ptMap σ
  hz : C'.ι ≫ f = z ≫ C.ι
  hu : C'.j ≫ f = u ≫ C.j

def Cpt.Hom.Q {k : Type} [Field k] {d : ℕ} {C' C : Cpt k d} (φ : Cpt.Hom C' C) : C'.Q ⟶ C.Q :=
  pushout.map _ _ _ _ (sch.map φ.f) (sch.map (ptMap φ.σ)) (sch.map φ.z)
    (by rw [← Functor.map_comp, ← Functor.map_comp, φ.hz])
    (by rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, ← φ.hp, ← Category.assoc, φ.hz, Category.assoc])

def lev {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (a : Hl l E n i) (m : ℕ) : Ht (l ^ m) E n i := a.1 m

def PointClasses (k : Type) [Field k] : Prop := ∀ d : ℕ,
  ∃ cl : ∀ (q : ℕ) (X : SP k d), X.X → Ht q (sch.obj X.X) (2 * d) d,
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (X : SP k d), IsIntegral X.X → ∀ x : X.X, IsClosed ({x} : Set X.X) →
      Function.Bijective (fun m : ZMod q => m • cl q X x) ∧ ∀ y : X.X, IsClosed ({y} : Set X.X) → cl q X y = cl q X x) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (Y X : SP k d) (σ : k ≃+* k) (f : Y.X ⟶ X.X), f ≫ X.p = Y.p ≫ ptMap σ →
      ∀ (V : X.X.Opens), Etale (f ∣_ V) → ∀ x : X.X, x ∈ V → IsClosed ({x} : Set X.X) → ∀ s : Finset Y.X,
        (s : Set Y.X) = f ⁻¹' {x} → pull _ (sch.map f) _ _ (cl q X x) = ∑ y ∈ s, cl q Y y) ∧
    ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → IsUnit (Q : k) → ∀ (X : SP k d) (x : X.X), IsClosed ({x} : Set X.X) →
      red Q q _ _ _ (cl Q X x) = cl q X x

def AdicFin : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), Inv l E → (∀ m n, Finite (Ht (l ^ m) E n i)) →
  ∀ n, Module.Finite ℤ_[l] (Hl l E n i) ∧ ∃ c : ℕ, ∀ (m : ℕ) (x : Ht (l ^ m) E n i), ∃ y : Hl l E n i, lev y m = l ^ c • x

end LateralTheory.EDual
end
