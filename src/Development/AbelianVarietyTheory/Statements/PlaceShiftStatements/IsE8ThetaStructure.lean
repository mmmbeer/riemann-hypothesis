import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

def ThetaOn {S : Scheme.{0}} (G : Over S) (L : LB G.left) (δ : LB S) : Prop :=
  δ.IsLB ∧ ∃ σ : (CechPic.tens L (δ.pull G.hom)).Sec,
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (y : Sp K ⟶ G.left) (j : (CechPic.tens L (δ.pull G.hom)).ι),
      y ≫ G.hom = x ∧ valF y _ (σ.f j) ≠ 0

def SameAbPart {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (x y : Sp K ⟶ S) : Prop :=
  ∃ (E E' : SplitExt (Sp K)) (φ : E.B ≅ E'.B), E.IsGt ((Over.pullback x).obj G) ∧ E'.IsGt ((Over.pullback y).obj G) ∧
    Module.finrank ℤ E.X = Module.finrank ℤ E'.X ∧ IsMonHom φ.hom

def IsFormBundleOn {X S T : Scheme.{0}} {A : Over X} (P : LB (G2 A).left) {G H : Over S} (U : S.Opens) (α : T ⟶ A.left)
    (e : T ⟶ G.left) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (H ⟶ G)) (L : LB H.left) : Prop :=
  ∃ (p : Fin r → ((H.hom ⁻¹ᵁ U).toScheme ⟶ T)) (q : Fin r × Fin r → ((H.hom ⁻¹ᵁ U).toScheme ⟶ (G2 A).left)),
    (∀ u, p u ≫ e = (H.hom ⁻¹ᵁ U).ι ≫ (pr u).left) ∧
    (∀ uv, q uv ≫ (fst A A).left = p uv.1 ≫ α ∧ q uv ≫ (snd A A).left = p uv.2 ≫ α) ∧
    LBIso (L.pull (H.hom ⁻¹ᵁ U).ι) (LB.LinComb P q fun uv => W uv.1 uv.2)

def IsE8ThetaStructure {X S T : Scheme.{0}} {A : Over X} (P : LB (G2 A).left) (G : Over S) [GrpObj G] (U : S.Opens)
    (α : T ⟶ A.left) (e : T ⟶ G.left) (δ : LB S) : Prop :=
  ∃ (W : Matrix (Fin 8) (Fin 8) ℤ) (H : Over S) (_ : GrpObj H) (_ : IsCommMonObj H) (pr : Fin 8 → (H ⟶ G)) (L : RigLB H),
    IsE8 W ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (Y : Over S) (y : Fin 8 → (Y ⟶ G)), ∃! x : Y ⟶ H, ∀ u, x ≫ pr u = y u) ∧
    L.IsSymmetric ∧ Nonempty (CubicalStr H L) ∧ IsFormBundleOn P U α e W pr L.L ∧ ThetaOn H L.L δ

end GlobalTheory.SiegMin
