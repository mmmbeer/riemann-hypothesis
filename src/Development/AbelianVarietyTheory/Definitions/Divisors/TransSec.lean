import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBX

abbrev Tor {K : Type} [Field K] (P : PolAV (Sp K)) (N : ℕ) : Type := {x : 𝟙_ (Over (Sp K)) ⟶ P.A // x ^ N = 1}

def TorFull {K : Type} [Field K] (P : PolAV (Sp K)) (N : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : K →+* Ω) (z : Over.mk (spMap f) ⟶ P.A), z ^ N = 1 →
    ∃ x : Tor P N, spMap f ≫ x.1.left = z.left

structure TGrp (R K : Type) [CommRing R] [Field K] [Algebra R K] (P : PolAV (Sp K)) (N : ℕ) : Type 1 where

  AA : Over (Sp R)
  [grp : GrpObj AA]
  [comm : IsCommMonObj AA]
  smooth : SmoothOfRelativeDimension P.g AA.hom
  sep : IsSeparated AA.hom
  qc : QuasiCompact AA.hom

  φ : P.A.left ⟶ AA.left
  fib : IsGrpPullback P.A AA (spMap (algebraMap R K)) φ

  G : Over (Sp R)
  [grpG : GrpObj G]
  [commG : IsCommMonObj G]
  semi : IsSemiAbelian G

  j : G ⟶ AA
  jhom : IsMonHom j
  jopen : IsOpenImmersion j.left

  φ₀ : P.A.left ⟶ G.left
  fac : φ₀ ≫ j.left = φ
  fib₀ : IsGrpPullback P.A G (spMap (algebraMap R K)) φ₀
  pos : 1 ≤ N
  full : TorFull P N

  τ : Tor P N → (𝟙_ (Over (Sp R)) ⟶ AA)
  τ_over : ∀ x, (x.1.left ≫ φ : Sp K ⟶ AA.left) = spMap (algebraMap R K) ≫ (τ x).left
  cover : ∀ z : AA.left, ∃ x, z ∈ Set.range ((toUnit G ≫ τ x) * j).left

attribute [instance] TGrp.grp TGrp.comm TGrp.grpG TGrp.commG

section Model

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {P : PolAV (Sp K)} {N : ℕ}

def TGrp.comp (m : TGrp R K P N) (σ : 𝟙_ (Over (Sp R)) ⟶ m.AA) : Set m.AA.left := Set.range ((toUnit m.G ≫ σ) * m.j).left

structure TBun (m : TGrp R K P N) (n : ℕ) where

  M : RigLB m.AA
  cub : Nonempty (CubicalStr m.AA M)

  w : LB.Iso (M.L.pull m.φ) (lbPow P.L n)
  gen : w.IsGen

end Model

section Lattice

variable {K : Type} [Field K] [NumberField K] {P : PolAV (Sp K)} {N n : ℕ} {m : TGrp (𝓞 K) K P N}

end Lattice

section Power

variable {S : Scheme.{0}}

def lin {A T : Over S} [GrpObj A] {k : ℕ} (v : Fin k → ℤ) (x : Fin k → (T ⟶ A)) : T ⟶ A :=
  (List.ofFn fun j => x j ^ v j).prod

end Power

section Iso

variable {K : Type} [Field K] [NumberField K] {P₁ P₂ : PolAV (Sp K)} {N n : ℕ} {m₁ : TGrp (𝓞 K) K P₁ N}
  {m₂ : TGrp (𝓞 K) K P₂ N}

end Iso

def Over₀ {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K''] [Algebra K K'']
    {P : PolAV (Sp K'')} {N : ℕ} (ψ : P.A.left ⟶ F.P₀.A.left) (m : TGrp (𝓞 K'') K'' P N) : Prop :=
  GlobalTheory.MBLow.IsOver F ψ m.φ₀

end GlobalTheory.MBX

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBX

def transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) : A.left ⟶ A.left := ((toUnit A ≫ x) * 𝟙 A).left

section Generic

variable {K : Type} [Field K] {P P₂ : PolAV (Sp K)} {n : ℕ}

def TransSec (x : 𝟙_ (Over (Sp K)) ⟶ P.A) (s s' : (lbPow P.L n).Sec) : Prop :=
  ∃ io : LB.Iso ((lbPow P.L n).pull (transl x)) (lbPow P.L n), io.IsGen ∧ SecMaps io (secPull s (transl x)) s'

end Generic

section Model

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {P P₂ : PolAV (Sp K)} {N N₂ n : ℕ}

end Model

end GlobalTheory.MBX

end
end
