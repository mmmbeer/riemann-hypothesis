import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayHoriz

section Jet

variable {S : Type} [CommRing S] {ρ : Type}

def jetW {K : Type} [Fintype K] (w : K → ρ → S) (m : ℕ) : Jet S ρ m →ₐ[S] Jet S (K × ρ) m :=
  jetMap (fun r => ∑ i, MvPolynomial.C (w i r) * MvPolynomial.X (i, r)) fun r =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (X_mem_orig (i, r))

end Jet

section Frames

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left)
  (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))

structure IsRigFr (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m y J, Good L y J →
    val (e (m + 1)) (homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m)).left y J = val (e m) (𝟙 _) y J
  zero : ∀ y J, Good L y J → val (e 0) (homAt x0 (jetAug : Jet S ρ 0 →ₐ[S] S)).left y J = val rig x0 y J

def ev {K : Type} [Fintype K] {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (w : K → ρ → S) (m : ℕ)
    (y : (overAt x0 (Jet S (K × ρ) m)).left) (J : ((overAt x0 (Jet S (K × ρ) m)).left ⟶ G.left) → L.ι) :
    ((overAt x0 (Jet S (K × ρ) m)).left.presheaf.stalk y)ˣ :=
  val (e m) (homAt x0 (jetW w m)).left y J

def pt2 (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) : overAt x0 (Jet S (Fin 2 × ρ) m) ⟶ G ⊗ G :=
  lift (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)

def pt3 (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) : overAt x0 (Jet S (Fin 3 × ρ) m) ⟶ G3 G :=
  lift (homAt x0 (jetIn (0 : Fin 3)) ≫ x m)
    (lift (homAt x0 (jetIn (1 : Fin 3)) ≫ x m) (homAt x0 (jetIn (2 : Fin 3)) ≫ x m))

def ThetaIs (t : LB.Gen (Theta G L)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop :=
  ∀ m y J, Good L y J → val t (pt3 x0 x m).left y J =
    ∏ I : Finset (Fin 3), val (e m) (homAt x0 (jetSum I : Jet S ρ m →ₐ[S] Jet S (Fin 3 × ρ) m)).left y J ^
      ((-1 : ℤ) ^ (3 - I.card))

end Frames

end GlobalTheory.RayHoriz
