import Mathlib
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

namespace Formalism.MainNotions.DIV.Cons

universe u

attribute [local instance] CategoryTheory.Hom.group

abbrev GrpSch (S : Scheme.{u}) : Type (u + 1) := Grp (Over S)

def IsAbSch {S : Scheme.{u}} (A : GrpSch S) : Prop :=
  IsCommMonObj A.X ∧ IsProper A.X.hom ∧ Smooth A.X.hom ∧ GeometricallyConnected A.X.hom

def bchG {S T : Scheme.{u}} (f : T ⟶ S) (A : GrpSch S) : GrpSch T :=
  (Over.pullback f).mapGrp.obj A

def nMul {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : A.X ⟶ A.X := (𝟙 A.X) ^ N

def tors {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : Over S :=
  pullback (nMul A N) (MonObj.one : 𝟙_ (Over S) ⟶ A.X)

structure RAct (R : Type) [Ring R] {S : Scheme.{u}} (A : GrpSch S) where
  act : R → (A.X ⟶ A.X)
  hom : ∀ a, IsMonHom (act a)
  map_one : act 1 = 𝟙 A.X
  map_mul : ∀ a b, act (a * b) = act b ≫ act a
  map_add : ∀ a b, act (a + b) = act a * act b

def fibreAt {Z : Scheme.{u}} (A : GrpSch Z) (x : Z) : GrpSch (Spec (Z.residueField x)) :=
  bchG (Z.fromSpecResidueField x) A

def AbelianAt {Z : Scheme.{u}} (A : GrpSch Z) (x : Z) : Prop := IsAbSch (fibreAt A x)

structure ModelG (O : Type u) [CommRing O] [IsLocalRing O] where
  Z : Scheme.{u}
  str : Z ⟶ Spec (CommRingCat.of O)
  G : GrpSch Z

def ModelG.spf {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) : Scheme.{u} :=
  M.str.fiber (IsLocalRing.closedPoint O)

def ModelG.Gen {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) : Type u :=
  ↥(irreducibleComponents M.spf)

def ModelG.gpt {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) (η : M.Gen) : M.Z :=
  M.str.fiberι _ (η.2.1.genericPoint)

def ModelG.abAt {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) (η : M.Gen) : Prop :=
  AbelianAt M.G (M.gpt η)

end Formalism.MainNotions.DIV.Cons
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace Formalism.MainNotions.DIV.Cons

abbrev BigT : Type := Set (Set ℝ)

structure SCF (p : ℕ) where
  S : Set BigT
  [fld : NontriviallyNormedField S]
  [ultra : IsUltrametricDist S]
  [ac : IsAlgClosed S]
  [cpl : CompleteSpace S]
  [ch0 : CharZero S]
  norm_p : ‖(p : S)‖ = (p : ℝ)⁻¹

attribute [instance] SCF.fld SCF.ultra SCF.ac SCF.cpl SCF.ch0

def SCF.toCF {p : ℕ} (c : SCF p) : Formalism.MainNotions.ModuliIntegralCharts.CF p where
  C := c.S
  norm_p := c.norm_p

def intO (C : Type) [NormedField C] [IsUltrametricDist C] : Subring C where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a + b‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

def genPt (R : Type) [CommRing R] [IsDomain R] : Spec (CommRingCat.of R) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)

structure ModelO (O : Type) [CommRing O] where
  Z : Scheme.{0}
  str : Z ⟶ Spec (CommRingCat.of O)
  proper : IsProper str
  flat : Flat str
  normal : ∀ x : Z, IsDomain (Z.presheaf.stalk x) ∧ IsIntegrallyClosed (Z.presheaf.stalk x)
  G : GrpSch Z
  U : Z.Opens
  U_iff : ∀ x : Z, x ∈ U ↔ (CharZero (Z.residueField x) ∧ AbelianAt G x)
  U_dense : Dense (U : Set Z)


def ModelO.toG {O : Type} [CommRing O] [IsLocalRing O] (M : ModelO O) : ModelG O := ⟨M.Z, M.str, M.G⟩

structure PtOver {O : Type} [CommRing O] (M : ModelO O) (C : Type) [NormedField C] [IsUltrametricDist C] where
  alg : O →+* intO C
  x : Spec (CommRingCat.of (intO C)) ⟶ M.Z
  comm : x ≫ M.str = Spec.map (CommRingCat.ofHom alg)
  gen_open : x (genPt (intO C)) ∈ M.U

def PtM (p : ℕ) {O : Type} [CommRing O] (M : ModelO O) : Type :=
  Σ c : SCF p, PtOver M c.S

def PtM.fld {p : ℕ} {O : Type} [CommRing O] {M : ModelO O} (y : PtM p M) : Formalism.MainNotions.ModuliIntegralCharts.CF p := y.1.toCF

abbrev ChartM {O : Type} [CommRing O] (M : ModelO O) (OK : Type) [CommRing OK] : Type :=
  Spec (CommRingCat.of (PowerSeries OK)) ⟶ M.Z

def ChartM.IsOpenPart {O : Type} [CommRing O] {M : ModelO O} {OK : Type} [CommRing OK] [IsLocalRing OK]
    (χ : ChartM M OK) : Prop :=
  ∀ q : PrimeSpectrum (PowerSeries OK), PowerSeries.X ∉ q.asIdeal →
    (∃ a ∈ IsLocalRing.maximalIdeal OK, PowerSeries.C a ∉ q.asIdeal) → χ q ∈ M.U

end Formalism.MainNotions.DIV.Cons
end
end
