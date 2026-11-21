import Formalism.CharacterColumnKernels.StatementX

open Finset

noncomputable section

namespace Formalism.NG

universe u

def blockOf {g n K : Type*} (M : Matrix g g (Matrix n n K)) : Matrix (g × n) (g × n) K :=
  fun p q => M p.1 q.1 p.2 q.2

def epsImg (O : Type*) {OO M : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M]
    [Module OO M] [Module O M] [IsScalarTower O OO M] (ε : OO) : Submodule O M :=
  LinearMap.range (DistribSMul.toLinearMap O M ε)

def epsIdeal (O : Type*) {OO : Type*} [CommRing O] [Ring OO] [Algebra O OO] (ε : OO) :
    Submodule O OO :=
  LinearMap.range (LinearMap.mulLeft O ε)

def rightMulEps (O : Type*) {OO : Type*} [CommRing O] [Ring OO] [Algebra O OO] (ε a : OO) :
    epsIdeal O ε →ₗ[O] epsIdeal O ε where
  toFun x := ⟨x.1 * a, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y * a, by simp only [LinearMap.mulLeft_apply] at hy ⊢; rw [← mul_assoc, hy]⟩⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp

abbrev EpsDual (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
    (ε : OO) : Type _ :=
  epsIdeal O ε →ₗ[O] Q

section EpsDual
variable (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
  (ε : OO)

instance EpsDual.moduleOO : Module OO (EpsDual O OO Q ε) where
  smul a φ := (show epsIdeal O ε →ₗ[O] Q from φ).comp (rightMulEps O ε a)
  one_smul φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε 1 x) = φ x
    congr 1; ext; simp [rightMulEps]
  mul_smul a b φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε (a * b) x) = φ (rightMulEps O ε b (rightMulEps O ε a x))
    congr 1; ext; simp [rightMulEps, mul_assoc]
  smul_zero a := by
    refine LinearMap.ext fun x => ?_
    rfl
  smul_add a φ ψ := by
    refine LinearMap.ext fun x => ?_
    rfl
  add_smul a b φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε (a + b) x) = φ (rightMulEps O ε a x) + φ (rightMulEps O ε b x)
    rw [← map_add]; congr 1; ext; simp [rightMulEps, mul_add]
  zero_smul φ := by
    refine LinearMap.ext fun x => ?_
    show φ (rightMulEps O ε 0 x) = 0
    have : rightMulEps O ε 0 x = 0 := by ext; simp [rightMulEps]
    rw [this, map_zero]

end EpsDual

def StatMatlis : Prop :=
  ∀ (O N : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup N]
    [Module O N], IsFiniteLength O N →
    Module.length O (N →ₗ[O] KO O) = Module.length O N

def nnY {R Y S : Type*} [Ring R] [Ring S] [AddCommGroup Y] [Module R Y] (pr : R →+* S) :
    Submodule R Y :=
  Submodule.span R {z | ∃ x : R, pr x = 0 ∧ ∃ y : Y, z = x • y}

def nnYe {R Y S : Type*} [Ring R] [Ring S] [AddCommGroup Y] [Module R Y] (pr : R →+* S) (e : R) :
    Submodule R Y :=
  nnY pr ⊔ Submodule.span R (Set.range fun y : Y => (1 - e) • y)

end Formalism.NG
