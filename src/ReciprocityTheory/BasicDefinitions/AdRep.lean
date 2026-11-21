import Mathlib

section
namespace ReciprocityTheory.Def

open IsLocalRing Matrix

universe u v w w'

class IsCNL (O : Type u) (A : Type w) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

abbrev PS (O : Type u) [CommRing O] (a : ℕ) : Type u := MvPowerSeries (Fin a) O

structure Pattern (n : ℕ) where
  rel : Fin n → Fin n → Prop
  refl : ∀ i, rel i i
  trans : ∀ i j l, rel i j → rel j l → rel i l

namespace Pattern

variable {n : ℕ}

def full (n : ℕ) : Pattern n := ⟨fun _ _ => True, fun _ => trivial, fun _ _ _ _ _ => trivial⟩

def upper (n : ℕ) : Pattern n := ⟨fun i j => i ≤ j, fun i => le_refl i, fun _ _ _ h h' => le_trans h h'⟩

def diag (n : ℕ) : Pattern n := ⟨fun i j => i = j, fun _ => rfl, fun _ _ _ h h' => h.trans h'⟩

def Mem (S : Pattern n) {A : Type*} [Zero A] (X : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j, ¬ S.rel i j → X i j = 0

def mat (S : Pattern n) (A : Type*) [CommRing A] : Submodule A (Matrix (Fin n) (Fin n) A) where
  carrier := {X | S.Mem X}
  add_mem' := fun {X Y} hX hY i j h => by simp [hX i j h, hY i j h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX i j h => by simp [hX i j h]

end Pattern

section Lift

variable (O : Type u) [CommRing O] [IsLocalRing O]
variable {G : Type v} [Group G] [TopologicalSpace G] {n : ℕ}

structure IsResidual (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O)) : Prop where
  cont : IsOpen {g : G | rbar g = 1}
  mem : ∀ g, S.Mem (rbar g).val

structure IsLift (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O))
    {A : Type w} [CommRing A] [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (ρ : G →* GL (Fin n) A) : Prop where
  cont : ∀ N : ℕ, IsOpen {g : G | ∀ i j, (ρ g).val i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ maximalIdeal A ^ N}
  red : ∀ g, (ρ g).val.map (residue A) = (rbar g).val.map (ResidueField.map (algebraMap O A))
  mem : ∀ g, S.Mem (ρ g).val

def push {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (f : A →ₐ[O] B)
    (ρ : G →* GL (Fin n) A) : G →* GL (Fin n) B :=
  (Matrix.GeneralLinearGroup.map f.toRingHom).comp ρ

structure IsUniversal (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O))
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra O R] [IsCNL O R] (ρu : G →* GL (Fin n) R) : Prop where
  isLift : IsLift O S rbar ρu
  existsUnique : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra O A] [IsCNL O A]
    (ρ : G →* GL (Fin n) A), IsLift O S rbar ρ → ∃! f : R →ₐ[O] A, push O f ρu = ρ

end Lift

end ReciprocityTheory.Def
end

section
namespace ReciprocityTheory.Def

open Matrix

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module k M]

def C1 (G : Type*) [TopologicalSpace G] (N : Submodule k M) : Submodule k (G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g, c g ∈ N}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g => N.add_mem (ha.2 g) (hb.2 g)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' := fun c x hx => ⟨hx.1.comp (fun m => c • m), fun g => N.smul_mem c (hx.2 g)⟩

def C2 (G : Type*) [TopologicalSpace G] (N : Submodule k M) : Submodule k (G × G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ x, c x ∈ N}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g => N.add_mem (ha.2 g) (hb.2 g)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' := fun c x hx => ⟨hx.1.comp (fun m => c • m), fun g => N.smul_mem c (hx.2 g)⟩

def d0 (π : Representation k G M) : M →ₗ[k] (G → M) where
  toFun m := fun g => π g m - m
  map_add' := fun a b => by ext g; simp; abel
  map_smul' := fun c a => by ext g; simp [smul_sub]

def d1 (π : Representation k G M) : (G → M) →ₗ[k] (G × G → M) where
  toFun c := fun x => π x.1 (c x.2) - c (x.1 * x.2) + c x.1
  map_add' := fun a b => by ext x; simp; abel
  map_smul' := fun c a => by ext x; simp [smul_sub, smul_add]

def d2 (π : Representation k G M) : (G × G → M) →ₗ[k] (G × G × G → M) where
  toFun z := fun x => π x.1 (z (x.2.1, x.2.2)) - z (x.1 * x.2.1, x.2.2) + z (x.1, x.2.1 * x.2.2) - z (x.1, x.2.1)
  map_add' := fun a b => by ext x; simp; abel
  map_smul' := fun c a => by ext x; simp [smul_sub, smul_add]

def Z1 (π : Representation k G M) (N : Submodule k M) : Submodule k (G → M) :=
  C1 G N ⊓ LinearMap.ker (d1 π)

def B1 (π : Representation k G M) (N : Submodule k M) : Submodule k (G → M) := N.map (d0 π)

def Z2 (π : Representation k G M) (N : Submodule k M) : Submodule k (G × G → M) :=
  C2 G N ⊓ LinearMap.ker (d2 π)

def B2 (π : Representation k G M) (N : Submodule k M) : Submodule k (G × G → M) := (C1 G N).map (d1 π)

abbrev H1 (π : Representation k G M) (N : Submodule k M) : Type _ := Z1 π N ⧸ (B1 π N).submoduleOf (Z1 π N)

abbrev H2 (π : Representation k G M) (N : Submodule k M) : Type _ := Z2 π N ⧸ (B2 π N).submoduleOf (Z2 π N)

def adRep {n : ℕ} (rbar : G →* GL (Fin n) k) : Representation k G (Matrix (Fin n) (Fin n) k) where
  toFun g :=
    { toFun := fun X => (rbar g).val * X * ((rbar g)⁻¹).val
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp }
  map_one' := by ext X : 1; simp
  map_mul' := fun g h => by ext X : 1; simp [mul_assoc]

end ReciprocityTheory.Def
end
