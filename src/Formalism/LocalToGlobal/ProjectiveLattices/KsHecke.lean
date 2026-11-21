import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

namespace KsHecke

open Polynomial

section Gen

variable {L : Type*} [Field L] {WL : Type*} [AddCommGroup WL] [Module L WL]
  {XS : Type*} [AddCommGroup XS] [Module L XS] {G : Type*}

def IsHL (act : G → WL →ₗ[L] WL) (th : XS → WL) (TV : XS →ₗ[L] XS) (T : WL →ₗ[L] WL) : Prop :=
  (∀ g, T ∘ₗ act g = act g ∘ₗ T) ∧ ∀ x, T (th x) = th (TV x)

open Classical in

def hLby (act : G → WL →ₗ[L] WL) (th : XS → WL) (TV : XS →ₗ[L] XS) : WL →ₗ[L] WL :=
  if h : ∃! T, IsHL act th TV T then h.choose else 0

variable {act : G → WL →ₗ[L] WL} {th : XS → WL} {TV : XS →ₗ[L] XS}

def KerStab (Th : XS →ₗ[L] WL) (TV : XS →ₗ[L] XS) : Prop := ∀ x, Th x = 0 → Th (TV x) = 0

def thE (e : WL →ₗ[L] WL) (th : XS → WL) : XS → LinearMap.range e :=
  fun x => ⟨e (th x), LinearMap.mem_range_self e (th x)⟩

def actE (e : WL →ₗ[L] WL) (act : G → WL →ₗ[L] WL) (hc : ∀ g, e ∘ₗ act g = act g ∘ₗ e) (g : G) :
    LinearMap.range e →ₗ[L] LinearMap.range e :=
  (act g).restrict (p := LinearMap.range e) (q := LinearMap.range e) fun w hw => by
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    exact LinearMap.mem_range.mpr ⟨act g v, LinearMap.congr_fun (hc g) v⟩

def hLe (e : WL →ₗ[L] WL) (act : G → WL →ₗ[L] WL) (hc : ∀ g, e ∘ₗ act g = act g ∘ₗ e) (th : XS → WL)
    (TV : XS →ₗ[L] XS) : LinearMap.range e →ₗ[L] LinearMap.range e :=
  hLby (actE e act hc) (thE e th) TV

end Gen

section Str

variable {L : Type*} [Field L] {XS : Type*} [AddCommGroup XS] [Module L XS]

def HeckeIdentityAtZero (tV : ℕ → XS →ₗ[L] XS) : Prop := tV 0 = LinearMap.id

def kap (B q : L) (r n : ℕ) : L := B⁻¹ * q ^ ((((r + 1) / 2 : ℕ) : ℤ) - (n : ℤ))

end Str

section Test

end Test

end KsHecke

end Formalism.L2.Pj
