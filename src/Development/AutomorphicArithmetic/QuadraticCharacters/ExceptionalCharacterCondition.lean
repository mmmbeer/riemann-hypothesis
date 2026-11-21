import Mathlib

section
open ArithmeticFunction

namespace HostParam

structure AbField where
  N : ℕ
  N_pos : 0 < N
  H : Subgroup (ZMod N)ˣ

namespace AbField

variable (E : AbField)

abbrev Gal : Type := (ZMod E.N)ˣ ⧸ E.H

def res : (ZMod E.N)ˣ →* E.Gal := QuotientGroup.mk' E.H

def conj : E.Gal := E.res (-1)

def IsReal : Prop := (-1 : (ZMod E.N)ˣ) ∈ E.H

def inertiaUnits (p : ℕ) : Subgroup (ZMod E.N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd E.N p)).ker

def inertia (p : ℕ) : Subgroup E.Gal := (E.inertiaUnits p).map E.res

def Ramified (p : ℕ) : Prop := E.inertia p ≠ ⊥

def frob (p : ℕ) (hp : p.Coprime E.N) : E.Gal := E.res (ZMod.unitOfCoprime p hp)

def IsModulus (M : ℕ) : Prop := ∃ h : M ∣ E.N, (ZMod.unitsMap h).ker ≤ E.H

noncomputable def conductor : ℕ := sInf {M : ℕ | E.IsModulus M}

def chars : Set (DirichletCharacter ℂ E.N) := {χ | ∀ u ∈ E.H, χ (u : ZMod E.N) = 1}

noncomputable def toGalChar (χ : DirichletCharacter ℂ E.N) (hχ : χ ∈ E.chars) : E.Gal →* ℂˣ :=
  QuotientGroup.lift E.H χ.toUnitHom (fun u hu => by
    rw [MonoidHom.mem_ker]; ext; simpa using hχ u hu)

end AbField

def SplitsIn (d p : ℕ) : Prop :=
  p ≠ d ∧ (p = 2 → d % 8 = 7) ∧ (p ≠ 2 → jacobiSym (-(d : ℤ)) p = 1)

noncomputable def quadCharNeg (d : ℕ) : DirichletCharacter ℂ d :=
  if h : d.Prime then
    letI : Fact d.Prime := ⟨h⟩
    (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  else 1

noncomputable def AbField.chOf (E : AbField) (d : ℕ) (h : d ∣ E.N) : DirichletCharacter ℂ E.N :=
  DirichletCharacter.changeLevel h (quadCharNeg d)

noncomputable def logDerivAtOne {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) : ℂ :=
  deriv (DirichletCharacter.LFunction ψ) 1 / DirichletCharacter.LFunction ψ 1

noncomputable def Gfun {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  (∑ r ∈ Finset.range (⌊y⌋₊ + 1), (Λ r : ℂ) * ψ r * ((y / r - 1 : ℝ) : ℂ)) +
    haveI := Classical.propDecidable (ψ = 1)
    if ψ = 1 then ((-(y * Real.log y) + (1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)
    else (y : ℂ) * logDerivAtOne ψ

end HostParam
end

section
open ArithmeticFunction

namespace HostParam

abbrev PrimChar : Type := Σ M : ℕ, DirichletCharacter ℂ M

structure HostType where

  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52

  J : ℝ
  one_le_J : 1 ≤ J

  zp : ℝ → ℝ
  zp_ge : ∀ X : ℝ, 1 ≤ X → X ^ (eps / (5 * J)) * Real.log (X ^ (1 / J)) ^ 2 ≤ zp X
  zp_le : ∀ X : ℝ, 1 ≤ X → zp X ≤ X ^ (eps / (5 * J)) * Real.log X ^ 2

  kept : Set PrimChar
  kept_finite : kept.Finite
  kept_pos : ∀ χ ∈ kept, 0 < χ.1
  kept_primitive : ∀ χ ∈ kept, χ.2.IsPrimitive
  kept_conj : ∀ χ ∈ kept, (⟨χ.1, χ.2⁻¹⟩ : PrimChar) ∈ kept
  one_mem_kept : (⟨1, 1⟩ : PrimChar) ∈ kept

  P0 : ℕ
  P0_pos : 0 < P0

  psK : Option PrimChar
  psK_spec : ∀ ψ ∈ psK, ψ ∈ kept ∧ ψ.2 ≠ 1 ∧ ψ.2 ^ 2 = 1 ∧ ψ.2.Odd

  Ct : ℝ
  t : ℝ → ℕ
  t_le : ∀ x : ℝ, 1 ≤ x → (t x : ℝ) ≤ x ^ Ct

  o : ℕ
  o_pos : 0 < o

  rrBound : ℕ

  cA : ℝ
  cA_pos : 0 < cA

  CB : ℝ

namespace HostType

variable (T : HostType)

def SM (l : ℕ) : Prop :=
  l.Prime ∧ l ∣ 2 * T.P0 * ∏ᶠ (χ : PrimChar) (_ : χ ∈ T.kept), χ.1

end HostType

noncomputable def zR (T : HostType) (X : ℝ) : ℝ := X ^ (T.eps / (5 * T.J))

noncomputable def zR' (T : HostType) (X : ℝ) : ℝ := T.zp X

def IsRangeText (T : HostType) (x : ℝ) (e : ℕ) : Prop :=
  x ^ (2 + 8 * T.eps) / 2 ≤ (2 ^ e : ℝ) ∧ (2 ^ e : ℝ) ≤ 2 * x ^ (2 + 8 * T.eps)

def IsRangeN (T : HostType) (x : ℝ) (e : ℕ) : Prop :=
  2 ≤ e ∧ x ^ (2 + 8 * T.eps) / (2 * T.o) ≤ (2 ^ e : ℝ) ∧ (2 ^ e : ℝ) ≤ 2 * x ^ (2 + 8 * T.eps)


abbrev GalRealCyclotomic (n : ℕ) : Type := (ZMod (4 * n))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * n))ˣ)

structure PreHost (T : HostType) (X x : ℝ) where

  one_le_X : 1 ≤ X
  x_ge : X ^ (1 / (T.J : ℝ)) ≤ x
  x_le : x ≤ X
  e : ℕ
  range_n : IsRangeN T x e

  E : AbField
  not_real : ¬ E.IsReal

  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_dvd : d ∣ E.N
  K_le : E.chOf d d_dvd ∈ E.chars

  card_inertia_d : Nat.card (E.inertia d) = 2

  ps : DirichletCharacter ℂ E.N
  ps_mem : ps ∈ E.chars
  ps_ne_one : ps ≠ 1
  ps_sq : ps ^ 2 = 1
  ps_odd : ps.Odd
  ps_inertia : ∀ u ∈ E.inertiaUnits d, ps (u : ZMod E.N) = 1

  four_n_dvd : 4 * 2 ^ e ∣ E.N
  attached_subfield_le_adjoin_simple : ∀ u ∈ E.H, ZMod.unitsMap four_n_dvd u = 1 ∨ ZMod.unitsMap four_n_dvd u = -1

  A0 : Subgroup E.Gal
  base_exponent_le_a : A0 ≤ (E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓ (E.toGalChar ps ps_mem).ker
  A0_inf_stabilizer_trivial : ∀ u : (ZMod E.N)ˣ, E.res u ∈ A0 →
    (QuotientGroup.mk (ZMod.unitsMap four_n_dvd u) : GalRealCyclotomic (2 ^ e)) = 1 → E.res u = 1
  index_A0_eq_o : (A0.subgroupOf ((E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓
      (E.toGalChar ps ps_mem).ker)).index = T.o

  z_ge : 11 ≤ zR T X
  split_small : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ zR T X → SplitsIn d p
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → SplitsIn d l

  ram_kinds : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l →
    ((l : ℝ) ≤ zR T X / 4 ∧ T.SM l) ∨
      (zR T X / 2 < Real.log l ∧ Nat.card (E.inertia l) = 2)
  large_unique : ∀ l l' : ℕ, l.Prime → l'.Prime → l ≠ d → l' ≠ d → E.Ramified l →
    E.Ramified l' → zR T X / 2 < Real.log l → zR T X / 2 < Real.log l' → l = l'

  log_d_gt : zR' T X / 2 < Real.log d
  log_d_le : Real.log d ≤ zR' T X
  log_large_le : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → zR T X / 2 < Real.log l →
    Real.log l ≤ zR T X
  Nsharp : ℕ
  cond_dvd : E.conductor ∣ Nsharp
  log_Nsharp : Real.log Nsharp ≤ 3 * zR' T X

  qs : ℕ
  qs_prime : qs.Prime
  qs_ne : qs ≠ d
  qs_mod : qs % 8 = 3
  qs_split : SplitsIn d qs
  log_qs_gt : zR T X / 2 < Real.log qs
  log_qs_le : Real.log qs ≤ zR T X
  large_eq_qs : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → zR T X / 2 < Real.log l → l = qs
  Nsharp_eq : Nsharp = Nat.lcm E.conductor qs

  rr : ℕ
  rr' : ℕ
  rr_prime : rr.Prime
  rr'_prime : rr'.Prime
  rr_odd : rr ≠ 2
  rr_lt : rr < rr'
  rr'_lt : rr' < 2 * rr
  rr_unram : ¬ E.Ramified rr
  rr'_unram : ¬ E.Ramified rr'
  rr'_le_alt : (rr' : ℝ) ≤ zR T X
  rr'_le : rr' ≤ T.rrBound

end HostParam
end

section
open ArithmeticFunction MeasureTheory

namespace HostParam

noncomputable def prim {N : ℕ} (χ : DirichletCharacter ℂ N) : PrimChar :=
  ⟨χ.conductor, χ.primitiveCharacter⟩

noncomputable def GP (ψ : PrimChar) (y : ℝ) : ℂ :=
  if h : ψ.1 = 0 then 0 else
    haveI : NeZero ψ.1 := ⟨h⟩
    Gfun ψ.2 y

noncomputable def kappaP (ψ : PrimChar) : ℂ :=
  if h : ψ.1 = 0 then 0 else
    haveI : NeZero ψ.1 := ⟨h⟩
    logDerivAtOne ψ.2

noncomputable def Xprime (T : HostType) (x : ℝ) : ℝ := Real.exp (x ^ (T.eps / 3))

namespace PreHost

variable {T : HostType} {X x : ℝ} (P : PreHost T X x)

noncomputable def ch : DirichletCharacter ℂ P.E.N := P.E.chOf P.d P.d_dvd

def Xplus : Set (DirichletCharacter ℂ P.E.N) :=
  {χ | ∃ hχ : χ ∈ P.E.chars, (∀ g ∈ P.A0, P.E.toGalChar χ hχ g = 1) ∧
    ∀ u ∈ P.E.inertiaUnits P.d, χ (u : ZMod P.E.N) = 1}

def fixedA0Chars : Set PrimChar :=
  {ψ | ∃ (χ : DirichletCharacter ℂ P.E.N) (hχ : χ ∈ P.E.chars),
    (∀ g ∈ P.A0, P.E.toGalChar χ hχ g = 1) ∧ prim χ = ψ}

def Xminus : Set (DirichletCharacter ℂ P.E.N) := {χ | ∃ ξ ∈ P.Xplus, χ = P.ch * ξ}

def bounded : Set PrimChar :=
  {ψ | ∃ χ ∈ P.Xplus, prim χ = ψ ∧ ψ ∉ T.kept} ∪ {ψ | ∃ χ ∈ P.Xminus, prim χ = ψ}

def BoundedCharsPointwise : Prop := ∀ ψ ∈ P.bounded, ‖GP ψ x‖ ≤ x ^ (1 / 2 + T.eps)

def BoundedCharsMeanSquare : Prop :=
  ∑ᶠ (ψ : PrimChar) (_ : ψ ∈ P.bounded),
      ∫ y in (X ^ (1 / (T.J : ℝ)))..X, ‖GP ψ y‖ ^ 2 * y ^ (-1 - 2 * T.eps) / y ≤ 1

end PreHost

structure VVFun where
  VV : AbField → ℕ → ENNReal
  mono : ∀ E, Monotone (VV E)

structure Host (T : HostType) (VV : VVFun) (X x : ℝ) extends PreHost T X x where

  kept_sub : ∀ κ ∈ T.kept, ∃ χ ∈ toPreHost.Xplus, prim χ = κ

  character_prime_sum_bound : ∀ χ ∈ E.chars, ∀ y : ℝ, Xprime T x / 3 ≤ y →
    ‖GP (prim χ) y‖ ≤ y * Real.exp (-(T.cA * x ^ (T.eps / 8)))

  character_kappa_power_bound : ‖kappaP (prim toPreHost.ch)‖ ≤ x ^ T.eps
  bounded_chars_log_bound : ∀ ψ ∈ toPreHost.bounded, ‖kappaP ψ‖ ≤ T.CB * Real.log X

  first_or_second_condition : toPreHost.BoundedCharsPointwise ∨ toPreHost.BoundedCharsMeanSquare

  exceptional_character_condition : match T.psK with
    | some κ => prim ps = κ
    | none => prim ps ∉ T.kept

  ha11 : VV.VV E (T.t x) ≤ ENNReal.ofReal (Real.exp (x ^ T.eps) ^ (1 / 2 : ℝ))

structure HostFamily (T : HostType) (VV : VVFun) (X : ℝ) (S : Set ℝ) where
  host : ∀ x ∈ S, Host T VV X x
  second_clause_independent_of_x : ∀ x hx x' hx', ¬ (host x hx).toPreHost.BoundedCharsPointwise →
    let H := host x hx
    let H' := host x' hx'
    H.d = H'.d ∧ H.qs = H'.qs ∧ prim H.ps = prim H'.ps ∧
      H.toPreHost.fixedA0Chars = H'.toPreHost.fixedA0Chars

end HostParam
end
