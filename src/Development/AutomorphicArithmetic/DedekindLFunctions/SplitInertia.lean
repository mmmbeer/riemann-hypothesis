import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain

section
open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Deduction

structure PC where
  N : ℕ
  [nz : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PC.nz

namespace PC

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PC :=
  @PC.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def one : PC := PC.of (1 : DirichletCharacter ℂ 1)

def G (ψ : PC) (y : ℝ) : ℂ := Gchi ψ.χ y

def L (ψ : PC) (s : ℂ) : ℂ := DirichletCharacter.LFunction ψ.χ s

def kappa (ψ : PC) : ℂ := deriv (DirichletCharacter.LFunction ψ.χ) 1 / DirichletCharacter.LFunction ψ.χ 1

end PC

structure BFrame where
  G : Type
  [grp : CommGroup G]
  [fin : Fintype G]
  N : ℕ
  [nz : NeZero N]
  art : (ZMod N)ˣ →* G
  art_surj : Function.Surjective art
  d : ℕ
  d_prime : d.Prime
  d_mod : d % 4 = 3
  d_dvd : d ∣ N
  ch : G →* ℂˣ
  ch_art : ∀ u : (ZMod N)ˣ, ((ch (art u) : ℂˣ) : ℂ) = (jacobiSym (((u : ZMod N).val : ℕ) : ℤ) d : ℤ)
  iod : G
  inertia_d : ∀ g : G, (∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[d] N] ∧ art u = g) ↔ (g = 1 ∨ g = iod)
  ps : G →* ℂˣ
  ps_sq : ps ^ 2 = 1
  ps_conj : ps (art (-1)) = -1
  ps_iod : ps iod = 1
  A0 : Subgroup G
  base_exponent_le_a : A0 ≤ ch.ker ⊓ ps.ker
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d →
    (∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] ∧ art u ≠ 1) → jacobiSym (l : ℤ) d = 1

attribute [instance] BFrame.grp BFrame.fin BFrame.nz

namespace BFrame

open Classical

variable (F : BFrame)

abbrev Char : Type := F.G →* ℂˣ

instance : Fintype F.Char := by
  haveI : NeZero ((Monoid.exponent F.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  exact Fintype.ofFinite _

def c : F.G := F.art (-1)

def sg : F.G := F.c * F.iod

def Phi : Finset F.G := Finset.univ.filter fun g => F.ch g = 1

def coPhi : Finset F.G := Finset.univ.filter fun g => F.ch g ≠ 1

def A : Subgroup F.G := F.ch.ker ⊓ F.ps.ker

def BaseGroupFinset : Finset F.G := Finset.univ.filter fun g => g ∈ F.A0

def f : ℕ := F.Phi.card

def n0 : ℕ := Nat.card F.A0

def o : ℕ := F.A0.relIndex F.A

def dir (θ : F.Char) : DirichletCharacter ℂ F.N := MulChar.ofUnitHom (θ.comp F.art)

def prim (θ : F.Char) : PC := PC.of (F.dir θ)

def frobSet (p i : ℕ) : Set F.G :=
  {g | ∃ u : (ZMod F.N)ˣ, (u : ZMod F.N).val ≡ p ^ i [MOD ordCompl[p] F.N] ∧ F.art u = g}

def frob (p : ℕ) : F.G := if h : (F.frobSet p 1).Nonempty then h.choose else 1

def Inert (p : ℕ) : Prop := p.Prime ∧ jacobiSym (p : ℤ) F.d = -1

def gd (i : ℕ) : F.G := if F.ch (F.frob F.d ^ i) = 1 then F.frob F.d ^ i * F.iod else F.frob F.d ^ i

def partner (τ g : F.G) : F.G := F.c * g * τ

def ASK (τ : F.G) (a : ℝ) (w : F.G → ℝ) : ℝ :=
  (∑' p : ℕ, if F.Inert p then
      2 * Real.log p * ∑' i : ℕ, if Odd i then max (a / (p : ℝ) ^ i - w (F.partner τ (F.frob p ^ i))) 0 else 0 else 0) +
    Real.log F.d * ∑' i : ℕ, max (a / (F.d : ℝ) ^ (i + 1) - w (F.partner τ (F.gd (i + 1)))) 0

def MAIN (a : ℝ) (w : F.G → ℝ) : ℝ :=
  a * (Real.log a - 1 - Real.eulerMascheroniConstant + (F.prim F.ch).kappa.re -
    (F.f : ℝ)⁻¹ * ∑ ρ ∈ F.Phi, Real.log (w ρ))

def term (g : F.G) (a v : ℝ) : ℂ :=
  ∑ θ : F.Char, (starRingEnd ℂ) (θ g : ℂˣ) * (v : ℂ) * (F.prim θ).G (a / v)

def Delta (τ : F.G) (a : ℝ) (w : F.G → ℝ) : ℂ :=
  (F.f : ℂ)⁻¹ * ∑ g ∈ F.coPhi, F.term g a (w (F.partner τ g))

def Xp : Finset F.Char := Finset.univ.filter fun θ => (∀ s ∈ F.A0, θ s = 1) ∧ θ F.iod = 1

def Xm : Finset F.Char := Finset.univ.filter fun θ => (∀ s ∈ F.A0, θ s = 1) ∧ θ F.iod = -1

def bounded (S : Finset PC) : Finset F.Char := F.Xp.filter (fun θ => F.prim θ ∉ S) ∪ F.Xm

def SigB (S : Finset PC) (y : ℝ) : ℝ := ∑ θ ∈ F.bounded S, ‖(F.prim θ).G y‖

end BFrame

structure DType where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  J : ℝ
  one_le_J : 1 ≤ J
  KEPT : Finset PC
  one_mem : PC.one ∈ KEPT
  psK : Option PC
  oB : ℕ
  aStar : ℝ
  aStar_pos : 0 < aStar
  aStar_le : aStar ≤ 1
  cA : ℝ
  cA_pos : 0 < cA
  CB : ℝ
  kaN : ℝ
  kaN_nonneg : 0 ≤ kaN

namespace DType

open Classical

variable (T : DType)

def wt (ξ : PC) : ℝ := if ξ = PC.one ∨ T.psK = some ξ then 1 else T.aStar

def Gm (y : ℝ) : ℝ := ∑ ξ ∈ T.KEPT, T.wt ξ * (ξ.G y).re

def ZeroFree (θ : ℝ) : Prop := ∀ ξ ∈ T.KEPT, ∀ s : ℂ, θ < s.re → ξ.L s ≠ 0

end DType

structure AnHost (T : DType) (X x : ℝ) (F : BFrame) (n : ℕ) : Prop where
  x_ge : X ^ (1 / T.J) ≤ x
  x_le : x ≤ X
  n_ge : x ^ (2 + 8 * T.eps) / 2 ≤ n
  n_le : (n : ℝ) ≤ 2 * x ^ (2 + 8 * T.eps)
  n_le_A : n ≤ Nat.card F.A
  n0_le_Ns : F.n0 ≤ n
  o_le : F.o ≤ T.oB
  kept : ∀ ξ ∈ T.KEPT, ∃ θ ∈ F.Xp, F.prim θ = ξ
  character_prime_sum_bound : ∀ θ : F.Char, ∀ y : ℝ, Real.exp (x ^ (T.eps / 3)) / 3 ≤ y →
    ‖(F.prim θ).G y‖ ≤ y * Real.exp (-(T.cA * x ^ (T.eps / 8)))
  kappa_norm_le_log : ∀ θ ∈ F.bounded T.KEPT, ‖(F.prim θ).kappa‖ ≤ T.CB * Real.log X
  exceptional_character_condition : (∀ ψ, T.psK = some ψ → F.prim F.ps = ψ) ∧ (T.psK = none → F.prim F.ps ∉ T.KEPT)

open Classical in

structure Rows (T : DType) (x : ℝ) (F : BFrame) (n : ℕ) where
  m : ℕ
  k : ℝ
  m_ge : x ^ (1 / 2 - T.eps / 8) ≤ m
  m_le : (m : ℝ) ≤ x ^ (1 / 2 : ℝ)
  k_ge : x ^ (9 / 2 + 10 * T.eps) ≤ k
  k_le : k ≤ 2 * x ^ (9 / 2 + 10 * T.eps)
  TT : Finset F.G
  TT_sub : ∀ t ∈ TT, t ∈ F.A
  TT_ge : (Nat.card F.A : ℝ) * x ^ (-(T.eps / 8)) / 2 ≤ TT.card
  TT_share : ∀ g ∈ F.A, |((TT.filter fun t => g⁻¹ * t ∈ F.A0).card : ℝ) / TT.card -
    ((1 - T.aStar) / F.o + if g ∈ F.A0 then T.aStar else 0)| ≤ x ^ (-1 + T.eps)
  T2 : Finset F.G
  T2_subset_A0 : ∀ s ∈ T2, s ∈ F.A0
  T2_card_lower_bound : x ^ (-T.eps) ≤ (T2.card : ℝ) / F.n0
  aT : F.G → ℝ
  aT_ge : ∀ t ∈ TT, (x - 1) * Real.exp (x ^ T.eps) ≤ aT t
  aT_le : ∀ t ∈ TT, aT t ≤ (x + 1) * Real.exp (x ^ T.eps)
  om : ℝ
  om_le : 4 * F.f * x * om ≤ Real.exp (x ^ T.eps) / x
  w : F.G → Fin m → F.G → ℝ
  w_thick : ∀ u ∈ F.A0, ∀ j, ∀ s ∈ T2,
    Real.exp (x ^ T.eps) ≤ w u j (F.sg * u * s) ∧ w u j (F.sg * u * s) ≤ Real.exp (x ^ T.eps) + om
  w_thin : ∀ u ∈ F.A0, ∀ j, ∀ ρ ∈ F.Phi, (¬ ∃ s ∈ T2, ρ = F.sg * u * s) →
    0 < w u j ρ ∧ w u j ρ ≤ 2 * (x * Real.exp (x ^ T.eps) / Real.exp (x ^ (T.eps / 3)))
  Nc : ℝ
  Nc_le : Nc ≤ T.kaN * ((T2.card : ℝ) / F.n0) * k * Real.exp (x ^ T.eps) * x ^ (2 * T.eps) / n

namespace Rows

variable {T : DType} {x : ℝ} {F : BFrame} {n : ℕ} (D : Rows T x F n)

def E0 : ℝ :=
  D.TT.card * (x * Real.exp (x ^ T.eps)) * (1 + (D.m : ℝ) ^ 2 / D.k) +
    D.m * (F.f * D.m * Real.exp (x ^ T.eps) * x ^ T.eps + D.Nc)

def gap (u : F.G) : ℝ := ∑ j : Fin D.m, ∑ t ∈ D.TT, (F.ASK t (D.aT t) (D.w u j) - F.MAIN (D.aT t) (D.w u j))

def TL (C₁ : ℝ) : Prop := (F.n0 : ℝ)⁻¹ * ∑ u ∈ F.BaseGroupFinset, D.gap u ≤ x ^ (C₁ * T.eps) * D.E0

end Rows

end Deduction

end
end

section
open Finset

noncomputable section

namespace Deduction.CH

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

structure HostFactsS (D : ArithData H) (S : Finset ℕ) : Prop where
  d_prime : D.d.Prime
  two_mem : 2 ∈ S
  q1_mem : D.q1 ∈ S
  d_not_mem : D.d ∉ S
  unram : ∀ p : ℕ, p.Prime → p ∉ S → p ≠ D.d → D.inertia p = ⊥
  split_inertia : ∀ p ∈ S, ∀ x ∈ D.inertia p, InPhi x
  split_frob : ∀ p ∈ S, InPhi (D.frob p)
  inertia_d : ∀ x, x ∈ D.inertia D.d ↔ x = 0 ∨ x = sgc0

open Classical in

def PsiA (A0 : AddSubgroup H) : Finset (AddChar (E0 × H) ℂ) := univ.filter fun ψ => ∀ s ∈ A0, ψ (0, s) = 1

open Classical in

def wtA (c : ℝ) (ψ : AddChar (E0 × H) ℂ) : ℝ := if ∀ h : H, ψ (0, h) = 1 then 1 else c

open Classical in

def GmA (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Kp : Finset (AddChar (E0 × H) ℂ)) (c y : ℝ) : ℝ :=
  ∑ ψ ∈ Kp, wtA c ψ * (GPsi D ell ψ y).re

open Classical in

def SigA (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (y : ℝ) : ℝ :=
  ∑ ψ ∈ PsiA A0 \ Kp, ‖GPsi D ell ψ y‖

def SizesA (A0 : AddSubgroup H) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (N : ℕ)
    (x b b' η X' θ : ℝ) : Prop :=
  0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  (∀ u0 ∈ A0, ∀ j ρ, InPhi ρ → 0 < w u0 j ρ) ∧
  (∀ u0 ∈ A0, ∀ j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + η + 1) ∧
  (∀ u0 ∈ A0, ∀ j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w u0 j ρ ≤ 2 * b') ∧
  (∀ u0 ∈ A0, ∀ j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N)

def gapA (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (u0 : H) : ℝ :=
  ∑ t ∈ TT, ∑ j : Fin m, (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)

open Classical in

def CharsA (ell : AddChar (E0 × H) ℂ → ℂ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (TT : Finset H)
    (c M Ko CE ε x : ℝ) : Prop :=
  0 ∈ Kp ∧ (∀ ψ ∈ Kp, ψ ∈ PsiA A0 ∧ ψ sgc0 = 1) ∧ ((PsiA A0).card : ℝ) ≤ M ∧
  (∀ ψ ∈ Kp, (¬ ∀ h : H, ψ (0, h) = 1) →
    ‖(∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)‖ ≤ M * x ^ (-1 + ε) * (TT.card : ℝ)) ∧
  (∀ ψ ∈ Kp, ψ ≠ 0 → ‖ell ψ‖ ≤ Ko) ∧
  (∀ ψ ∈ PsiA A0, ψ ∉ Kp → ‖ell ψ‖ ≤ CE * Real.log x)

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}

def IdentU (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) : Prop :=
  (∀ τ, Dd.aT τ = a (eT τ)) ∧ (∀ u j ρ, Dd.w u j ρ = w (tr u) j (eP ρ)) ∧
  Dd.gam = Real.eulerMascheroniConstant ∧ Dd.LpL = (ell chC).re ∧
  (∀ u, Dd.ASK u = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w (tr u) j))

def BNBoundsU (Dd : Data U0 W Top m f) (T2 : Finset H) : Prop :=
  Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε ∧
  Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε)))

open Classical in

def ReadsKept (T : DType) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Kp : Finset (AddChar (E0 × H) ℂ)) : Prop :=
  ∃ rd : PC → AddChar (E0 × H) ℂ, Set.InjOn rd T.KEPT ∧ Kp = T.KEPT.image rd ∧
    ∀ ξ ∈ T.KEPT, (∀ n : ℕ, n ≠ 0 → ξ.χ (n : ZMod ξ.N) = primVal D (rd ξ) n) ∧ (rd ξ = 0 ↔ ξ = PC.one) ∧
      (ξ ≠ PC.one → ell (rd ξ) = ξ.kappa) ∧ (T.psK = some ξ ∨ ξ = PC.one ↔ rd ξ = psC ∨ rd ξ = 0)

end Deduction.CH

end
end
