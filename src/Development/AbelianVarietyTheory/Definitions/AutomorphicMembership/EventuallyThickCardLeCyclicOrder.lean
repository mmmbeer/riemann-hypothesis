import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

section
noncomputable section

namespace GlobalTheory.Mem.Num

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits

def evenCeil (y : ℝ) : ℕ := 2 * ⌈y / 2⌉₊

variable (C : FC) (s : Scale) (n : ℕ)

def fAt : ℕ := 2 * n

def mAt : ℕ := evenCeil (Real.sqrt (s.x * s.delta1))

def kAt : ℕ := evenCeil (s.x ^ (9 / 2 + 10 * s.eps))

def rAt : ℕ := kAt s + mAt s - 1

def nWAt : ℕ := 8 * ⌈C.P.CnW * (rAt s : ℝ) * ((fAt n : ℝ) + (fAt n : ℝ) ^ 2 * ((kAt s : ℝ) - 1) ^ 3 * s.L ^ 2 / (mAt s : ℝ)) / 8⌉₊

def nPAt : ℕ := 8 * fAt n * rAt s + 4

def TOAt : ℕ := ⌈s.x ^ C.T.cTO⌉₊

def tAt : ℕ := TOAt C s * nWAt C s n + nPAt s n - rAt s

def NAt : ℕ := kAt s + mAt s * (tAt C s n + 1)

def RanksOK : Prop :=
  Odd (tAt C s n) ∧ 2 ≤ mAt s ∧ mAt s + 3 ≤ kAt s ∧ kAt s + mAt s - 1 + 5 ≤ tAt C s n ∧ 3 * mAt s < tAt C s n ∧
    mAt s ≤ 2 * n ∧ 2 * n ≤ kAt s ∧ mAt s ^ 2 ≤ kAt s + mAt s * (tAt C s n + 1)

def ranksOf (φ : Formalism.HC.Frame) (h : RanksOK C s φ.ord) : Ranks where
  toFrame := φ
  k := kAt s
  m := mAt s
  t := tAt C s φ.ord
  k_even := even_two_mul _
  m_even := even_two_mul _
  t_odd := h.1
  two_le_m := h.2.1
  m_add_three_le_k := h.2.2.1
  rank_add_five_le := h.2.2.2.1
  three_m_lt_t := h.2.2.2.2.1
  m_le_f := h.2.2.2.2.2.1
  f_le_k := h.2.2.2.2.2.2.1
  m_sq_le_N := h.2.2.2.2.2.2.2

def cStar : ℝ := max (max C.P.CDel C.P.CCount) (max C.P.Ch0N 7)

def cP : ℝ := 7 * C.T.eP - 1

def cDel : ℝ := (C.Ct + 5) * cStar C + cStar C * (C.P.CF + 6) + 2 * C.Ct + 10

def cLam : ℝ := max (3 * C.Ct + 6) (cDel C + 17) + 1

def cH : ℝ := max (max (max (cLam C + 1) ((C.Ct + 5) * cStar C)) (max (cStar C * (C.Ct + 1) + 6) (3 * C.Ct + 7)))
  (max (cP C + C.T.cTO + C.Ct + 30) 100)

def DelAt : ℕ := ⌈s.x ^ cDel C⌉₊

def hhAt : ℕ := ⌈s.x ^ cH C⌉₊

def etaAt : ℝ := (mAt s : ℝ) * (2 * (hhAt C s : ℝ))

def j0At : ℕ := ⌈Real.logb 5 ((n : ℝ) * (NAt C s n : ℝ) / (mAt s : ℝ))⌉₊

def LwAt : ℕ := 10 * ⌈(C.Ct + 4) * Real.log s.x⌉₊ + 2 * ⌈30 / s.eps⌉₊ + 22

def GamAt : ℝ := Real.exp (C.CGam * (mAt s : ℝ) ^ 5 * (fAt n : ℝ) * s.L)

def wordsAt : ℕ := ⌈3 * GamAt C s n ^ 2 * s.x ^ C.P.CF⌉₊

def YAt : ℝ := ((kAt s : ℝ) * s.b) ^ 8

def bTopAt : ℝ := s.b' + 2 * (n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (kAt s : ℝ)

structure HCIn where
  Del : ℕ
  hh : ℕ
  B : ℤ
  U1 : ℤ
  Uk : ℤ
  δ : ℕ → Bool

def HCIn.OK (I : HCIn) (R : Ranks) : Prop :=
  1 ≤ I.Del ∧ R.t + 3 ≤ 2 * I.hh ∧ ((R.k : ℤ) - 2) * (4 * I.Del) ≤ I.U1 ∧ I.Uk ≤ -1 ∧ -I.B ≤ I.Uk

def HCIn.vZ (I : HCIn) (R : Ranks) (i : ℕ) : ℤ := ((R.k : ℤ) - 2 - i) * (4 * I.Del)

def HCIn.uZ (I : HCIn) (R : Ranks) (i : ℕ) : ℤ :=
  if i = 0 then I.U1 else if i + 1 = R.k then I.Uk
  else ((R.k : ℤ) - 1 - i) * (4 * I.Del) - 1 - (if I.δ (i - 1) then (I.Del : ℤ) else 0)

def HCIn.hc (I : HCIn) (R : Ranks) (h : I.OK R) : HCParam R where
  u i := (I.uZ R i : ℚ) + 1 / 2
  v i := (I.vZ R i : ℚ)
  b j := ((I.B + (j : ℕ) * (2 * I.hh) : ℤ) : ℚ)
  e j := ((I.B + (j : ℕ) * (2 * I.hh) + I.hh : ℤ) : ℚ)
  u_gt_v i := by
    obtain ⟨h1, -, h3, -, -⟩ := h
    have hi := i.2
    have h1' : (1 : ℤ) ≤ I.Del := by exact_mod_cast h1
    have : I.vZ R i ≤ I.uZ R i := by
      unfold HCIn.vZ HCIn.uZ
      split_ifs with a b c
      · rw [a]; simpa using h3
      · omega
      · nlinarith
      · nlinarith
    have h' : (I.vZ R i : ℚ) ≤ I.uZ R i := by exact_mod_cast this
    show (I.vZ R i : ℚ) < (I.uZ R i : ℚ) + 1 / 2
    linarith
  v_gt_u i := by
    obtain ⟨h1, -, -, h4, -⟩ := h
    have hi := i.2
    have h1' : (1 : ℤ) ≤ I.Del := by exact_mod_cast h1
    have : I.uZ R (i + 1) + 1 ≤ I.vZ R i := by
      unfold HCIn.vZ HCIn.uZ
      rw [if_neg (Nat.succ_ne_zero _)]
      split_ifs with b c
      · have : (R.k : ℤ) - 2 - (i : ℕ) = 0 := by omega
        rw [this]; omega
      · push_cast; nlinarith
      · push_cast; nlinarith
    have h' : (I.uZ R (i + 1) : ℚ) + 1 ≤ I.vZ R i := by exact_mod_cast this
    show (I.uZ R (i + 1) : ℚ) + 1 / 2 < (I.vZ R i : ℚ)
    linarith
  u_last_gt hk hm := by
    obtain ⟨-, -, -, -, h5⟩ := h
    have h3 := R.m_add_three_le_k
    have : I.uZ R (R.k - 1) = I.Uk := by
      unfold HCIn.uZ
      rw [if_neg (by omega), if_pos (by omega)]
    have h' : (-I.B : ℚ) ≤ I.Uk := by exact_mod_cast h5
    show -((I.B + (0 : ℕ) * (2 * I.hh) : ℤ) : ℚ) < (I.uZ R (R.k - 1) : ℚ) + 1 / 2
    rw [this]; push_cast; linarith
  gap_be j := by
    have h' : (R.t : ℚ) + 3 ≤ 2 * I.hh := by exact_mod_cast h.2.1
    push_cast; linarith
  gap_eb j hj := by
    have h' : (R.t : ℚ) + 3 ≤ 2 * I.hh := by exact_mod_cast h.2.1
    push_cast; linarith
  e_int j := ⟨_, rfl⟩
  u_half i := ⟨_, rfl⟩
  v_int i := ⟨_, rfl⟩
  b_int j := ⟨_, rfl⟩

section Places

variable {R : Ranks} (H : Host R) (a b : R.A → ℤ)

instance psiFin (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

open Classical in

def baseZ (g : R.GG) : ℤ :=
  if g ∈ H.topPlaces then b (R.iotaInv g.2) + ⌊s.b' / s.x⌋
  else if g ∈ H.thickPlaces then ⌈s.b⌉ else ⌈s.w'' R.n⌉

def shiftPl : R.GG := R.tau2 (R.dig (sInf (H.T2 : Set ℕ)) + H.u0)

open Classical in

def nodeZ (g : R.GG) : ℤ :=
  baseZ s H b g + if g = shiftPl H ∧ Odd (∑ g' : R.Psi, baseZ s H b (g' : R.GG)) then 1 else 0

open Classical in

def inAt (δ : ℕ → Bool) (g : R.GG) : HCIn where
  Del := DelAt C s
  hh := hhAt C s
  B := nodeZ s H b g
  U1 := if g ∈ H.topPlaces then a (R.iotaInv g.2) + (R.k / 2 : ℕ) - 1
    else ((R.k : ℤ) - 2) * (4 * DelAt C s) + R.k * (4 * DelAt C s)
  Uk := if g ∈ H.topPlaces then -b (R.iotaInv g.2) - (R.k / 2 : ℕ) else -1
  δ := δ

end Places

end GlobalTheory.Mem.Num

end
end

section
noncomputable section

namespace GlobalTheory.Mem.Num

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits NumberField

structure admitted (C : FC) : Prop where
  fixed : C.Fixed
  eP : C.T.eP = 12
  Cp : C.T.Cp = 1
  cTO : C.T.cTO = 377
  Cc : C.Cc = 2
  CLw : C.P.CLw = 4455
  Cj0 : C.P.Cj0 = 405
  cw : C.P.cw = 9 / 10
  CYL : C.P.CYL = 9
  CccK : C.P.CccK = 1
  CetaF : C.P.CetaF = 6
  pos : ∀ c ∈ C.P.list, 0 < c
  CP : 1 ≤ C.T.CP
  Cb : 0 ≤ C.T.Cb
  ChT : 1 ≤ C.T.ChT
  CbN : 1 ≤ C.T.CbN
  CGam : 0 < C.CGam
  GK : C.GK.Nonneg
  La : 1 ≤ C.GK.La

structure AdmStd (C : FC) : Prop where
  std : GlobalTheory.EX.Std C
  GK : C.GK.Nonneg
  La : 1088 ≤ C.GK.La

theorem AdmStd.adm {C : FC} (h : AdmStd C) : admitted C := by
  obtain ⟨⟨hF, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12, h13, hm, hl⟩, hG, hLa⟩ := h
  have hnW := hF.2.2.2.2.2.2.2.1
  simp only [FC.cMid, FC.cLast, List.mem_cons, forall_eq_or_imp, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hm hl
  obtain ⟨m1, m2, -⟩ := hm
  obtain ⟨l1, l2, l3, l4, l5, -, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, -⟩ := hl
  have hc : 0 < C.P.cLL := inv_pos.1 (by linarith)
  refine ⟨hF, h8, h7, h9, h1, by rw [h2]; norm_num, h3, h4, h5, h6, h11, ?_, by linarith, by linarith, l17, l18,
    by linarith, hG, by linarith⟩
  simp only [PC.list, List.mem_cons, forall_eq_or_imp, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem AdmStd.CTu {C : FC} (h : AdmStd C) : C.CTu = 25 ∧ C.CTu = 2 * C.P.CYL + 3 + 4 := by
  obtain ⟨-, -, -, -, -, h5, -, -, -, -, h10, -⟩ := h.std
  exact ⟨h10, by rw [h10, h5]; norm_num⟩

theorem AdmStd.CP {C : FC} (h : AdmStd C) : 1000 ≤ C.T.CP := h.std.2.2.2.2.2.2.2.2.2.2.2.2.2.1

def RChosen (C : FC) (s : Scale) (R : Ranks) : Prop :=
  (s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps)) ∧
    R.k = kAt s ∧ R.m = mAt s ∧ R.t = tAt C s R.n ∧ (R.o : ℝ) ≤ C.P.Cpde

def dlogH {R : Ranks} (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))) 1 /
    DirichletCharacter.LFunction ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) 1).re

structure HChosen (C : FC) (s : Scale) {R : Ranks} (H : Host R) : Prop where
  ranks : RChosen C s R
  q_lo : Real.exp (s.x ^ (s.ez / 5) / 2) < (H.q : ℝ)
  q_hi : (H.q : ℝ) ≤ Real.exp (s.x ^ (s.eps / 5))
  d_lo : Real.exp (s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 / 2) < (H.d : ℝ)
  d_hi : (H.d : ℝ) ≤ Real.exp (s.x ^ (s.eps / 5) * Real.log s.x ^ 2)
  dlog : |dlogH H| ≤ s.x ^ s.eps
  split : ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound
  tt : s.delta1 * R.n / 2 ≤ (H.TT.card : ℝ) ∧ (H.TT.card : ℝ) ≤ 2 * s.delta1 * R.n
  t2 : s.x ^ (-s.eps) ≤ (H.T2.card : ℝ) / R.n
  Lw : H.Lw = LwAt C s
  CT2 : H.CT2 = C.CT2
  ccK : H.ccK = ⊤
  pde_log : Real.log H.pde ≤ C.P.Cpde * Real.log (H.QS * H.q * H.d) ∧
    Real.log H.pde' ≤ C.P.Cpde * Real.log (H.QS * H.q * H.d)
  pde_split : (Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E
  g_win : ∀ i, YAt s ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * YAt s
  g_norm : ∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_mod : ∀ i, H.g i % (H.QS * H.q * H.d) = 1
  level_split : ∀ p ∈ H.levelPrimes, H.cls p = .splitK
  J_le : s.J ≤ C.P.Cpde
  QS_le : (H.QS : ℝ) ≤ C.P.Cpde * R.n

structure InRange (C : FC) (s : Scale) {R : Ranks} (H : Host R) (q0 : ℕ) : Prop extends HChosen C s H where
  thickCard_bound : 4 * H.Lw * H.T2.card ≤ R.n0
  automorphicMembership_prime_fact : q0.Prime
  automorphicMembership_level_fact : q0 ∈ H.levelPrimes
  q0_mod_eq_one_of_dvd_condE : q0 % (H.QS * H.q * H.d) = 1
  automorphicMembership_ge_fact : 5 ≤ q0
  automorphicMembership_log_fact : Real.log q0 ≤ C.P.Cpde * Real.log (H.QS * H.q * H.d)
  q0_ne_two_and_ne_q_and_ne_d : q0 ≠ H.pde ∧ q0 ≠ H.pde'

def WtWin (C : FC) (s : Scale) {R : Ranks} (H : Host R) (a b : R.A → ℤ) : Prop :=
  ∀ t ∈ H.TT, (s.a ≤ (a t : ℝ) ∧ (a t : ℝ) ≤ s.a + s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧
    s.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ bTopAt C s R.n

structure DChosen (C : FC) (s : Scale) (D : D7) (a b : D.R.A → ℤ) : Prop where
  host : HChosen C s D.host
  wt : WtWin C s D.host a b
  hc : ∀ u τ, ∃ h : (inAt C s D.host a b (wordBits D u) (D.eTau τ : D.R.GG)).OK D.R,
    D.hcW u τ = (inAt C s D.host a b (wordBits D u) (D.eTau τ : D.R.GG)).hc D.R h
  Del : D.s.Del = (DelAt C s : ℚ)
  etaF : D.div.etaF = C.P.CetaF * s.x ^ (-C.P.CF)
  words : @Fintype.card D.what₂.Word D.wordFin = wordsAt C s D.R.n
  Gam : ∀ u, (D.mem u).A.GamP = GamAt C s D.R.n

structure LChosen (C : FC) {D : D7} (L : SizeData₂ D) : Prop where
  d : DChosen C L.sc D (G.aL L) (G.bL L)
  eta : L.etaSz = etaAt C L.sc
  LaG : L.LaG = G.La C.GK L.sc
  Ct : L.Ct = C.Ct
  Cc : L.Cc = C.Cc
  CGam : L.CGam = C.CGam
  j0 : L.j0 = j0At C L.sc D.R.n

structure LedNum (C : FC) (s : Scale) (D : D7) (a b : D.R.A → ℤ) : Prop where
  top_u : ∀ τ (t : D.host.TT) (h0 : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).u ⟨0, h0⟩ : ℚ) : ℝ) = a t + ((D.R.k : ℝ) - 1) / 2 ∧
    (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -(b t : ℝ) - ((D.R.k : ℝ) - 1) / 2
  top_b : ∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (b t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3
  b_le : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ s.b ^ 2
  logFiveDepth_le : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0At C s D.R.n
  weightLength_ge_depth : 10 * j0At C s D.R.n + 20 ≤ D.host.Lw
  thickDensity_pos : 0 < (D.host.T2.card : ℝ) / D.R.n
  thickDensity_le_one : (D.host.T2.card : ℝ) / D.R.n ≤ 1
  win_thick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
    s.b ≤ wj D j τ ∧ wj D j τ ≤ s.b + etaAt C s + 1
  win_top : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (b t : ℝ) + s.b' / s.x ≤ wj D j τ ∧ wj D j τ ≤ (b t : ℝ) + s.b' / s.x + etaAt C s
  win_thin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
    s.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ s.w'' D.R.n + etaAt C s
  cloud_gap : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
    (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ C.Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
  cloud_v : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  cloud_u : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
    0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  be_close : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ etaAt C s
  eta_pos : 0 < etaAt C s
  t_win : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ s.x ^ C.Ct
  o_tie : (D.R.o : ℝ) ≤ s.x ^ (s.eps / 100)
  QS_tie : (D.host.QS : ℝ) ≤ 4 * D.R.n * s.x ^ (s.eps / 100)

def wPartner (D : D7) (j : ℕ) (t : G.HH D) (p i : ℕ) : ℝ :=
  max 1 (wPl D (max 1 (min j D.R.m)) (G.partner D p t i))

def sizeData0 (C : FC) (hC : admitted C) (s : Scale) (D : D7) (a b : D.R.A → ℤ) (hD : DChosen C s D a b)
    (hN : LedNum C s D a b)
    (hA : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0) : SizeData₂ D where
  sc := s
  aT t := a t
  aT_win t := (hD.wt t t.2).1
  bT t := b t
  bT_ge t := (hD.wt t t.2).2.1
  top_u := hN.top_u
  top_b := hN.top_b
  supp := ∅
  gain _ _ := 0
  F _ _ := 0
  E _ _ _ := 0
  tau _ := 0
  io _ := 0
  gain_supp _ _ _ := rfl
  F_supp _ _ _ := rfl
  E_supp _ _ _ _ := rfl
  tau_supp _ _ := rfl
  io_supp _ _ := rfl
  gain_g _ _ _ := rfl
  b_le := hN.b_le
  untwisted w h j h1 h2 := ⟨hA w h j h1 h2, rfl⟩
  not_inert _ _ _ := ⟨fun _ => rfl, rfl, rfl⟩
  drop := ∅
  drop_alt _ := Set.notMem_empty _
  F_conj _ _ := rfl
  F_above _ _ _ _ _ := rfl
  j0 := j0At C s D.R.n
  logFiveDepth_le := hN.logFiveDepth_le
  weightLength_ge_depth := hN.weightLength_ge_depth
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := hD.host.split
  o_tie := hN.o_tie
  QS_tie := hN.QS_tie
  NuLat u := (D.div.Nu u).L
  de2 := (D.host.T2.card : ℝ) / D.R.n
  thickDensity_pos := hN.thickDensity_pos
  thickDensity_le_one := hN.thickDensity_le_one
  typeDensity_eq_card_div := rfl
  LaG := G.La C.GK s
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := etaAt C s
  Sc_pos := by
    have h1 : (0 : ℝ) < D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    have h2 : (0 : ℝ) < (D.s.Del : ℝ) := by exact_mod_cast D.s.Del_pos
    positivity
  Sc_eq := rfl
  Cc := C.Cc
  win_thick := hN.win_thick
  win_top := hN.win_top
  win_thin := hN.win_thin
  cloud_gap := hN.cloud_gap
  cloud_v := hN.cloud_v
  cloud_u := hN.cloud_u
  be_close := hN.be_close
  etaSz_pos := hN.eta_pos
  TTw _ := Finset.univ
  TTw_full _ _ := rfl
  Ct := C.Ct
  t_win := hN.t_win
  CGam := C.CGam
  CGam_pos := hC.CGam
  Gam_eq u := by
    obtain ⟨-, -, h3, -⟩ := hD.host.ranks
    rw [hD.Gam u, GamAt, Real.log_exp, ← h3]
    rfl
  wPart j t p i := wPartner D j t p i
  wPart_ge _ _ _ _ := le_max_left _ _
  lenMN _ _ := 0

def numOf (C : FC) (s : Scale) (D : D7) : Formalism.L2.DIV.NumDatum where
  R := D.R
  sc := s
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := DelAt C s
  h0 := 2 * hhAt C s
  hc z := D.hc (tauPl D z)

namespace Chosen

def consts (CT2 C8 Cdg C5 : ℝ) (full : Prop) (p m l : ℝ) : FC where
  Ct := 401
  Cc := 2
  CT2 := CT2
  CGam := m
  Csz := m
  Cr := 1
  CTu := 25
  Cdg := Cdg
  C5 := C5
  full := full
  GK := ⟨m, l, l, l, l, l, l, l, l, l, l, 5, 4, 1, l⟩
  cX := ⟨1, ⟨12, 3, m⟩⟩
  P := ⟨l, l, l, l⁻¹, 10, l, l, 11 * 405, 405, l, 9 / 10, l, l, l, l, l, l, 6, l, 9, C8, 1, m⟩
  T := ⟨p, 12, 1, l, 377, l, l⟩

theorem admissibleStandard_constants (CT2 Cdg C5 : ℝ) (full : Prop) {C8 p m l : ℝ} (h8 : 1 ≤ C8) (hp : 1000 ≤ p) (hm : 1088 ≤ m) (hl : 1 ≤ l) :
    AdmStd (consts CT2 C8 Cdg C5 full p m l) := by
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    h8, hp, ?_, ?_⟩, ?_, hm⟩
  · intro c hc
    have : c = m := by simpa [FC.cMid, consts] using hc
    linarith
  · intro c hc
    have : c = l := by simpa [FC.cLast, consts] using hc
    linarith
  · simp [G.Consts.Nonneg, consts, hm0, hl0]

example : admitted (consts 1 1 1 1 True 1000 1088 1) := (admissibleStandard_constants 1 1 1 True le_rfl le_rfl le_rfl le_rfl).adm

example : ¬ AdmStd (consts 1 1 1 1 True 999 1088 1) := fun h => by
  have := h.CP
  norm_num [consts] at this

theorem iota_inv (φ : Formalism.HC.Frame) (t : φ.A) : φ.iotaInv (φ.tau1 t).2 = t := rfl

theorem top_ex {R : Ranks} (H : Host R) {g : R.GG} (hg : g ∈ H.topPlaces) : ∃ t ∈ H.TT, g = R.tau1 t := by
  classical
  unfold Host.topPlaces at hg
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hg
  exact ⟨t, ht, rfl⟩

end Chosen

end GlobalTheory.Mem.Num

end
end
