import Formalism.WideWeightTheorem.Statement

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.D5

open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter

def DLVP : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y → |Gz y| ≤ K * y * Real.exp (-(c * Real.sqrt (Real.log y)))

structure SizeParameters where

  b : ℝ

  b1 : ℝ

  w2 : ℝ

  m : ℕ
  k : ℕ
  H : ℕ

  de1 : ℝ
  de2 : ℝ

  R : ℝ

  p0 : ℝ

  kap : ℝ

  Lrd : ℝ

  hc : ℝ
  logc : ℝ

  mthin : ℝ

structure ExplicitFormulaData (C ε x : ℝ) (P : SizeParameters) {nn : ℕ} (w y : Fin nn → ℝ) (d : ℕ)
    (χ : DirichletCharacter ℂ d) where

  ps : ℕ → ℝ
  chps : ℕ → ℝ
  ellPs : ℝ
  ellChPs : ℝ

  nT : ℕ
  β : Fin nT → ℝ
  u : Fin nT → ℝ
  A : Fin nT → ℝ
  g : Fin nT → ℝ → ℝ
  u_mem : ∀ i, P.w2 ≤ u i ∧ u i ≤ 2 * P.b1

  A_mem : ∀ i, x * P.b ≤ A i ∧ A i ≤ 2 * (x * P.b)
  mass : (∑ i, |β i|) ≤ P.mthin

  box : ∀ i, g i = Gz ∨ ∀ Y : ℝ, x * P.b / (2 * P.b1) ≤ Y →
    |g i Y| ≤ C * Y * (Y ^ (-(1 : ℝ) / 20) * x ^ (P.hc + ε) + x ^ (-P.hc) * P.logc ^ 6
      + Real.exp (-(x ^ (ε / C)) / C))

  copy : ℝ
  frame : ℝ
  lev : ℝ
  phic : ℝ
  serv : ℝ
  iv : ℝ
  ram : ℝ
  thinPl : ℝ
  divMain : ℝ
  nTot : ℝ
  Ld : Finset ℕ
  len : ℕ → ℝ

  ineq : P.de2 / 2 * (gavg w y Gz + gavg w y (Gch ps ellPs) - gavg w y (GJ d χ)
        - gavg w y (Gch chps ellChPs))
      + (∑ i, β i * (u i / P.b) * g i (A i / u i))
      ≤ copy + frame + lev + phic + serv + iv + ram + thinPl
        + P.de2 / P.de1 * (divMain + P.m * nTot + P.m * (∑ l ∈ Ld, Real.log l * len l)) / (P.m * P.b)

  frame_S : frame ≤ C * x ^ ε * (x / P.m)

  copy_G : copy ≤ C * x ^ ε * (x / P.m)

  lev_G : lev ≤ C * x ^ ε * (x * P.m / P.k)

  phic_G : phic ≤ C * x ^ ε * (x / P.H)

  serv_G : serv ≤ C * x ^ ε * (x / P.k + 1 + x / P.p0 ^ 2 + P.m * P.kap * x)

  iv_G : iv ≤ C * x ^ ((1 : ℝ) / 2 + ε)

  ram_G : ram ≤ C * x ^ ε * (1 + P.logc)

  thinPl_DIV : thinPl ≤ C * x ^ ε * (2 * P.k * P.b1 * P.Lrd / (P.de1 * P.b))

  div_DIV : divMain ≤ C * x ^ ε * (P.m : ℝ) ^ 2 * P.b

  N_tot : nTot ≤ C * x ^ ε * P.m * P.b

  N_d : ∀ l ∈ Ld, 0 ≤ len l ∧ len l ≤ C * x ^ ε * P.k * P.b / (l : ℝ) ^ 2

  phi_i : ∀ l ∈ Ld, P.R < l
  phi_ii : (∑ l ∈ Ld, Real.log l / (l : ℝ) ^ 2) ≤ x ^ ε / (P.H * P.R)

def SizeConditions (ε K x : ℝ) (P : SizeParameters) : Prop :=
  0 < P.b ∧ 0 < P.b1 ∧ 0 < P.w2 ∧ 0 < P.m ∧ 0 < P.k ∧ 0 < P.H ∧ 0 < P.de1 ∧ 0 < P.R ∧ 0 < P.p0 ∧
  0 ≤ P.kap ∧ 0 ≤ P.Lrd ∧ 0 ≤ P.logc ∧ 0 ≤ P.mthin ∧
  x ^ (-ε) ≤ P.de2 ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.m ∧
  x * P.m ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.k ∧
  P.m * P.de2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.de1 ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.H ∧
  P.k * P.de2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.de1 * P.H * P.R ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.k ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.p0 ^ 2 ∧
  P.m * P.kap * x ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧
  P.k * P.b1 * P.Lrd ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.de1 * P.b ∧
  Real.exp (x ^ (ε / K)) ≤ x * P.b / P.b1 ∧
  2 ≤ P.hc ∧ P.hc ≤ K ∧ P.logc ≤ x ^ ε ∧
  P.mthin ≤ K * x ^ K ∧ P.mthin * x * x ^ (-P.hc) * P.logc ^ 6 ≤ K

end Formalism.D5
