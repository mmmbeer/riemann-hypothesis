import Formalism.WeightedDeltaMeans.LogBaseHeightBound
import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
import Formalism.LocalToGlobal.LatticeGeometry.ExtPtHt
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.SharpRestriction.Divisibility.ProductFirstParts
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.DegreeFormula.PointDegree.FlagDeg

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MvPolynomial Filter Topology

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtThmB (U : ShimU D G jC ng w) where

  hFl : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ →ₗ[ℝ] ℝ
  hFl_homog : ∀ (P : MvPolynomial (DV.Rt D.what₂.Tau w.N) ℝ) (d : ℕ),
    d ≠ Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1 → P.IsHomogeneous d → hFl P = 0

  PBs : ℝ → MvPolynomial (DV.Rt D.what₂.Tau w.N ⊕ Unit) ℝ

  PBsC : ℝ → U.Comp → MvPolynomial (DV.Rt D.what₂.Tau w.N ⊕ Unit) ℝ

  v0 : D.what₂.Tau → Fin w.N → ℝ

def extThmBJunk (U : ShimU D G jC ng w) : ExtThmB U where
  hFl := 0
  hFl_homog := fun _ _ _ _ => rfl
  PBs := fun _ => 0
  PBsC := fun _ _ => 0
  v0 := fun _ _ => 0

section Defs

variable (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

abbrev YU : DV.ShimX D.what₂.Tau := toShimX U h lev hlev

abbrev Wts (w : Dat D Lev) : Type := D.what₂.Tau → Fin w.N → ℝ

def RatW (lam : Wts w) : Prop := ∀ τ i, ∃ q : ℚ, lam τ i = q

variable {U}

def lamPP (E : ExtThmB U) (lam : Wts w) (s : ℚ) : Wts w := fun τ i => lam τ i - (s : ℝ) * E.v0 τ i

def hFlPoly (E : ExtThmB U) (lam : Wts w) : ℝ :=
  E.hFl (Formalism.DegreeFormula.linRoot lam ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1))

end Defs

section Reformulated

variable (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

def ThmBI3 (E : ExtThmB U) : Prop :=
  ∀ (B : ℝ) (lam : Wts w) (s : ℚ), 2 ≤ B → RatW lam → 0 < s → WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) →
    (∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs (YU U h lev hlev) (lamPP E lam s) ≤
      (B - 2) * WeightThresholdDefs.gap (YU U h lev hlev) (lamPP E lam s) τ) →
    (YU U h lev hlev).semipos ((YU U h lev hlev).Mbar B lam s) ∧
      (YU U h lev hlev).nefFib ((YU U h lev hlev).Mbar B lam s)

def ThmBI3R (E : ExtThmB U) : Prop :=
  ∀ Λ : ℝ, ∃ s0 : ℝ, 0 < s0 ∧ ∀ (B : ℝ) (lam : Wts w) (s : ℚ), 2 ≤ B → RatW lam →
    WeightThresholdDefs.supAbs (YU U h lev hlev) lam ≤ Λ → 0 < s → (s : ℝ) ≤ s0 →
    WeightThresholdDefs.Dominant (YU U h lev hlev) (lamPP E lam s) →
    (∀ τ, 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs (YU U h lev hlev) (lamPP E lam s) ≤
      (B - 2) * WeightThresholdDefs.gap (YU U h lev hlev) (lamPP E lam s) τ) →
    (YU U h lev hlev).semipos ((YU U h lev hlev).Mbar B lam s) ∧
      (YU U h lev hlev).nefFib ((YU U h lev hlev).Mbar B lam s)


end Reformulated

section Targets

variable (U : ShimU D G jC ng w) (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime)

end Targets

end Formalism.L2.Geo
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MvPolynomial Filter Topology Finset

namespace Formalism.L2.Geo

section Alg

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def smallBlock (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => j ≤ i.val)

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def a0Mu (j : ℕ) : Pol Ψ N := ∑ τ : Ψ, ∑ i ∈ smallBlock N j, X (τ, i)

def smallBlockPowerSum (j : ℕ) (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i ∈ smallBlock N j, X (τ, i) ^ k

def blockVandermondePolynomial (τ : Ψ) (S : Finset (Fin N)) : Pol Ψ N :=
  ∏ a ∈ S, ∏ b ∈ S.filter (fun b => a < b), (X (τ, a) - X (τ, b))

def fibreVandermondeProduct (j : ℕ) (cf : ℝ) : Pol Ψ N :=
  C cf * ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j))

def a0F (j n : ℕ) (cf : ℝ) : Pol Ψ N := a0Mu j ^ (n + 1) * fibreVandermondeProduct j cf

def a0JP (j n : ℕ) (cf : ℝ) : Pol Ψ N := a0Mu j ^ n * fibreVandermondeProduct j cf

def a0n (Ψ : Type) [Fintype Ψ] (N j : ℕ) : ℕ := Fintype.card Ψ * (j * (N - j))

end Alg

section AlgStmt

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def LargestBlockVandermondeVanishes : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (cf : ℝ) (τ : Ψ),
    ∑ i ∈ Formalism.ShimuraLimitIdentity.top N j, pderiv (τ, i) (a0F (Ψ := Ψ) (N := N) j n cf) = 0

def TotalDerivativeValue : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (cf : ℝ) (τ : Ψ),
    ∑ i : Fin N, pderiv (τ, i) (a0F (Ψ := Ψ) (N := N) j n cf) =
      C (((n : ℝ) + 1) * ((N - j : ℕ) : ℝ)) * a0JP j n cf

def TestPolynomialHomogeneous : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N j : ℕ) (cf : ℝ), j ≤ N →
    (a0F (Ψ := Ψ) (N := N) j (a0n Ψ N j) cf).IsHomogeneous (Formalism.DegreeFormula.dimFl Ψ N + 1)

def FlagIntegralNonzero : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N →
    degFlL Ψ N (a0JP (Ψ := Ψ) (N := N) j (a0n Ψ N j) 1) ≠ 0

def FlagIntegralAnnihilatesPowerSums : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), Kills (degFlL Ψ N)

def RestTermBound : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℝ) (Q : Ψ → ℕ → Pol Ψ N), j < N →
    a0F j (a0n Ψ N j) cf = ∑ σ : Ψ, ∑ k ∈ Icc 1 N, psumAt σ k * Q σ k →
    ∀ (τ τ' : Ψ) (k : ℕ), k ∈ Icc 2 N →
      |(k : ℝ) * degFlL Ψ N (smallBlockPowerSum j τ' (k - 1) * Q τ k)| ≤
        ((a0n Ψ N j : ℝ) + 1) * |degFlL Ψ N (a0JP j (a0n Ψ N j) cf)| *
          (2 * (((j * (N - j) : ℕ) : ℝ) + N)) ^ (k - 1) / (Nat.factorial k : ℝ)

def PrimeSumBound : Prop :=
  ∀ (Pr : Finset ℕ) (f N B0 X : ℝ) (K : ℕ), (∀ p ∈ Pr, p.Prime ∧ B0 < p) → 1 ≤ f → 2 ≤ N →
    4 * f * N ^ 2 ≤ B0 → 0 ≤ X → X ≤ 3 / 2 * N ^ 2 →
    ∑ p ∈ Pr, Real.log p *
      (f * ∑ k ∈ Icc 2 K, 2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (Nat.factorial k : ℝ)) ≤ 8 / 5

def TwistShapeProp {Ψ : Type} [Fintype Ψ] {N : ℕ} (j : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ) (vol : ℝ) (p : ℕ)
    (Q : Ψ → ℕ → Pol Ψ N) (rp : ℝ) : Prop :=
  ∃ (geo : Ψ → ℕ → ℝ) (Gt : ℕ → Ψ → ℕ → Pol Ψ N),
    rp = Real.log p * vol * ∑ τ : Ψ, ∑ k ∈ Icc 2 N, (k : ℝ) * geo τ k ∧
    (∀ τ k, HasSum (fun m : ℕ => (((p : ℝ) ^ k)⁻¹) ^ (m + 1) * I (Gt m τ k * Q τ k)) (geo τ k)) ∧
    ∀ m τ k, ∃ (τ' : Ψ) (s : ℝ) (H : Pol Ψ N), (s = 1 ∨ s = -1) ∧
      Gt m τ k = C s * smallBlockPowerSum j τ' (k - 1) + psumAt τ' (k - 1) * H

def RestBoundFromPrimeSum : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf vol B0 restF : ℝ)
    (Q : Ψ → ℕ → Pol Ψ N) (Pr : ℕ → Finset ℕ) (rp : ℕ → ℝ),
    RestTermBound → PrimeSumBound → Kills (degFlL Ψ N) →
    j < N → 2 ≤ N → 0 < vol → 4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 ≤ B0 →
    a0F j (a0n Ψ N j) cf = ∑ σ : Ψ, ∑ k ∈ Icc 1 N, psumAt σ k * Q σ k →
    (∀ B, ∀ p ∈ Pr B, p.Prime ∧ B0 < p) →
    (∀ B, ∀ p ∈ Pr B, TwistShapeProp j (degFlL Ψ N) vol p Q (rp p)) →
    Tendsto (fun B => ∑ p ∈ Pr B, rp p) atTop (𝓝 restF) →
    |restF| ≤ 8 / 5 * (((a0n Ψ N j : ℝ) + 1) * vol * |degFlL Ψ N (a0JP j (a0n Ψ N j) cf)|)

def CauchyBinetHadamard : Prop :=
  ∀ (a b : ℕ) (Z : Matrix (Fin a) (Fin b) ℂ), (∀ i k, ‖Z i k‖ = 1) →
    1 / 2 * Real.log (Matrix.det (1 + Z * Z.conjTranspose)).re ≤ (a : ℝ) / 2 * Real.log (1 + b)

def LowerBoundFromTermBounds : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [Nonempty Ψ] (N j jp n : ℕ) (PPF hhF restF vol J K1 Ca Λ : ℝ)
    (A0 b0 ShF TotF : Ψ → ℝ),
    N = j + jp → 1 ≤ jp → 2 * jp ≤ N → 0 < vol → 0 < J → 0 ≤ K1 → 0 ≤ Ca → 1 ≤ Λ →
    Real.log ((N : ℝ) + 1) ≤ Λ →
    PPF = vol * (hhF - (∑ τ, A0 τ * ShF τ) - (∑ τ, b0 τ * TotF τ)) + restF →
    (∀ τ, ShF τ = 0) → (∀ τ, TotF τ = ((n : ℝ) + 1) * jp * J) →
    -(((n : ℝ) + 1) * vol * J * (Ca * (Fintype.card Ψ : ℝ) * jp * Λ)) ≤ PPF →
    hhF ≤ ((n : ℝ) + 1) * J * ((Fintype.card Ψ : ℝ) * (jp / 2 * Real.log ((N : ℝ) + 1))) →
    |restF| ≤ 8 / 5 * (((n : ℝ) + 1) * vol * J) →
    (∀ τ, |(j : ℝ) * A0 τ + (N : ℝ) * b0 τ| ≤ K1 * N * Λ) →
    (∀ τ σ, A0 τ = A0 σ) →
    ∀ τ, -((2 * K1 + 2 * Ca + 21 / 5) * Λ) ≤ A0 τ

def LowerBoundHypothesis {Ψ : Type} (A0 : Ψ → ℝ) (K2 Λ : ℝ) : Prop := ∀ τ, -(K2 * Λ) ≤ A0 τ

end AlgStmt

section Geo

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtensionData (U : ShimU D G jC ng w) where

  Xb : U.Comp → G.Var

  PtX : U.Comp → Type

  bdX : ∀ c, PtX c → Prop

  htX : ∀ c, G.Adl (Xb c) → PtX c → ℝ

  degX : ∀ c, G.Adl (Xb c) → ℝ

  semiposX : ∀ c, G.Adl (Xb c) → Prop
  nefFibX : ∀ c, G.Adl (Xb c) → Prop
  ampleX : ∀ c, G.Adl (Xb c) → Prop

  muC : ℝ → ℝ → ℝ → ∀ c, G.Adl (Xb c)

  arLim : ℝ → U.Comp → ℝ

  degMu : U.Comp → ℝ

  meanU : U.Comp → ℝ

  fdeg : ℝ

def trivialExtensionData (U : ShimU D G jC ng w) : ExtensionData U where
  Xb := U.alg.Yv
  PtX := fun _ => Empty
  bdX := fun _ _ => False
  htX := fun _ _ _ => 0
  degX := fun _ _ => 0
  semiposX := fun _ _ => True
  nefFibX := fun _ _ => True
  ampleX := fun _ _ => False
  muC := fun B _ _ c => U.alg.Mbar B 0 0 c
  arLim := fun _ _ => 0
  degMu := fun _ => 1
  meanU := fun _ => 0
  fdeg := 1

section Props

variable (U : ShimU D G jC ng w) (X : ExtensionData U)

abbrev fA (D : D7) : ℝ := (Fintype.card D.what₂.Tau : ℝ)

abbrev jpA (w : Dat D Lev) : ℝ := ((w.N - w.j : ℕ) : ℝ)

abbrev nA (w : Dat D Lev) : ℕ := a0n D.what₂.Tau w.N w.j

def JA (w : Dat D Lev) (cf : ℝ) : ℝ := by
  classical
  exact degFlL D.what₂.Tau w.N (a0JP w.j (nA w) cf)

abbrev FA (w : Dat D Lev) (cf : ℝ) : Pol D.what₂.Tau w.N := a0F w.j (nA w) cf

def ZhangLowerXProp : Prop :=
  ∀ (c : U.Comp) (Lb : G.Adl (X.Xb c)), X.semiposX c Lb → X.nefFibX c Lb → X.ampleX c Lb →
    ∀ e : ℝ, (∀ y, e ≤ X.htX c Lb y) → ((G.dim (X.Xb c) : ℝ) + 1) * e * X.degX c Lb ≤ G.arTop (X.Xb c) Lb

def DimXProp : Prop := ∀ c, G.dim (X.Xb c) = nA w

def CuspBundlePosProp : Prop :=
  ∀ B : ℝ, 4 * fA D ≤ B - 2 → ∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 → ∀ c,
    X.semiposX c (X.muC B ep t' c) ∧ X.nefFibX c (X.muC B ep t' c) ∧ X.ampleX c (X.muC B ep t' c)

def HtInteriorProp (Ch K rd Lchi : ℝ) : Prop :=
  ∀ B : ℝ, 4 * fA D * (w.N : ℝ) ^ 2 ≤ B → ∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 → ∀ c y, ¬ X.bdX c y →
    -(Ch * fA D * jpA w * (Real.log (B * rd) + Lchi)) - ep * K ≤ X.htX c (X.muC B ep t' c) y

def HtBoundaryProp (Ch K rd Lchi : ℝ) : Prop :=
  ∀ B : ℝ, 4 * fA D * (w.N : ℝ) ^ 2 ≤ B → ∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 → ∀ c y, X.bdX c y →
    -(Ch * fA D * jpA w * (Real.log (B * rd) + Lchi)) - ep * K ≤ X.htX c (X.muC B ep t' c) y

def StokesLimitProp (K : ℝ) : Prop :=
  ∀ B : ℝ, 4 * fA D ≤ B - 2 → ∀ (c : U.Comp) (a : ℝ),
    (∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 →
      ((nA w : ℝ) + 1) * (a - ep * K) * X.degX c (X.muC B ep t' c) ≤ G.arTop (X.Xb c) (X.muC B ep t' c)) →
    ((nA w : ℝ) + 1) * (a - X.meanU c / 2) * X.degMu c ≤ X.arLim B c

def CuspMeanProp (Cu rd Lchi : ℝ) : Prop :=
  1 ≤ w.N - w.j → 3 * (w.N - w.j) + 1 ≤ w.N → ∀ B : ℝ, 4 * fA D * (w.N : ℝ) ^ 2 ≤ B → ∀ c,
    X.meanU c ≤ Cu * fA D * jpA w * (Real.log (B * rd) + Lchi)

def PushDownProp (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) (cf B : ℝ) : Prop :=
  PPf (FA w cf) = cf * X.fdeg * ∑ c, X.arLim B c ∧
    (∀ c, cf * X.fdeg * X.degMu c = U.cx.volC c * JA w cf) ∧ ∀ c, 0 < X.degMu c

def PolarTie (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime) (B : ℝ)
    (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) : Prop :=
  (∀ (P : Pol D.what₂.Tau w.N) (d : ℕ), d ≠ WeightThresholdDefs.dimY (YU U h lev hlev) + 1 → P.IsHomogeneous d → PPf P = 0) ∧
    ∀ lam : Wts w, PPf (Formalism.DegreeFormula.linRoot lam ^ (WeightThresholdDefs.dimY (YU U h lev hlev) + 1)) = product_first_partition.PB (YU U h lev hlev) B lam

def GrassmannianHeightBound (E : ExtThmB U) (cf : ℝ) : Prop :=
  0 < JA w cf → ∀ e : ℝ, (∀ Z : Matrix (Fin (w.N - w.j)) (Fin w.j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (Matrix.det (1 + Z * Z.conjTranspose)).re ≤ e) →
    E.hFl (FA w cf) ≤ ((nA w : ℝ) + 1) * JA w cf * (fA D * e)

end Props

section Assembly

variable (U : ShimU D G jC ng w)

def SlopeLowerBoundFromPluckerHeights : Prop :=
  ∀ (X : ExtensionData U) (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) (cf B rd Lchi Ch Cu K : ℝ),
    0 < Fintype.card D.what₂.Tau → 1 ≤ w.N - w.j → 3 * (w.N - w.j) + 1 ≤ w.N →
    4 * fA D * (w.N : ℝ) ^ 2 ≤ B → 1 ≤ rd → 0 ≤ Lchi → 0 ≤ Ch → 0 ≤ Cu → 0 < JA w cf →
    ZhangLowerXProp U X → DimXProp U X → CuspBundlePosProp U X → HtInteriorProp U X Ch K rd Lchi →
    HtBoundaryProp U X Ch K rd Lchi → StokesLimitProp U X K → CuspMeanProp U X Cu rd Lchi →
    PushDownProp U X PPf cf B →
    -(((nA w : ℝ) + 1) * U.cx.vol * JA w cf *
        ((Ch + Cu / 2) * fA D * jpA w * (Real.log (B * rd) + Lchi))) ≤ PPf (FA w cf)

open Classical in

def LowerBoundOnShimura : Prop :=
  ∀ (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime) (E : ExtThmB U) (X : ExtensionData U)
    (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) (rest : Pol D.what₂.Tau w.N → ℝ) (A0 b0 : D.what₂.Tau → ℝ)
    (cf B0 rd Lchi Ch Cu K K1 : ℝ) (Q : Pol D.what₂.Tau w.N) (Qd : D.what₂.Tau → ℕ → Pol D.what₂.Tau w.N)
    (Pr : ℕ → Finset ℕ) (rp : ℕ → ℝ),

    LargestBlockVandermondeVanishes → TotalDerivativeValue → TestPolynomialHomogeneous → FlagIntegralAnnihilatesPowerSums → RestTermBound → PrimeSumBound → RestBoundFromPrimeSum →
    CauchyBinetHadamard → LowerBoundFromTermBounds → SlopeLowerBoundFromPluckerHeights U →

    0 < Fintype.card D.what₂.Tau → 1 ≤ w.N - w.j → 3 * (w.N - w.j) + 1 ≤ w.N →
    4 * fA D * (w.N : ℝ) ^ 2 ≤ B0 → 1 ≤ rd → 0 ≤ Lchi → 0 ≤ K1 → 0 ≤ Ch → 0 ≤ Cu → 0 < JA w cf →

    PolarTie U h lev hlev B0 PPf →
    (∀ F : Pol D.what₂.Tau w.N, F.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1) →
      PPf F = U.cx.vol * (E.hFl F - (∑ τ, A0 τ * Sh (degFlL D.what₂.Tau w.N) w.j τ F)
        - (∑ τ, b0 τ * Tot (degFlL D.what₂.Tau w.N) τ F)) + rest F) →

    Q.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N) → degFlL D.what₂.Tau w.N Q = 1 →
    (∀ τ, E.hFl (psumAt τ 1 * Q) = 0) → (∀ τ, rest (psumAt τ 1 * Q) = 0) →
    (∀ τ, |PPf (psumAt τ 1 * Q)| ≤ U.cx.vol * (K1 * (w.N : ℝ) * (Real.log (B0 * rd) + Lchi))) →

    (∀ τ σ, A0 τ = A0 σ) →

    FA w cf = ∑ σ, ∑ k ∈ Icc 1 w.N, psumAt σ k * Qd σ k →
    (∀ B, ∀ p ∈ Pr B, p.Prime ∧ B0 < p) →
    (∀ B, ∀ p ∈ Pr B, TwistShapeProp w.j (degFlL D.what₂.Tau w.N) U.cx.vol p Qd (rp p)) →
    Tendsto (fun B => ∑ p ∈ Pr B, rp p) atTop (𝓝 (rest (FA w cf))) →

    ZhangLowerXProp U X → DimXProp U X → CuspBundlePosProp U X → HtInteriorProp U X Ch K rd Lchi →
    HtBoundaryProp U X Ch K rd Lchi → StokesLimitProp U X K → CuspMeanProp U X Cu rd Lchi →
    PushDownProp U X PPf cf B0 → GrassmannianHeightBound U E cf →
    LowerBoundHypothesis A0 (2 * K1 + 2 * Ch + Cu + 21 / 5) (Real.log (B0 * rd) + Lchi)

end Assembly


end Geo

end Formalism.L2.Geo
end
end

section
noncomputable section

open Finset MvPolynomial

namespace Formalism.L2.Geo

namespace BlockVandermondeForms

open Formalism.ShimuraLimitIdentity (Pol psumAt)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def dS (τ : Ψ) (S : Finset (Fin N)) : Derivation ℝ (Pol Ψ N) (Pol Ψ N) := ∑ i ∈ S, pderiv (τ, i)

theorem dS_apply (τ : Ψ) (S : Finset (Fin N)) (P : Pol Ψ N) : dS τ S P = ∑ i ∈ S, pderiv (τ, i) P := by
  classical
  unfold dS
  refine Finset.induction_on S (by simp) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

theorem dS_X (τ : Ψ) (S : Finset (Fin N)) (σ : Ψ) (a : Fin N) :
    dS τ S (X (σ, a)) = if σ = τ ∧ a ∈ S then 1 else 0 := by
  rw [dS_apply]
  simp only [pderiv_X]
  by_cases h : σ = τ ∧ a ∈ S
  · obtain ⟨rfl, ha⟩ := h
    rw [if_pos ⟨rfl, ha⟩, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · intro h'
      exact absurd ha h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Pi.single_apply, if_neg]
    intro he
    simp only [Prod.mk.injEq] at he
    exact h ⟨he.1, by rw [he.2]; exact hi⟩

theorem d_prod_zero (D : Derivation ℝ (Pol Ψ N) (Pol Ψ N)) {ι : Type*} (s : Finset ι) (f : ι → Pol Ψ N)
    (h : ∀ i ∈ s, D (f i) = 0) : D (∏ i ∈ s, f i) = 0 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by rw [Finset.prod_empty, Derivation.map_one_eq_zero]) ?_
  intro a t ha ih h
  rw [Finset.prod_insert ha, Derivation.leibniz, h a (Finset.mem_insert_self a t),
    ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), smul_zero, smul_zero, add_zero]

private theorem card_filter_fin_val_eq_card_filter_range (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin N => p i.val)).card = ((Finset.range N).filter p).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun x => if p x then 1 else 0) N

theorem card_smallBlock (N j : ℕ) : (smallBlock N j).card = N - j := by
  unfold smallBlock
  rw [card_filter_fin_val_eq_card_filter_range N (fun x => j ≤ x)]
  have e : (Finset.range N).filter (fun x => j ≤ x) = Finset.Ico j N := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e, Nat.card_Ico]

theorem card_top (N j : ℕ) (hj : j ≤ N) : (Formalism.ShimuraLimitIdentity.top N j).card = j := by
  unfold Formalism.ShimuraLimitIdentity.top
  rw [card_filter_fin_val_eq_card_filter_range N (fun x => x < j)]
  have e : (Finset.range N).filter (fun x => x < j) = Finset.range j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [e, Finset.card_range]

end BlockVandermondeForms

open BlockVandermondeForms

theorem flag_integral_kills_power_sums : FlagIntegralAnnihilatesPowerSums := by
  intro Ψ _ _ N τ k hk G
  simp only [degFlL, LinearMap.smul_apply, LinearMap.sum_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]
  rw [mul_eq_zero]
  right
  have h : ∀ σ : Ψ → Equiv.Perm (Fin N),
      (∏ t, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ)) * (Formalism.ShimuraLimitIdentity.psumAt τ k * G).coeff (Formalism.DegreeFormula.permExp σ) =
        ∑ j : Fin N, Formalism.DegreeFormula.PPowSum.sgnP σ *
          (X (τ, (σ τ).symm j) ^ k * G).coeff (Formalism.DegreeFormula.permExp σ) := by
    intro σ
    rw [Formalism.ShimuraLimitIdentity.psumAt, Finset.sum_mul, coeff_sum, Finset.mul_sum]
    exact (Equiv.sum_comp (σ τ).symm
      (fun i => Formalism.DegreeFormula.PPowSum.sgnP σ * (X (τ, i) ^ k * G).coeff (Formalism.DegreeFormula.permExp σ))).symm
  rw [Finset.sum_congr rfl fun σ _ => h σ, Finset.sum_comm]
  exact Finset.sum_eq_zero fun j _ => Formalism.DegreeFormula.PPowSum.slice τ k hk G j

namespace BlockVandermondeForms

theorem pairs_eq {N : ℕ} (S : Finset (Fin N)) :
    ∑ a ∈ S, (S.filter (fun b => a < b)).card = S.card.choose 2 := by
  refine Finset.induction_on_max S (by simp) fun m S hm ih => ?_
  have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
  rw [Finset.sum_insert hmS, Finset.card_insert_of_notMem hmS]
  have h1 : ((insert m S).filter (fun b => m < b)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact lt_irrefl _
    · exact fun h => lt_asymm h (hm x hx)
  have h2 : ∀ a ∈ S, ((insert m S).filter (fun b => a < b)).card = (S.filter (fun b => a < b)).card + 1 := by
    intro a ha
    rw [Finset.filter_insert, if_pos (hm a ha),
      Finset.card_insert_of_notMem (fun h => hmS (Finset.mem_filter.mp h).1)]
  rw [h1, zero_add, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ih, Finset.sum_const, smul_eq_mul, mul_one,
    Nat.choose_succ_succ', Nat.choose_one_right]
  simp only [Nat.reduceAdd]
  omega

theorem add_choose_two (a b : ℕ) : (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  have hs : ∀ k : ℕ, (k + 1).choose 2 = k.choose 2 + k := fun k => by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    simp only [Nat.reduceAdd]
    omega
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, hs, hs, ih]
    ring

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem vdm_homog (τ : Ψ) (S : Finset (Fin N)) : (blockVandermondePolynomial τ S).IsHomogeneous (S.card.choose 2) := by
  unfold blockVandermondePolynomial
  rw [← pairs_eq S]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun a _ => ?_
  rw [Finset.card_eq_sum_ones]
  exact MvPolynomial.IsHomogeneous.prod _ _ _ fun b _ => (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)

end BlockVandermondeForms

end Formalism.L2.Geo
end
end

section
noncomputable section

open Finset MvPolynomial

namespace Formalism.L2.Geo

namespace WeylPolynomialAlgebra

section Polar

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

def Qp (ℓ : ι → R) (s : Finset ι) (k : ℕ) : R :=
  ∑ S ∈ s.powerset, (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k

theorem Qp_insert (ℓ : ι → R) (a : ι) (s : Finset ι) (ha : a ∉ s) (k : ℕ) :
    Qp ℓ (insert a s) k = ∑ m ∈ range k, (k.choose (m + 1) : R) * ℓ a ^ (m + 1) * Qp ℓ s (k - 1 - m) := by
  unfold Qp
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have h1 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card + 1 - S.card) * (∑ i ∈ S, ℓ i) ^ k =
      -((-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k) := by
    intro S hS
    have hc : S.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
    rw [show s.card + 1 - S.card = (s.card - S.card) + 1 by omega, pow_succ]
    ring
  have h2 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card + 1 - (insert a S).card) * (∑ i ∈ insert a S, ℓ i) ^ k =
      (-1) ^ (s.card - S.card) * (ℓ a + ∑ i ∈ S, ℓ i) ^ k := by
    intro S hS
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.card_insert_of_notMem haS, Finset.sum_insert haS,
      show s.card + 1 - (S.card + 1) = s.card - S.card by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib, ← sub_eq_neg_add,
    ← Finset.sum_sub_distrib]
  have h3 : ∀ S ∈ s.powerset, (-1 : R) ^ (s.card - S.card) * (ℓ a + ∑ i ∈ S, ℓ i) ^ k -
      (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ k =
      ∑ m ∈ range k, (k.choose (m + 1) : R) * ℓ a ^ (m + 1) *
        ((-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ (k - 1 - m)) := by
    intro S _
    rw [add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    rw [mul_add, add_sub_cancel_right, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m < k := Finset.mem_range.mp hm
    rw [show k - (m + 1) = k - 1 - m by omega]
    ring
  rw [Finset.sum_congr rfl h3, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]

theorem Qp_eq (ℓ : ι → R) (s : Finset ι) : ∀ k ≤ s.card,
    Qp ℓ s k = if k = s.card then (s.card.factorial : R) * ∏ i ∈ s, ℓ i else 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp [Qp]
  | insert a s ha ih =>
    intro k hk
    rw [Finset.card_insert_of_notMem ha] at hk ⊢
    rw [Qp_insert ℓ a s ha k]
    by_cases hks : k = s.card + 1
    · subst hks
      rw [if_pos rfl, Finset.sum_eq_single 0]
      · rw [ih _ (by omega), if_pos (by omega), Finset.prod_insert ha, Nat.factorial_succ]
        push_cast
        simp only [Nat.choose_one_right, zero_add, pow_one]
        push_cast
        ring
      · intro m hm hm0
        have := Finset.mem_range.mp hm
        rw [ih _ (by omega), if_neg (by omega), mul_zero]
      · intro h; simp at h
    · rw [if_neg hks]
      refine Finset.sum_eq_zero (fun m hm => ?_)
      have hm' : m < k := Finset.mem_range.mp hm
      rw [ih _ (by omega), if_neg (by omega), mul_zero]

theorem polarization (ℓ : ι → R) (s : Finset ι) :
    (s.card.factorial : R) * ∏ i ∈ s, ℓ i =
      ∑ S ∈ s.powerset, (-1) ^ (s.card - S.card) * (∑ i ∈ S, ℓ i) ^ s.card := by
  have := Qp_eq ℓ s s.card le_rfl
  rw [if_pos rfl] at this
  exact this.symm

end Polar

section Apol

variable {σ : Type*}

def apol (P g : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ P.support, P.coeff m * g.coeff m * (m.prod fun _ e => (e.factorial : ℝ))

theorem apol_add (P g h : MvPolynomial σ ℝ) : apol P (g + h) = apol P g + apol P h := by
  unfold apol; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun m _ => ?_); rw [coeff_add]; ring

theorem apol_smul (P g : MvPolynomial σ ℝ) (c : ℝ) : apol P (c • g) = c * apol P g := by
  unfold apol; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun m _ => ?_); rw [coeff_smul, smul_eq_mul]; ring

theorem apol_self_pos (P : MvPolynomial σ ℝ) (hP : P ≠ 0) : 0 < apol P P := by
  unfold apol
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hP)
  refine Finset.sum_pos (fun m hm => ?_) ⟨m, hm⟩
  have h1 : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h2 : 0 < m.prod fun _ e => (e.factorial : ℝ) :=
    Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (Nat.factorial_pos _))
  have h3 : 0 < P.coeff m * P.coeff m := mul_self_pos.mpr h1
  positivity

end Apol

end WeylPolynomialAlgebra

namespace WeylPolynomialAlgebra

section ApolPow

variable {σ : Type*} [Fintype σ]

theorem apol_pow (P : MvPolynomial σ ℝ) (d : ℕ) (hP : P.IsHomogeneous d) (a : σ → ℝ) :
    apol P ((∑ i, a i • X i : MvPolynomial σ ℝ) ^ d) = (d.factorial : ℝ) * eval a P := by
  unfold apol
  rw [MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hdeg : (m.sum fun _ e => e) = d := by
    have := hP (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.degree, Finsupp.sum, Finsupp.weight_apply] using this
  rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
  have hspec := Nat.multinomial_spec m.support m
  have hsum : ∑ i ∈ m.support, m i = d := by simpa [Finsupp.sum] using hdeg
  rw [hsum] at hspec
  simp only [Finsupp.prod, Finsupp.multinomial_eq]
  have hcast : (∏ i ∈ m.support, ((m i).factorial : ℝ)) * (Nat.multinomial m.support m : ℝ) =
      (d.factorial : ℝ) := by exact_mod_cast hspec
  rw [← hcast]
  ring

end ApolPow

open Formalism.ShimuraLimitIdentity (Pol)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def idxS (Ψ : Type) [Fintype Ψ] (N j : ℕ) : Finset (Ψ × Fin N × Fin N) :=
  univ.filter (fun t => t.2.1 < t.2.2 ∧ (t.2.1.val < j ↔ t.2.2.val < j))

def idxC (Ψ : Type) [Fintype Ψ] (N j : ℕ) : Finset (Ψ × Fin N × Fin N) :=
  univ.filter (fun t => t.2.1 < t.2.2 ∧ ¬ (t.2.1.val < j ↔ t.2.2.val < j))

def ell (t : Ψ × Fin N × Fin N) : Pol Ψ N := X (t.1, t.2.1) - X (t.1, t.2.2)

def nuT (t : Ψ × Fin N × Fin N) : Ψ → Fin N → ℝ := fun τ i =>
  (if (τ, i) = (t.1, t.2.2) then 1 else 0) - (if (τ, i) = (t.1, t.2.1) then 1 else 0)

theorem linRoot_nuT (t : Ψ × Fin N × Fin N) : Formalism.DegreeFormula.linRoot (nuT t) = ell t := by
  unfold Formalism.DegreeFormula.linRoot nuT ell
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib, neg_sub]
  have h : ∀ y : Ψ × Fin N, (∑ x : Ψ × Fin N, C (if (x.1, x.2) = y then (1 : ℝ) else 0) * X x) = X y := by
    intro y
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; rw [if_neg (by simpa using hb)]; simp
    · simp
  rw [h, h]

theorem linRoot_add (l1 l2 : Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot (l1 + l2) = Formalism.DegreeFormula.linRoot l1 + Formalism.DegreeFormula.linRoot l2 := by
  unfold Formalism.DegreeFormula.linRoot
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, neg_add]

theorem linRoot_sum {α : Type*} (s : Finset α) (l : α → Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot (∑ a ∈ s, l a) = ∑ a ∈ s, Formalism.DegreeFormula.linRoot (l a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.DegreeFormula.linRoot]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linRoot_add, ih]

theorem linRoot_smul (c : ℝ) (l : Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot (c • l) = C c * Formalism.DegreeFormula.linRoot l := by
  unfold Formalism.DegreeFormula.linRoot
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_neg]
  congr 1; refine Finset.sum_congr rfl (fun x _ => ?_); ring

theorem fib_eq (j : ℕ) :
    fibreVandermondeProduct (Ψ := Ψ) (N := N) j 1 = ∏ t ∈ idxS Ψ N j, ell t := by
  classical
  unfold fibreVandermondeProduct blockVandermondePolynomial idxS ell
  rw [map_one, one_mul, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  unfold Formalism.ShimuraLimitIdentity.top smallBlock
  simp only [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  by_cases ha : a.val < j
  · have ha' : ¬ j ≤ a.val := by omega
    simp only [ha, ha', if_true, if_false, mul_one]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    by_cases hb : b.val < j
    · simp [hb]
    · simp [hb]
  · have ha' : j ≤ a.val := by omega
    simp only [ha, ha', if_true, if_false, one_mul]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    by_cases hb : j ≤ b.val
    · have hb' : ¬ b.val < j := by omega
      simp [hb, hb']
    · have hb' : b.val < j := by omega
      simp [hb, hb']

end WeylPolynomialAlgebra

namespace WeylPolynomialAlgebra

open Formalism.ShimuraLimitIdentity (Pol)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def eW (Ψ : Type) (N j : ℕ) : Ψ → Fin N → ℝ := fun _ i => if j ≤ i.val then -1 else 0

theorem linRoot_eW (j : ℕ) : Formalism.DegreeFormula.linRoot (eW Ψ N j) = a0Mu (Ψ := Ψ) (N := N) j := by
  unfold Formalism.DegreeFormula.linRoot eW a0Mu smallBlock
  rw [← Finset.sum_neg_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

theorem degFlL_C_mul (a : ℝ) (P : Pol Ψ N) : degFlL Ψ N (C a * P) = a * degFlL Ψ N P := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem weyl_coeff (j : ℕ) (ν : Ψ → Fin N → ℝ) (n k : ℕ) (hD : Formalism.DegreeFormula.dimFl Ψ N = n + k)
    (hk : (idxS Ψ N j).card = k) :
    ((Formalism.DegreeFormula.dimFl Ψ N).choose n : ℝ) * degFlL Ψ N (a0Mu j ^ n * Formalism.DegreeFormula.linRoot ν ^ k) =
      ((Formalism.DegreeFormula.dimFl Ψ N).factorial : ℝ) *
        ((∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
          ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) := by
  set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef
  set μ : Pol Ψ N := a0Mu j with hμ
  set L : Pol Ψ N := Formalism.DegreeFormula.linRoot ν with hL
  have hW : ∀ ε : ℝ, degFlL Ψ N ((μ + C ε * L) ^ D) =
      (D.factorial : ℝ) * Formalism.DegreeFormula.weylProd (eW Ψ N j + ε • ν) := by
    intro ε
    have h := Formalism.DegreeFormula.flagDegFormula_statement Ψ N (eW Ψ N j + ε • ν)
    unfold Formalism.DegreeFormula.flagDeg at h
    rw [linRoot_add, linRoot_smul, linRoot_eW] at h
    rw [degFlL_apply]; exact h

  set PL : Polynomial ℝ := ∑ m ∈ range (D + 1),
    Polynomial.C ((D.choose m : ℝ) * degFlL Ψ N (μ ^ m * L ^ (D - m))) * Polynomial.X ^ (D - m) with hPLdef
  have hPL : ∀ ε : ℝ, PL.eval ε = degFlL Ψ N ((μ + C ε * L) ^ D) := by
    intro ε
    rw [add_pow, map_sum, hPLdef, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have e : μ ^ m * (C ε * L) ^ (D - m) * ((D.choose m : ℕ) : Pol Ψ N) =
        C (ε ^ (D - m) * (D.choose m : ℝ)) * (μ ^ m * L ^ (D - m)) := by
      rw [map_mul, map_pow, map_natCast]; ring
    rw [e, degFlL_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

  set F : Ψ × Fin N × Fin N → Polynomial ℝ := fun t =>
    if t.2.1 < t.2.2 then Polynomial.C ((eW Ψ N j t.1 t.2.1 - eW Ψ N j t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) +
      Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1 with hFdef
  set PR : Polynomial ℝ := Polynomial.C (D.factorial : ℝ) * ∏ t, F t with hPRdef
  have hPR : ∀ ε : ℝ, PR.eval ε = (D.factorial : ℝ) * Formalism.DegreeFormula.weylProd (eW Ψ N j + ε • ν) := by
    intro ε
    rw [hPRdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Formalism.DegreeFormula.weylProd,
      Fintype.prod_prod_type]
    congr 1
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
    simp only [hFdef]
    split_ifs
    · simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    · simp
  have hPLR : PL = PR := Polynomial.funext (fun ε => by rw [hPL, hPR, hW])

  have hcL : PL.coeff k = (D.choose n : ℝ) * degFlL Ψ N (μ ^ n * L ^ k) := by
    rw [hPLdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one, show D - n = k by omega]
    · intro m hm hmn
      have := Finset.mem_range.mp hm
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hsplit : ∀ t, F t = (if t ∈ idxS Ψ N j then
      Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1) *
      (if t ∈ idxC Ψ N j then Polynomial.C (1 / ((t.2.2 : ℝ) - t.2.1)) +
        Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X else 1) := by
    intro t
    simp only [hFdef, idxS, idxC, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hab : t.2.1 < t.2.2
    · by_cases hs : (t.2.1.val < j ↔ t.2.2.val < j)
      · have he : eW Ψ N j t.1 t.2.1 = eW Ψ N j t.1 t.2.2 := by
          unfold eW
          by_cases h1 : j ≤ t.2.1.val
          · have h2 : j ≤ t.2.2.val := by omega
            simp [h1, h2]
          · have h2 : ¬ j ≤ t.2.2.val := by omega
            simp [h1, h2]
        simp only [hab, hs, and_self, if_true, not_true, and_false, if_false, mul_one, he, sub_self, zero_div,
          map_zero, zero_add]
      · have h1 : t.2.1.val < j := by
          by_contra h; apply hs; have : (t.2.1 : ℕ) < t.2.2 := hab; constructor <;> intro h' <;> omega
        have h2 : j ≤ t.2.2.val := by
          by_contra h; apply hs; constructor <;> intro _ <;> omega
        have he : eW Ψ N j t.1 t.2.1 - eW Ψ N j t.1 t.2.2 = 1 := by
          unfold eW; rw [if_neg (by omega), if_pos h2]; norm_num
        simp only [hab, hs, and_false, if_false, one_mul, not_false_eq_true, and_self, if_true, he]
    · simp [hab]
  have hcR : PR.coeff k = (D.factorial : ℝ) *
      ((∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
        ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) := by
    rw [hPRdef, Finset.prod_congr rfl (fun t _ => hsplit t), Finset.prod_mul_distrib,
      Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter, Finset.prod_mul_distrib,
      Finset.prod_const, ← map_prod]
    set Q : Polynomial ℝ := ∏ t ∈ idxC Ψ N j, (Polynomial.C (1 / ((t.2.2 : ℝ) - t.2.1)) +
        Polynomial.C ((ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) * Polynomial.X) with hQ
    have hQ0 : Q.coeff 0 = ∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1) := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hQ, Polynomial.eval_prod]
      refine Finset.prod_congr rfl (fun t _ => ?_)
      simp
    have e : Polynomial.C (D.factorial : ℝ) *
        (Polynomial.C (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
          Polynomial.X ^ (idxS Ψ N j).card * Q) =
        Polynomial.C ((D.factorial : ℝ) * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1)) *
          (Polynomial.X ^ (idxS Ψ N j).card * Q) := by
      rw [map_mul]; ring
    rw [e, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', if_pos hk.le, hk, Nat.sub_self, hQ0]
    ring
  rw [← hcL, hPLR, hcR]

end WeylPolynomialAlgebra

namespace WeylPolynomialAlgebra

open Formalism.ShimuraLimitIdentity (Pol)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def apolL {σ : Type*} (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ where
  toFun := apol P
  map_add' := apol_add P
  map_smul' c g := by rw [apol_smul]; rfl

def PhiL (j n : ℕ) : Pol Ψ N →ₗ[ℝ] ℝ := (degFlL Ψ N).comp (LinearMap.mulLeft ℝ (a0Mu j ^ n))

theorem PhiL_apply (j n : ℕ) (g : Pol Ψ N) : PhiL j n g = degFlL Ψ N (a0Mu j ^ n * g) := rfl

theorem PhiL_C_mul (j n : ℕ) (a : ℝ) (g : Pol Ψ N) : PhiL j n (C a * g) = a * PhiL j n g := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem apolL_C_mul {σ : Type*} (P : MvPolynomial σ ℝ) (a : ℝ) (g : MvPolynomial σ ℝ) :
    apolL P (C a * g) = a * apolL P g := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem linRoot_eq_smul (ν : Ψ → Fin N → ℝ) :
    Formalism.DegreeFormula.linRoot ν = ∑ x : Ψ × Fin N, (-ν x.1 x.2) • (X x : Pol Ψ N) := by
  unfold Formalism.DegreeFormula.linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]

theorem ell_homog (t : Ψ × Fin N × Fin N) : (ell t : Pol Ψ N).IsHomogeneous 1 :=
  (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)

theorem fib_homog (j : ℕ) : (∏ t ∈ idxS Ψ N j, ell t : Pol Ψ N).IsHomogeneous (idxS Ψ N j).card := by
  have := IsHomogeneous.prod (idxS Ψ N j) (fun t => (ell t : Pol Ψ N)) (fun _ => 1) (fun t _ => ell_homog t)
  simpa using this

theorem fib_ne_zero (j : ℕ) : (∏ t ∈ idxS Ψ N j, ell t : Pol Ψ N) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro t ht
  have hab : t.2.1 < t.2.2 := (Finset.mem_filter.mp ht).2.1
  unfold ell
  rw [sub_ne_zero]
  intro h
  have := MvPolynomial.X_injective (σ := Ψ × Fin N) (R := ℝ) h
  simp only [Prod.mk.injEq, true_and] at this
  exact absurd this hab.ne

theorem eval_fib (j : ℕ) (v : Ψ × Fin N → ℝ) :
    eval v (∏ t ∈ idxS Ψ N j, ell t : Pol Ψ N) = ∏ t ∈ idxS Ψ N j, (v (t.1, t.2.1) - v (t.1, t.2.2)) := by
  rw [map_prod]; refine Finset.prod_congr rfl (fun t _ => ?_); simp [ell]

theorem dim_split (j : ℕ) (hj : j ≤ N) :
    Formalism.DegreeFormula.dimFl Ψ N = a0n Ψ N j + (idxS Ψ N j).card := by
  have h2 : (∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j) : Pol Ψ N)).IsHomogeneous
      (∑ _τ : Ψ, (j.choose 2 + (N - j).choose 2)) := by
    refine IsHomogeneous.prod _ _ _ (fun τ _ => ?_)
    have := (BlockVandermondeForms.vdm_homog τ (Formalism.ShimuraLimitIdentity.top N j)).mul (BlockVandermondeForms.vdm_homog τ (smallBlock N j))
    rwa [BlockVandermondeForms.card_top N j hj, BlockVandermondeForms.card_smallBlock] at this
  have hf : fibreVandermondeProduct (Ψ := Ψ) (N := N) j 1 = ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j)) := by
    unfold fibreVandermondeProduct; rw [map_one, one_mul]
  have hk := (fib_homog (Ψ := Ψ) (N := N) j).inj_right (by rw [← fib_eq, hf]; exact h2) (fib_ne_zero j)
  rw [hk]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, a0n, Formalism.DegreeFormula.dimFl]
  have hN : N = j + (N - j) := by omega
  have e2 : N * (N - 1) / 2 = N.choose 2 := (Nat.choose_two_right N).symm
  rw [e2]
  conv_lhs => rw [hN]
  rw [BlockVandermondeForms.add_choose_two]
  ring

end WeylPolynomialAlgebra

open WeylPolynomialAlgebra

theorem mul_eq_sign_rearrange (K e s f : ℝ) (hf : f ≠ 0) (hs : s * s = 1) : K * e = K * s / f * (f * s * e) := by
  rw [div_mul_eq_mul_div, eq_div_iff hf]
  linear_combination (-(K * e * f)) * hs


end Formalism.L2.Geo
end
end
