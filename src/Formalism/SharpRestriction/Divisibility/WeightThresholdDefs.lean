import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.PrinLevClass

section
noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

def evV {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) :
    MvPolynomial (Vm D.what₂.Tau N) ℚ →ₐ[ℚ] MvPolynomial M.Z.LB ℚ :=
  aeval (fun v => match v with
    | Sum.inl r => X (rt r)
    | Sum.inr (false, k) => C ((Nat.factorial k : ℚ)⁻¹) *
        ((∑ l, X (M.lieW.x l) ^ k) + ∑ l, X (M.omW.x l) ^ k)
    | Sum.inr (true, k) => C ((Nat.factorial k : ℚ)⁻¹) *
        ((∑ l, X (M.lieW.x' l) ^ k) + ∑ l, X (M.omW.x' l) ^ k))

def evC {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) : M.Z.Ch :=
  evQ M.Z (evV M rt G)

def toR {σ : Type} (G : MvPolynomial σ ℚ) : MvPolynomial σ ℝ := map (algebraMap ℚ ℝ) G

def dRt (Tau : Type) [Fintype Tau] (N : ℕ) (r : Rt Tau N) : MvPolynomial (Vm Tau N) ℝ :=
  X (Sum.inl (false, r)) - X (Sum.inl (true, r))

def dCh (Tau : Type) [Fintype Tau] (N : ℕ) (k : ℕ) : MvPolynomial (Vm Tau N) ℝ :=
  X (Sum.inr (false, k)) - X (Sum.inr (true, k))

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

def adm2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p), ∃ n0 : ℕ, (p ∉ (XD.shv S κ).lev → n0 = 0) ∧
    ∀ n : ℕ, n0 ≤ n → (1 + 1 / ((p : ℝ) - 1)) < n → ∃ z : XD.Mp S κ p la, (XD.md S κ p la z).lvl = n

def adm3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (E E' : (XD.md S κ p la z).Z.VDiv)
    (a : (XD.md S κ p la z).Z.Ch),
    (XD.md S κ p la z).Z.capDeg E ((XD.md S κ p la z).Z.cD E' * a) =
      (XD.md S κ p la z).Z.capDeg E' ((XD.md S κ p la z).Z.cD E * a)

def ArchimedeanSignatureMatching : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la),
  (∀ (r : ℕ) (P P' P'' : FPair (XD.md S κ p la z).Z r), P'.x = P.x' → P''.x = P.x → P''.x' = P'.x' →
      (∀ i, P''.Dv i = P.Dv i + P'.Dv i) →
      ∀ (k : ℕ) (Q : (XD.md S κ p la z).Z.Ch), ck P'' k Q = ck P k Q + ck P' k Q) ∧
  (∀ (r : ℕ) (P : FPair (XD.md S κ p la z).Z r) (v : ℚ),
      (∀ i, P.Dv i = v • (XD.md S κ p la z).Z.divP) →
      ∀ (k : ℕ) (Q : (XD.md S κ p la z).Z.Ch), 1 ≤ k →
      ck P k Q = (k : ℚ) * v * (XD.md S κ p la z).Z.capDeg (XD.md S κ p la z).Z.divP
        ((∑ i, (XD.md S κ p la z).Z.c1 (P.x i) ^ (k - 1)) * Q)) ∧
  (∀ (r : ℕ) (P P' : FPair (XD.md S κ p la z).Z r),
      (∀ i, (XD.md S κ p la z).Z.c1 (P'.x i) = (p : ℚ) • (XD.md S κ p la z).Z.c1 (P.x i)) →
      (∀ i, (XD.md S κ p la z).Z.c1 (P'.x' i) = (p : ℚ) • (XD.md S κ p la z).Z.c1 (P.x' i)) →
      (∀ i, P'.Dv i = (p : ℚ) • P.Dv i) →
      ∀ (k : ℕ) (Q : (XD.md S κ p la z).Z.Ch), ck P' k Q = (p : ℚ) ^ k * ck P k Q)

def adm5 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la)
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ),
    G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
    (((XD.md S κ p la z).Z.capDeg (XD.md S κ p la z).Z.divP
        (evC (XD.md S κ p la z) (T.rt S κ p la z) G) : ℚ) : ℝ) / ((XD.md S κ p la z).cov : ℝ) =
      (XD.shv S κ).chern (collapse D _ (toR G))

def adm6 : Prop :=
  (∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ) [Fact p.Prime] (z : ∀ la : XD.PlP p, XD.Mp S κ p la)
    (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la *
          ((((XD.md S κ p la (z la)).Z.capDeg (((XD.md S κ p la (z la)).lie (τ' la)).Dv (i la))
            (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G) : ℚ) : ℝ) /
              ((XD.md S κ p la (z la)).cov : ℝ))) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ) [Fact p.Prime] (z : ∀ la : XD.PlP p, XD.Mp S κ p la)
    (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin ((XD.shv S κ).N -
        rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = (XD.shv S κ).j + i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la *
          ((((XD.md S κ p la (z la)).Z.capDeg (((XD.md S κ p la (z la)).om (τ' la)).Dv (i la))
            (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G) : ℚ) : ℝ) /
              ((XD.md S κ p la (z la)).cov : ℝ))) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ) [Fact p.Prime] (z : ∀ la : XD.PlP p, XD.Mp S κ p la)
    (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
    ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
      (XD.shv S κ).arMix Sx R p (dCh D.what₂.Tau (XD.shv S κ).N k * toR G) =
        Real.log p * ∑ la, XD.wtP p la *
          ((chk (XD.md S κ p la (z la)).lieW k
              (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G) +
            chk (XD.md S κ p la (z la)).omW k
              (evC (XD.md S κ p la (z la)) (T.rt S κ p la (z la)) G)) /
            ((XD.md S κ p la (z la)).cov : ℝ)))

def admitted : Prop :=
  adm1 D XD S κ ∧ adm2 D XD S κ ∧ adm3 D XD S κ ∧ ArchimedeanSignatureMatching D XD S κ ∧ adm5 D XD T S κ ∧
    adm6 D XD T S κ

def Conclusion1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev →
  ∀ (la : XD.PlP p) (z : XD.Mp S κ p la) (τ : Emb D p) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (XD.md S κ p la z).Z.LB ℚ, Q.IsHomogeneous m →
    (chk ((XD.md S κ p la z).lie τ) k (evQ _ Q) + chk ((XD.md S κ p la z).om τ) k (evQ _ Q)) /
        ((XD.md S κ p la z).cov : ℝ) =
      ((∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            chDiv ((XD.md S κ p la z).lie (phiPow D (n + 1) τ)).x (k - 1) (evQ _ Q)) -
          chDiv ((XD.md S κ p la z).lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)) /
        ((XD.md S κ p la z).cov : ℝ)

def Conclusion2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (XD.md S κ p la z).Z.LB ℚ, Q.IsHomogeneous m →
    (chk (XD.md S κ p la z).lieW k (evQ _ Q) + chk (XD.md S κ p la z).omW k (evQ _ Q)) /
        ((XD.md S κ p la z).cov : ℝ) =
      ((∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            chDiv (XD.md S κ p la z).lieW.x (k - 1) (evQ _ Q)) -
          chDiv (XD.md S κ p la z).lieW.x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)) /
        ((XD.md S κ p la z).cov : ℝ)

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

def Conclusion4 (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → ∀ (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p ((X (Sum.inr (false, k)) - X (Sum.inr (true, k))) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLieA D _ (XD.shv S κ).j (k - 1) * collapse D _ Q)) -
        (XD.shv S κ).chern (chLieA D _ (XD.shv S κ).j (k - 1) * collapse D _ Q) / ((p : ℝ) - 1))

def AdmX (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → admitted D XD T S κ

def ConclusionL (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → Conclusion1 D XD S κ ∧ Conclusion2 D XD S κ

def Stmt (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) (T : Loc D XD) : Prop :=
  AdmX D XD P T → ConclusionL D XD P ∧ PointsLemma D XD P ∧ Conclusion4 D XD P

abbrev LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AdmX (Fm.D x i) (Fm.X x i) (PL x hx i) (TF x hx i)

def LocalPropertiesFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConclusionL (Fm.D x i) (Fm.X x i) (PL x hx i)

def Conclusion3Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (Fm.D x i) (Fm.X x i) (PL x hx i)

def SlopeLemmaFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4 (Fm.D x i) (Fm.X x i) (PL x hx i)

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  AdmF Fm PL TF → LocalPropertiesFamily Fm PL ∧ Conclusion3Family Fm PL ∧ SlopeLemmaFamily Fm PL

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def vLie (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ : Emb D p)
    (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ) : ℝ :=
  (((XD.md S κ p la z).Z.capDeg (((XD.md S κ p la z).lie τ).Dv i)
      (evC (XD.md S κ p la z) (T.rt S κ p la z) G) : ℚ) : ℝ) / ((XD.md S κ p la z).cov : ℝ)

def vOm (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ : Emb D p)
    (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ) : ℝ :=
  (((XD.md S κ p la z).Z.capDeg (((XD.md S κ p la z).om τ).Dv i)
      (evC (XD.md S κ p la z) (T.rt S κ p la z) G) : ℚ) : ℝ) / ((XD.md S κ p la z).cov : ℝ)

def vCh (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (k : ℕ)
    (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ) : ℝ :=
  (chk (XD.md S κ p la z).lieW k (evC (XD.md S κ p la z) (T.rt S κ p la z) G) +
      chk (XD.md S κ p la z).omW k (evC (XD.md S κ p la z) (T.rt S κ p la z) G)) /
    ((XD.md S κ p la z).cov : ℝ)

def ModInd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z z' : XD.Mp S κ p la),
    (∀ (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
        ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
        (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ),
        G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
        vLie D XD T S κ p la z τ i G = vLie D XD T S κ p la z' τ i G) ∧
    (∀ (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
        ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
        (G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ),
        G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
        vOm D XD T S κ p la z τ i G = vOm D XD T S κ p la z' τ i G) ∧
    (∀ (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
        ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
        G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
        vCh D XD T S κ p la z k G = vCh D XD T S κ p la z' k G)

def ThreeIdentitiesOnModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ z : ∀ la : XD.PlP p, XD.Mp S κ p la,
  (∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la * vLie D XD T S κ p la (z la) (τ' la) (i la) G) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : XD.PlP p → Emb D p),
    (∀ la, (XD.jC p la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin ((XD.shv S κ).N -
        rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j (τ' la)))
      (i' : Fin (XD.shv S κ).N), (∀ la, (i' : ℕ) = (XD.shv S κ).j + i la) →
      ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) (dimFl D.what₂.Tau (XD.shv S κ).N) →
      (XD.shv S κ).arMix Sx R p (dRt D.what₂.Tau (XD.shv S κ).N (τ0, i') * toR G) =
        Real.log p * ∑ la, XD.wtP p la * vOm D XD T S κ p la (z la) (τ' la) (i la) G) ∧
  (∀ (Sx : Finset ℕ) (R : ℝ) (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
    ∀ G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ,
      G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
      (XD.shv S κ).arMix Sx R p (dCh D.what₂.Tau (XD.shv S κ).N k * toR G) =
        Real.log p * ∑ la, XD.wtP p la * vCh D XD T S κ p la (z la) k G)



end One1

def ThreeIdentitiesOnModelFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
    ThreeIdentitiesOnModel (Fm.D x i) (Fm.X x i) (TF x hx i) S κ

def ModIndF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (TF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) S κ, HidaSetting (Fm.D x i) (Fm.X x i) S κ → DIV.Align.LevB (PL x hx i) κ →
    ModInd (Fm.D x i) (Fm.X x i) (TF x hx i) S κ



end Formalism.MainNotions.LatticeTransfer

end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

abbrev HS (D : D7) : Type 1 := letI := D.host.cmStar; Formalism.BasicNotions.HSpace D.host.E

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev dimY : ℕ := dimFl D.what₂.Tau Y.N

def jS : ℕ := min Y.j (Y.N - Y.j)

def inSmall (i : Fin Y.N) : Prop := if Y.j ≤ Y.N - Y.j then (i : ℕ) < Y.j else Y.j ≤ (i : ℕ)

def Dominant (lam : D.what₂.Tau → Fin Y.N → ℝ) : Prop :=
  ∀ τ (a b : Fin Y.N), a ≤ b → lam τ b ≤ lam τ a

def gap (lam : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) : ℝ :=
  lam τ ⟨Y.j - 1, by have := Y.j_lt; omega⟩ - lam τ ⟨Y.j, Y.j_lt⟩

def supAbs (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := ⨆ x : Rt D.what₂.Tau Y.N, |lam x.1 x.2|

def WeightHyp (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ (a b : Fin Y.N), a < b → u τ b < u τ a) ∧ (∀ τ, g ≤ gap Y u τ) ∧
  (∀ τ (a b : Fin Y.N), inSmall Y a → a ≠ b → g ≤ |u τ a - u τ b|)

def bigB0 (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g)

def geoDeg (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := Y.chern (linRoot lam ^ dimY Y)

def NefHT (p : ℕ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : Prop :=
  ∀ c : Y.CurveHT p, 0 ≤ -∑ x : Rt D.what₂.Tau Y.N, lam x.1 x.2 * Y.degHT p c x

def NefDR (p : ℕ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : Prop :=
  ∀ c : Y.CurveDR p, 0 ≤ -∑ x : Rt D.what₂.Tau Y.N, lam x.1 x.2 * Y.degDR p c x

end Derived

def cP (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

def NefM {S : HS D} {κ : V.Lev} {p : ℕ} [Fact p.Prime] {la : V.PlP p} (z : V.Mp S κ p la)
    (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ) : Prop :=
  ∀ c : V.CurveM S κ p la z, 0 ≤ -∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * V.degM S κ p la z c x

def FlagTriv {S : HS D} {κ : V.Lev} {p : ℕ} [Fact p.Prime] {la : V.PlP p} (z : V.Mp S κ p la) : Prop :=
  (∀ (τ : Emb D p) (k : ℕ), 1 ≤ k → ∀ (E : (V.md S κ p la z).Z.VDiv) (a : (V.md S κ p la z).Z.Ch),
    (V.md S κ p la z).Z.capDeg E
      (((∑ i, (V.md S κ p la z).Z.c1 (((V.md S κ p la z).lie τ).x' i) ^ k) +
        ∑ i, (V.md S κ p la z).Z.c1 (((V.md S κ p la z).om τ).x' i) ^ k) * a) = 0) ∧
  ∀ k : ℕ, 1 ≤ k → ∀ (E : (V.md S κ p la z).Z.VDiv) (a : (V.md S κ p la z).Z.Ch),
    (V.md S κ p la z).Z.capDeg E
      (((∑ i, (V.md S κ p la z).Z.c1 ((V.md S κ p la z).lieW.x' i) ^ k) +
        ∑ i, (V.md S κ p la z).Z.c1 ((V.md S κ p la z).omW.x' i) ^ k) * a) = 0

def r0 : ℝ := -((deriv riemannZeta (-1) / riemannZeta (-1)).re + 1 / 2)

def adm7 : Prop := ∀ t : V.Surf,
  (∃ q : ℚ, 2 * V.surfCh2 t - r0 * V.surfDegOm t = q * Real.log 2) ∧
  (∃ q : ℚ, 2 * V.surfCh2 t - r0 * V.surfDegOm t = q * Real.log 3)

def adm9 : Prop := LatticeTransfer.PointsLemma D V P

def adm10 : Prop := ∀ S κ, HidaSetting D V S κ →
  ∀ Q, (V.shv S κ).chern Q = (V.shv S κ).vol * degFl D.what₂.Tau (V.shv S κ).N Q

def admitted : Prop := adm7 V ∧ adm9 V P ∧ adm10 V

def Conclusion0 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ c : (V.shv S κ).FibComp p, ¬ (V.shv S κ).fibInBd p c

def Conclusion1 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ →
  (∀ (p : ℕ) [Fact p.Prime] (la : V.PlP p), ∃ n0 : ℕ, (p ∉ (V.shv S κ).lev → n0 = 0) ∧
    ∀ n : ℕ, n0 ≤ n → 1 + cP p < (n : ℝ) → ∃ z : V.Mp S κ p la, (V.md S κ p la z).lvl = n) ∧
  ∀ (p : ℕ) [Fact p.Prime] (la : V.PlP p) (z : V.Mp S κ p la),
    FlagTriv V z ∧ ∀ lam, Dominant (V.shv S κ) lam → NefM V z lam

def NefHodgeTateLattices : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ lam, Dominant (V.shv S κ) lam → NefHT (V.shv S κ) p lam

def TrivialFlagIntersectionCond : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (V.shv S κ).arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) *
      (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

def LogarithmicExponentBound (C1 : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime → UnramE D p →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiDR p y x| ≤
      C1 * D.R.f * (V.shv S κ).N * supAbs (V.shv S κ) lam * Real.log p / ((p : ℝ) - 1)

def ExponentBlockSplitting : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ∣ dE D →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiMod p y x| ≤
      C * supAbs (V.shv S κ) lam

def proposition_eleven_one_at_scale : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiFr p y x| ≤
      Real.log p * ∑ τ, (cP p * ∑ i, |lam τ i| +
        V.vdd p τ * |∑ i ∈ univ.filter (fun i : Fin (V.shv S κ).N => (i : ℕ) < (V.shv S κ).j),
          lam τ i|)

def Conclusion2 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * dE D →
  p ∉ (V.shv S κ).lev → ∀ mu, Dominant (V.shv S κ) mu →
    4 * (D.R.f : ℝ) * supAbs (V.shv S κ) mu ≤ ((p : ℝ) - 2) * (⨅ τ, gap (V.shv S κ) mu τ) →
    NefDR (V.shv S κ) p mu

def Conclusion4a (r : ℝ) : Prop := ∀ S : V.Surf, V.surfCh2 S = r / 2 * V.surfDegOm S

def Conclusion4b : Prop := ∀ S : V.SurfFp, V.surfFpCh2 S = 0

def Conclusion4 (r : ℝ) : Prop := Conclusion4a V r ∧ Conclusion4b V

def Conclusion5 (C5 : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ u g, WeightHyp (V.shv S κ) u g →
  ∀ Qs : D.what₂.Tau → ℕ → MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (∀ τ k, 1 ≤ k → k ≤ (V.shv S κ).N → (Qs τ k).IsHomogeneous (dimY (V.shv S κ) + 1 - k)) →
    linRoot u ^ (dimY (V.shv S κ) + 1) =
      ∑ τ, ∑ k ∈ Finset.Icc 1 (V.shv S κ).N, pk D _ τ k * Qs τ k →
    ∀ B : ℕ, (∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧
        bigB0 (V.shv S κ) u g < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ (V.shv S κ).lev),
      Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 (V.shv S κ).N, ∑' n : ℕ,
        |(Nat.factorial k : ℝ) * ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (V.shv S κ).chern (chLie (V.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            Qs τ k) / (((dimY (V.shv S κ) : ℝ) + 1) * geoDeg (V.shv S κ) u)|) ≤
    C5 * jS (V.shv S κ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

structure Loc4 where

  dRho : V.Surf → ℕ
  dRho_pos : ∀ t, 0 < dRho t

  CHr : V.Surf → Type
  instCHr : ∀ t, AddCommGroup (CHr t)

  ch2 : ∀ t, CHr t

  ch2o : ∀ t, CHr t

  arithFirstChernHom : ∀ t, ℝ →+ CHr t

  degA : ∀ t, CHr t →+ ℝ

attribute [instance] Loc4.instCHr

def ThetaChernBoundOfLastLine : Prop := adm7 V → Conclusion4a V r0

def Stmt (C1 C5 : ℝ) : Prop :=
  admitted V P → Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧
    Conclusion4 V r0 ∧ Conclusion5 V P C5

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

def AdmF : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.X x i) (PL x hx i)

def familyAllButProportionality (C1 : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
  Conclusion0 (Fm.X x i) (PL x hx i) ∧ Conclusion1 (Fm.X x i) (PL x hx i) ∧ NefHodgeTateLattices (Fm.X x i) (PL x hx i) ∧ TrivialFlagIntersectionCond (Fm.X x i) (PL x hx i) ∧
    LogarithmicExponentBound (Fm.X x i) (PL x hx i) C1 ∧ ExponentBlockSplitting (Fm.X x i) (PL x hx i) ∧ proposition_eleven_one_at_scale (Fm.X x i) (PL x hx i) ∧
    Conclusion2 (Fm.X x i) (PL x hx i) ∧ Conclusion4 (Fm.X x i) r0

def SlopeLossFamily (C5 : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion5 (Fm.X x i) (PL x hx i) C5

def OrbitValuationBound (C1 C5 : ℝ) : Prop := familyAllButProportionality Fm PL C1 ∧ SlopeLossFamily Fm PL C5

def KudlaFamilyStatement (C1 C5 : ℝ) : Prop := AdmF Fm PL → OrbitValuationBound Fm PL C1 C5

end Fam

end Formalism.MainNotions.WeightThresholdDefs

end
end
