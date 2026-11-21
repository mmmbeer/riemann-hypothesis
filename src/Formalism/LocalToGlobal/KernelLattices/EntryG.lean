import Formalism.LocalToGlobal.ExponentGrids.EntryG
import Formalism.LocalToGlobal.KernelLattices.ColInst

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.DivisionValues (vw)

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

open Classical in

def oneAt (m : DVar ι a b →₀ ℕ) : (DVar ι a b →₀ ℕ) → K := fun m' => if m' = m then 1 else 0

def jetCf (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (ℓ : Module.Dual K (DIV.VV K lam')) (P : DIV.VV K lam)
    (m : DVar ι a b →₀ ℕ) : K :=
  ℓ (jetOp lam lam' (oneAt m) n P)

open Classical in

def jetSupp (b : ℕ) (n : ι → ℕ) (P : Pol K ι a) : Finset (DVar ι a b →₀ ℕ) :=
  (subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ)).support.image fun μ => μ.comapDomain Sum.inr Sum.inr_injective.injOn

end Cf

def LevAtG (p cA cB c₀ cA' : ℕ) : Prop :=
  0 < cA ∧ 0 < cB ∧ (∃ k, cB = p * c₀ * k) ∧ cA' ∣ cA ∧ ¬ p ∣ c₀ ∧ ¬ p ∣ cA'

section AtG

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

def XiAtG (ι : ℂ ≃+* ℂ_[p]) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (c₀ cA' : ℕ) (e : ℝ) (Ξ : HomE X.E a b → X.K) : Prop :=
  (∀ x y, y ∈ mulLat (p * c₀) (homAt S N N') → Ξ (x + y) = Ξ x) ∧
  (∀ x, x ∉ divLat cA' (homAt S N N') → Ξ x = 0) ∧
  ∀ x, ‖ι (A.σ₀ (Ξ x))‖ ≤ ‖(p : ℂ_[p])‖ ^ e

def JetCfInt (ι : ℂ ≃+* ℂ_[p]) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (ℓ : Module.Dual X.K (DIV.VV X.K lam')) (P : DIV.VV X.K lam) : Prop :=
  ∀ m, ‖ι (A.σ₀ (jetCf lam lam' n ℓ P m))‖ ≤ 1

def StepAtG (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ) (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (S : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  IsSdLat N ∧ IsSdLat N' ∧ KerStd A N N' a₀ b₀ c₀' ha hd lam₀ hlam p ι ∧ A.LaHyp a b S ∧ SplitS A S p ϖ pE ∧ A.JetAdd a b S D

end AtG

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

def LatIntAt (w : HeightOneSpectrum (𝓞 K)) (Λ : Submodule (𝓞 K) V) (v : V) : Prop := ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ (s : K) • v ∈ Λ

end Lat

section AtRec

open Formalism.DivisionValues (PlOver)

def StdOver {E : Type} [Field E] [NumberField E] {n : ℕ} (g : ℕ) (Lat : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal Lat = stdAt E n P

end AtRec

section Hyp

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

def KerEntryHyp (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ) (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (D : ℕ) (e : ℝ) (S SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (Ξ : HomE X.E a b → X.K) (ℓ : Module.Dual X.K (DIV.VV X.K lam')) (P : DIV.VV X.K lam) : Prop :=
  ∃ c₀ cA' : ℕ, LevAtG p cA cB c₀ cA' ∧ StepAtG A a₀ b₀ c₀' ha hd lam₀ hlam ι ϖ pE S (cA * cB) N N' ∧ XiAtG A ι S N N' c₀ cA' e Ξ ∧
    ‖ι (A.σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹))‖ ≤ 1 ∧ JetCfInt A ι lam lam' n ℓ P ∧
    ∀ m ∈ jetSupp b n (P : Pol X.K X.Tau a), m.degree = D

end Hyp

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime]

def StepEntryHyp (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ) (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E)
    (D : ℕ) (e : ℝ) (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b)
    (N : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K) (ℓ : Module.Dual X.K (DIV.VV X.K lam'))
    (P : DIV.VV X.K (W.lamTrue u i)) : Prop :=
  KerEntryHyp A a₀ b₀ c₀' ha hd lam₀ hlam ι ϖ pE D e (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) sel (mUof Ch mu i)
    (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i) N fr N' fr' Ξ ℓ P

end Rec

section Paths

open Module NumberField IsDedekindDomain

open Formalism.L2.Col Formalism.L2.DIV

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (Q : KerChain K)

def Nd (j : ℕ) : Type := (Q.F j).Cl × (Q.F j).ιV

instance (j : ℕ) : Fintype (Nd Q j) :=
  letI := (Q.hF j).fintypeCl
  inferInstanceAs (Fintype ((Q.F j).Cl × (Q.F j).ιV))

def famRep (j : ℕ) (c : (Q.F j).Cl) : (Q.F j).D c.1 := ((Q.F j).mem c.1).outSec.rep c.2

def famWt (j : ℕ) (c : (Q.F j).Cl) : ℕ := (((Q.F j).mem c.1).toCSDOf (Q.hF j c.1) ((Q.F j).mem c.1).outSec).wt c.2

structure ChBas where

  B : ∀ j (c : (Q.F j).Cl), Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q} (Bb : ChBas Q)

def crd (j : ℕ) (ν : Nd Q j) : (Q.F j).Forms →ₗ[K] K :=
  (Bb.B j ν.1).coord ν.2 ∘ₗ (LinearMap.proj (famRep Q j ν.1)) ∘ₗ ((Q.F j).mem ν.1.1).EqFun.subtype ∘ₗ LinearMap.proj ν.1.1

def entM (j : ℕ) (ν : Nd Q j) (ν' : Nd Q (j + 1)) : K :=
  (Bb.B (j + 1) ν'.1).coord ν'.2 ((Q.kk j ν.1.1 ν'.1.1).k (famRep Q j ν.1) (famRep Q (j + 1) ν'.1) (Bb.B j ν.1 ν.2))

variable (Q) in

def PthTo : ∀ j : ℕ, Nd Q j → Type
  | 0, _ => Unit
  | j + 1, _ => Σ ν : Nd Q j, PthTo j ν

instance PthTo.fintype : ∀ (j : ℕ) (ν : Nd Q j), Fintype (PthTo Q j ν)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | j + 1, _ =>
    letI := fun ν => PthTo.fintype j ν
    inferInstanceAs (Fintype (Σ ν : Nd Q j, PthTo Q j ν))

def PthTo.first : ∀ (j : ℕ) (ν : Nd Q j), PthTo Q j ν → Nd Q 0
  | 0, ν, _ => ν
  | j + 1, _, ⟨ν, p⟩ => PthTo.first j ν p

def PthTo.gam : ∀ (j : ℕ) (ν : Nd Q j), PthTo Q j ν → ℕ → ℕ
  | 0, _, _ => fun _ => 1
  | j + 1, _, ⟨ν, p⟩ => Function.update (PthTo.gam j ν p) j (famWt Q j ν.1)

def PthTo.ent : ∀ (j : ℕ) (ν : Nd Q j), PthTo Q j ν → ℕ → K
  | 0, _, _ => fun _ => 1
  | j + 1, ν', ⟨ν, p⟩ => Function.update (PthTo.ent j ν p) j (entM Bb j ν ν')

variable (Q) in

def MidNd : Type := Σ c : Q.S.Cl, {y // y ∈ (Q.Y.fin (Q.S.outSec.rep c)).toFinset} × Q.S.ιV

instance : Fintype (MidNd Q) :=
  letI := Q.hS.fintypeCl
  inferInstanceAs (Fintype (Σ c : Q.S.Cl, {y // y ∈ (Q.Y.fin (Q.S.outSec.rep c)).toFinset} × Q.S.ιV))

def midWt (μ : MidNd Q) : ℕ := (Q.S.toCSDOf Q.hS Q.S.outSec).wt μ.1

def ent1 (ν : Nd Q Q.n) (μ : MidNd Q) : K :=
  (Bb.BS μ.1).coord μ.2.2 ((Q.cp ν.1.1).k1 (famRep Q Q.n ν.1) (Q.S.outSec.rep μ.1) μ.2.1.1 (Bb.B Q.n ν.1 ν.2))

def ent2 (b : (Q.F Q.n).β) (μ : MidNd Q) (d₁ : Q.S₁.D) (ℓ : Q.S₁.V →ₗ[K] K) : K :=
  ℓ ((Q.cp b).k2 (Q.S.outSec.rep μ.1) μ.2.1.1 d₁ (Bb.BS μ.1 μ.2.2))

structure LastDat (S₁ : GSD K) (Bsp : Type) [AddCommGroup Bsp] [Module K Bsp] where

  Cl : Type
  [finCl : Fintype Cl]

  pt : Cl → S₁.D

  wt : Cl → ℕ

  V₂ : Type
  [addV : AddCommGroup V₂]
  [modV : Module K V₂]

  ι₂ : Type
  [finι : Fintype ι₂]

  β : S₁.V →ₗ[K] V₂ →ₗ[K] K

  ev : Cl → Bsp →ₗ[K] V₂

  B1 : Cl → Basis S₁.ιV K S₁.V

  B2 : Cl → Basis ι₂ K V₂

attribute [instance] LastDat.finCl LastDat.addV LastDat.modV LastDat.finι

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp]

def LastDat.Is {S₁ : GSD K} (T : LastDat S₁ Bsp) (Λ : S₁.EqFun →ₗ[K] Module.Dual K Bsp) : Prop :=
  ∀ (ψ : S₁.EqFun) (F : Bsp), Λ ψ F = ∑ c : T.Cl, ((T.wt c : K))⁻¹ * T.β ((ψ : S₁.D → S₁.V) (T.pt c)) (T.ev c F)

variable (T : LastDat Q.S₁ Bsp)

variable (Q) in

abbrev ChPath (T : LastDat Q.S₁ Bsp) : Type := (T.Cl × Q.S₁.ιV × T.ι₂) × MidNd Q × (Σ ν : Nd Q Q.n, PthTo Q Q.n ν)

def ChPath.gamN (π : ChPath Q T) : ℕ → ℕ :=
  Function.update (Function.update (PthTo.gam Q.n π.2.2.1 π.2.2.2) Q.n (famWt Q Q.n π.2.2.1.1)) (Q.n + 1) (midWt π.2.1)

def ChPath.entN (π : ChPath Q T) : ℕ → K :=
  Function.update (Function.update (PthTo.ent Bb Q.n π.2.2.1 π.2.2.2) Q.n (ent1 Bb π.2.2.1 π.2.1)) (Q.n + 1)
    (ent2 Bb π.2.2.1.1.1 π.2.1 (T.pt π.1.1) ((T.B1 π.1.1).coord π.1.2.1))

variable {l : ℕ} [Fact l.Prime] {J : Type} [Fintype J] {Asp : Type} [AddCommGroup Asp] [Module K Asp]

def chainPaths (ι' : K →+* ℂ_[l]) (eJ : J ≃ Fin (Q.n + 2)) (f : Asp →ₗ[K] (Q.F 0).Forms) : PathData K l J Asp Bsp where
  Pi := ChPath Q T
  fPi := inferInstance
  x π := crd Bb 0 (PthTo.first Q.n π.2.2.1 π.2.2.2) ∘ₗ f
  y π := (T.B2 π.1.1).coord π.1.2.2 ∘ₗ T.ev π.1.1
  r π := ι' (T.β (T.B1 π.1.1 π.1.2.1) (T.B2 π.1.1 π.1.2.2))
  gam π j := if (eJ j : ℕ) = 0 then 1 else ChPath.gamN T π (eJ j)
  gamP π := T.wt π.1.1
  eps π j := if (eJ j : ℕ) = 0 then ((ChPath.gamN T π 0 : ℕ) : ℂ_[l])⁻¹ else 1
  e π j := ι' (ChPath.entN Bb T π (eJ j))

end Generic

section Transport

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def rhoEq (S : GSD K) (γ : S.G) : S.V ≃ₗ[K] S.V :=
  LinearEquiv.ofLinear (S.ρ γ) (S.ρ γ⁻¹)
    (by
      ext v
      have h := LinearMap.congr_fun (map_mul S.ρ γ γ⁻¹).symm v
      rw [mul_inv_cancel, map_one] at h
      exact h)
    (by
      ext v
      have h := LinearMap.congr_fun (map_mul S.ρ γ⁻¹ γ).symm v
      rw [inv_mul_cancel, map_one] at h
      exact h)

def mvTo (S : GSD K) (s : S.Sec) (c : S.Cl) : S.G :=
  Classical.choose ((S.cls_eq_iff (S.outSec.rep c) (s.rep c)).mp ((S.outSec.spec c).trans (s.spec c).symm))

structure ChGood (Q : KerChain K) where

  s : ∀ j b, ((Q.F j).mem b).Sec

  sS : Q.S.Sec

  B : ∀ j, (Q.F j).Cl → Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q : KerChain K} (G : ChGood Q)

def ChGood.bas : ChBas Q where
  B j c := (G.B j c).map (rhoEq ((Q.F j).mem c.1) (mvTo ((Q.F j).mem c.1) (G.s j c.1) c.2))
  BS c := (G.BS c).map (rhoEq Q.S (mvTo Q.S G.sS c))

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp] {J : Type}

end Transport

section Place

open Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

def lastRec {mu : Tup X.F X.E X.K Sg} {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    (u : Pr.Word) {n : ℕ} (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P)
    (B1 : (mtildeGSD W Ch sel mu P).Cl → Basis (evGSD W Ch sel mu P u).ιV X.K (evGSD W Ch sel mu P u).V)
    (B2 : (mtildeGSD W Ch sel mu P).Cl → Basis (VVIdx W.sgTrue) X.K (DIV.VV X.K W.sgTrue)) :
    LastDat (evGSD W Ch sel mu P u) (Fin n → X.K) where
  Cl := (mtildeGSD W Ch sel mu P).Cl
  finCl := hP.fintypeCl
  pt c := (mtildeGSD W Ch sel mu P).outSec.rep c
  wt c := ((mtildeGSD W Ch sel mu P).toCSDOf hP (mtildeGSD W Ch sel mu P).outSec).wt c
  V₂ := DIV.VV X.K W.sgTrue
  ι₂ := VVIdx W.sgTrue
  β := (pairBK (K := X.K) W.sgTrue) ∘ₗ brC W u
  ev c := LinearMap.proj ((mtildeGSD W Ch sel mu P).outSec.rep c) ∘ₗ (mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ
    (V0X W Ch sel mu Xg P).subtype ∘ₗ ev
  B1 := B1
  B2 := B2

abbrev recQ {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
    {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (Am : Amb X)
    (hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K :=
  KerChain.ofCol W Ch sel mu cst L (chKerC W Ch sel mu cst L Am u m2 b hY P hK) hF hE

section Entries

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  (Bb : ChBas (recQ Am hK hF hE))

end Entries

section Steps

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  {g : ℕ} [Fact g.Prime] {J : Type}

end Steps

end Record

end Paths

end Formalism.L2.Ker
