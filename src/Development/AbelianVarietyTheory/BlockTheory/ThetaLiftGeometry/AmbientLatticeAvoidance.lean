import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance

def reix (E : Type) [Field E] (n n' : ℕ) : Sp E n →ₗ[E] Sp E n' := LinearMap.pi fun l : Fin n' => atNL E n l.1

section Concrete

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev rkTop (R : Ranks) : ℕ := (R.N R.m - 1) + 0

open Classical in

def JTop (Pr : Primes X) (R : Ranks) (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) :
    Subgroup (Sp X.E (rkTop R) ≃ₗ[X.E] Sp X.E (rkTop R)) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.JGsym P (qOf P) R.k R.rS R.r R.t (R.N R.m - 1) 0 else LocE.JG P (qOf P) R.k R.r R.t (R.N R.m - 1) 0)
  else LocE.JQ P (qOf P) R.r (R.N R.m - 1) 0

open Classical in

def lamTop (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (rkTop R) (rkTop R)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (R.N R.m - 1) h

open Classical in

def latTop (Pr : Primes X) (R : Ranks) (n : ℕ) (π : X.E)
    (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (P : HeightOneSpectrum (𝓞 X.E)) :
    Set (Sp X.E n) :=
  if P ∈ Pr.vGs then (stdAt X.E n P : Set (Sp X.E n))
  else {x | reix X.E n (rkTop R) x ∈ abelian₂ P ∧ IntAt P (π⁻¹ * atNL X.E n (R.N R.m - 1) x)}

open Classical in

def TopLev (n : ℕ) (π : X.E) (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R)))
    (dep : HeightOneSpectrum (𝓞 X.E) → ℕ) (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (z : X.K) : Prop :=
  ∃ j ∈ JTop Pr R sharp P, ∃ jx k : Sp X.E n ≃ₗ[X.E] Sp X.E n,
    (∀ x, reix X.E n (rkTop R) (jx x) = j (reix X.E n (rkTop R) x)) ∧
    (∀ x, atNL X.E n (R.N R.m - 1) (jx x) = atNL X.E n (R.N R.m - 1) x) ∧
    (∀ x, k x ∈ latTop Pr R n π abelian₂ P ↔ x ∈ latTop Pr R n π abelian₂ P) ∧
    (∀ x ∈ latTop Pr R n π abelian₂ P,
      ((qOf P : X.E) ^ (if P ∈ Pr.vGs then 1 else dep P))⁻¹ • (k x - x) ∈ latTop Pr R n π abelian₂ P) ∧
    κ = jx * k ∧ z = lamTop Ch mu sharp P j.toLinearMap

abbrev Pt (u : Pr.Word) (i : ℕ) : Type := ChPt (R := R) sel mu u i × Option (L.β i) × Set (Sp X.E (R.N i))

def YbOk {u : Pr.Word} {i : ℕ} (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) : Prop :=
  Y ∈ ybSet sel mu cst p.deco.1.N ∧
  ∀ P : rowSG Pr sel mu, ∃ (al : L.β (R.m - 2)) (x₀ : HomE X.E (R.N (R.m - 2)) (R.N (R.m - 2 + 1))),
    PsiAt Ch sel mu cst (R.m - 2) P (L.h (R.m - 2) al P) x₀
      (reix X.E (R.N i) (R.N (R.m - 2 + 1)) ((frsF sel mu p P).symm (repY Y))) ≠ 0

def Pt.Valid {u : Pr.Word} {i : ℕ} (a : Pt sel mu L u i) : Prop :=
  (i < R.m → a.2.1 ≠ none) ∧ (R.m ≤ i → a.2.1 = none) ∧
  (i + 1 = R.m → YbOk Ch sel mu cst L a.1 a.2.2) ∧ (i + 1 ≠ R.m → a.2.2 = ∅)

variable (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)

def Mov {u : Pr.Word} {i : ℕ} (γ : UF X.E (R.N i)) (a a' : Pt sel mu L u i) (z : X.K) : Prop :=
  a'.2.1 = a.2.1 ∧ a'.2.2 = (fun v => γ.1 v) '' a.2.2 ∧
  ∃ (h : GLG X.E (R.N i) Pr.vGs) (c : GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))),
    a'.1 = ((γ, h, c) : UF X.E (R.N i) × GLG X.E (R.N i) Pr.vGs × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • a.1 ∧
    (∀ b : L.β i, a.2.1 = some b → ∃ (hh : h ∈ (L.levG i b).grp) (hc : c ∈ (L.levQ i b).grp),
      z = (((L.levG i b).chr ⟨h, hh⟩ * (L.levQ i b).chr ⟨c, hc⟩ : X.Kˣ) : X.K)) ∧
    (a.2.1 = none → ∃ (zG : Pr.vGs → X.K) (zQ : QE sel (mu : Chr X.F X.E X.K) → X.K),
      (∀ w : Pr.vGs, ∃ κ : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i),
        TopLev Ch mu (R.N i) ((Pr.piT u : 𝓞 X.E) : X.E) abelian₂ dep cst.sharp w.1 κ (zG w) ∧
        ∀ x ∈ stdAt X.E (R.N i) w.1, redV w.1 (κ x) = (h w).1.mulVec (redV w.1 x)) ∧
      (∀ P : QE sel (mu : Chr X.F X.E X.K),
        TopLev Ch mu (R.N i) ((Pr.piT u : 𝓞 X.E) : X.E) abelian₂ dep cst.sharp P.1 (c P).1 (zQ P)) ∧
      z = (∏ w, zG w) * ∏ P, zQ P)

def XiTop {u : Pr.Word} {i : ℕ} (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  phiT X.K p.deco.1 p'.deco.1 x *
    ∏ P : rowSG Pr sel mu,
      PhiTop Ch mu cst.sharp (R.m - 2) P.1
          (reix X.E (R.N (i + 1)) (rkTop R) ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ
            reix X.E (R.N (R.m - 2 + 1) + cOf R (R.m - 2 + 1)) (R.N i)) *
        ftY sel mu cst P
          ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N (i + 1)) (R.N R.m - 1)) ∘ₗ
            inFr (frsF sel mu p P) (frsF sel mu p' P) x)
          ((frsF sel mu p P).symm (repY Y))

def XiStep {u : Pr.Word} {i : ℕ} (a : Pt sel mu L u i) (a' : Pt sel mu L u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i + 2 < R.m then
    (match a.2.1, a'.2.1 with
      | some al, some be => XiEntry Ch sel mu cst L i al be a.1 a'.1 x
      | _, _ => 0)
  else if i + 2 = R.m then
    (match a.2.1 with
      | some al => XiCpl1 Ch sel mu cst L i al a.1 a'.1 a'.2.2 x
      | none => 0)
  else XiTop Ch sel mu cst a.1 a.2.2 a'.1 x

end Concrete

section Global

variable {D : D7} {X : Fields} (s : Seam D X)

def ambE (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D) (dgen : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := dgen (s.iT τ)
  e a b N N' z := e a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')

example {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (dgen : D.what₂.Tau → ℂ) :
    ambE s cc δ χ (B.eNat χ) dgen = ambOf s B χ dgen := rfl

open Classical in

def TupTie (Dx : DivX D) {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (tup : D.what₂.Tup → Tup X.F X.E X.K S) : Prop :=
  tup D.what₂.mu0 = 1 ∧ ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT D μ → Dx.Qp μ = (QE sel (tup μ : Chr X.F X.E X.K)).image qOf

end Global

section Chain

variable {D : D7} {X : Fields} (s : Seam D X) {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
  (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop D.R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)
  {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (v : Pr.Word)
  (rep : ∀ i, C.cls i → Pt sel mu L v i)
  (frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)

def ClsTie : Prop :=
  ∀ i ≤ D.R.m, (∀ c, Pt.Valid Ch sel mu cst L (rep i c)) ∧
    (∀ c c' γ z, Mov Ch sel mu cst L abelian₂ dep γ (rep i c) (rep i c') z → c = c') ∧
    ∀ a : Pt sel mu L v i, Pt.Valid Ch sel mu cst L a → ∃ c γ z, Mov Ch sel mu cst L abelian₂ dep γ (rep i c) a z

end Chain

example (E : Type) [Field E] (n : ℕ) (x : Sp E n) : reix E n n x = x := by
  funext l
  simp [reix, atNL]

end GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance
