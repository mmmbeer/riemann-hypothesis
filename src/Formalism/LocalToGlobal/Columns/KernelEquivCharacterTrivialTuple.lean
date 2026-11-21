import Formalism.LocalToGlobal.Columns.KernelEquivTrivialTuple
import Formalism.LocalToGlobal.Columns.FixEColLevSym
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThHypDeg
import Formalism.LocalToGlobal.Columns.ChainLawPhiTop
import Formalism.LocalToGlobal.Columns.ChainTwKer
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkEqcar
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Hyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}

theorem xiHyp_of_thHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hm : R.m = m2 + 2) (hσ : Am.σ₀ = σ₀) (hPr : Pr.Ok)
    (hTh : ThHyp W Ch sel mu cst Am u m2)
    (hχ : ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
      Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') ≠ 0)
    (hρ : RhoScal W Λ Ch sel mu cst G Am u) :
    XiHyp W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u) G := by
  have hA : ∀ i, i < R.m → Am.AnaStep (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) := by
    intro i hi
    rcases Nat.lt_or_ge m2 i with h | h
    · have e : i = m2 + 1 := by omega
      subst e
      have h2 := hTh.2.1
      rw [hm] at h2
      exact h2
    · exact hTh.1 i h
  exact
    { sig := hσ
      T_pos := (hPr.T_prime u).pos
      smooth := fun i hi => (hA i hi).2.1
      rat := fun i hi => (hA i hi).2.2
      chi_ne := hχ
      rho := hρ
      above := fun i hi p p' x => refXi1_above Ch sel mu cst L hQ m2 al u hm i hi p p' x }

end Hyp

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Am : Amb X) (u : Pr.Word) (m2 : ℕ)

abbrev symIdxD : ChIdx X Pr R (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) :=
  oneIdx (colLevSym Ch) (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2

abbrev symXi : XiFam Pr R u :=
  refXi1 Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) (exceptional_primes_trivial_tuple sel S) m2 (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2) u

structure KerRefHyp {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Gc : ChGlob X R.m) : Prop where
  hX : X.Ok
  hPr : Pr.Ok
  hm : R.m = m2 + 2
  sig : Am.σ₀ = σ₀
  thHyp : ThHyp W Ch sel (mu0 X.F X.E X.K S) cst Am u m2
  stepTop : Am.StepHyp (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel (mu0 X.F X.E X.K S) u)
    (cAof sel (mu0 X.F X.E X.K S) cst * cBof sel (mu0 X.F X.E X.K S) cst u)
  lawTop : ThEquivP (stepT W Ch sel (mu0 X.F X.E X.K S) cst Am u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel (mu0 X.F X.E X.K S) u)
    (cAof sel (mu0 X.F X.E X.K S) cst * cBof sel (mu0 X.F X.E X.K S) cst u)
    (colValF W sel (mu0 X.F X.E X.K S) u (m2 + 1)).rho (colValF W sel (mu0 X.F X.E X.K S) u (m2 + 1 + 1)).rho
  idx : (symIdxD Ch sel S m2).Ok Ch sel (mu0 X.F X.E X.K S) cst Gc m2
  xiLaw : ∀ i, i < m2 → ∀ (al : (symIdxD Ch sel S m2).β i) (be : (symIdxD Ch sel S m2).β (i + 1)),
    XiLaw Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) i al be
  psiLaw : ∀ al, PsiLaw Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) m2 al (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl)
  topLaw : TopLawG Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) m2 (colLevSym Ch (m2 + 1 + 1))
    (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl)
  chi_ne : ∀ i, i < R.m → ∀ (c : StCl W (colLevSym Ch) u i) (c' : StCl W (colLevSym Ch) u (i + 1)),
    Am.chiF (R.N i) (R.N (i + 1)) (repN W (colLevSym Ch) u i c) (repN W (colLevSym Ch) u (i + 1) c') ≠ 0
  rho : RhoScal W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst G Am u

variable {W Ch sel S cst Am u m2}

theorem KerRefHyp.xiHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHyp W Ch sel S cst Am u m2 G Gc) :
    XiHyp W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst Am u (symXi Ch sel S cst u m2) G :=
  xiHyp_of_thHyp H.hm H.sig H.hPr H.thHyp H.chi_ne H.rho

end Fin

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section XiD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word) (Ξ : XiFam Pr R u)

structure XiHypD {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) : Prop where
  sig : Am.σ₀ = σ₀
  T_pos : 0 < Pr.T u
  smooth : ∀ i, i < R.m → Am.ESmooth (R.N i) (R.N (i + 1))
  rat : ∀ i, i < R.m → Am.JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)
  chi_ne : ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') ≠ 0
  rho : RhoScal W Λ Ch sel mu cst G Am u
  above : ∀ i, R.m ≤ i → ∀ p p' x, Ξ i p p' x = 0

variable {W Λ Ch sel mu cst Am u Ξ}

end XiD

section FinD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Am : Amb X) (u : Pr.Word) (m2 : ℕ)

structure KerRefHypD {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Gc : ChGlob X R.m) : Prop where
  hX : X.Ok
  hPr : Pr.Ok
  hm : R.m = m2 + 2
  sig : Am.σ₀ = σ₀
  thHyp : ThHypD W Ch sel (mu0 X.F X.E X.K S) cst Am u m2
  lawTop : ThEquivP (stepT W Ch sel (mu0 X.F X.E X.K S) cst Am u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel (mu0 X.F X.E X.K S) u)
    (cAof sel (mu0 X.F X.E X.K S) cst * cBof sel (mu0 X.F X.E X.K S) cst u)
    (colValF W sel (mu0 X.F X.E X.K S) u (m2 + 1)).rho (colValF W sel (mu0 X.F X.E X.K S) u (m2 + 1 + 1)).rho
  idx : (symIdxD Ch sel S m2).Ok Ch sel (mu0 X.F X.E X.K S) cst Gc m2
  xiLaw : ∀ i, i < m2 → ∀ (al : (symIdxD Ch sel S m2).β i) (be : (symIdxD Ch sel S m2).β (i + 1)),
    XiLaw Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) i al be
  psiLaw : ∀ al, PsiLaw Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) m2 al (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl)
  topLaw : TopLawG Ch sel (mu0 X.F X.E X.K S) cst (symIdxD Ch sel S m2) m2 (colLevSym Ch (m2 + 1 + 1))
    (oneAl (colLevSym Ch) sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl)
  chi_ne : ∀ i, i < R.m → ∀ (c : StCl W (colLevSym Ch) u i) (c' : StCl W (colLevSym Ch) u (i + 1)),
    Am.chiF (R.N i) (R.N (i + 1)) (repN W (colLevSym Ch) u i c) (repN W (colLevSym Ch) u (i + 1) c') ≠ 0
  rho : RhoScal W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst G Am u

variable {W Ch sel S cst Am u m2}

theorem KerRefHypD.xiHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} {Gc : ChGlob X R.m} (H : KerRefHypD W Ch sel S cst Am u m2 G Gc) :
    XiHypD W (colLevSym Ch) Ch sel (mu0 X.F X.E X.K S) cst Am u (symXi Ch sel S cst u m2) G where
  sig := H.sig
  T_pos := (H.hPr.T_prime u).pos
  smooth := fun i hi => (anaStepD_of_thHypD W Ch sel _ cst Am u m2 H.hm H.thHyp i hi).2.1
  rat := fun i hi => (anaStepD_of_thHypD W Ch sel _ cst Am u m2 H.hm H.thHyp i hi).2.2
  chi_ne := H.chi_ne
  rho := H.rho
  above := fun i hi p p' x => refXi1_above Ch sel _ cst _ (exceptional_primes_trivial_tuple sel S) m2 _ u H.hm i hi p p' x

end FinD

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Car

variable {D : Formalism.L2.Ker.Car} {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) {m2 : ℕ}

structure CarNum : Prop where
  hS : (∀ l ∈ D.host.small, l ∈ S) ∧ D.host.q ∈ S ∧ D.host.d ∈ S ∧ Pr.T u ∈ S ∧ (∀ i, Pr.g i ∈ S)
  hSc : ∀ p : ℕ, p.Prime → p ∣ Ideal.absNorm cc → p ∈ S
  hT : Pr.T u ∉ D.host.small ∧ Pr.T u ≠ D.host.q ∧ Pr.T u ≠ D.host.d ∧ (Pr.T u).Coprime (Ideal.absNorm cc)
  hg : ∀ i, Pr.g i ∉ D.host.small ∧ Pr.g i ≠ D.host.q ∧ Pr.g i ≠ D.host.d ∧ (Pr.g i).Coprime (Ideal.absNorm cc)

variable {W Ch sel mu}

end Car

end Formalism.L2.Col
end
end
