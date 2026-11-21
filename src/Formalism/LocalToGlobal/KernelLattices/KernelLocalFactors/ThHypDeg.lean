import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
import Formalism.LocalToGlobal.Columns.RecChainUnfOne

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Mu0

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (L : ChIdx X Pr R (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

end Mu0

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem anaStepD_of_thHypD (A : Amb X) (u : Pr.Word) (m2 : ℕ) (hm : R.m = m2 + 2) (hTh : ThHypD W Ch sel mu cst A u m2) (i : ℕ) (hi : i < R.m) :
    A.AnaStepD (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i) := by
  rcases Nat.lt_or_ge m2 i with h | h
  · have e : i = m2 + 1 := by omega
    subst e
    have h2 := hTh.2.1
    rw [hm] at h2
    exact h2
  · exact hTh.1 i h

end Top

end Formalism.L2.Ker

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker MvPolynomial Matrix Module

section Ev

variable {X : Fields} {a b : ℕ}

end Ev

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Wt

end Formalism.L2.Col
