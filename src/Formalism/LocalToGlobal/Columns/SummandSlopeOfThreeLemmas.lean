import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Defs

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def latK (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (Pi.basisFun K (Fin n)) M (formAt (Pi.basisFun K (Fin n)) (hStd K n))

@[reducible] def weylH (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (bVV K (oneW lam)) (delK (oneW lam) fun _ => M) (formAt (bVV K (oneW lam)) (stdPair K lam))

@[reducible] def tenH {ι : Type} [Fintype ι] (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (bVV K lam) (delK lam M) (formAt (bVV K lam) (pairK lam fun _ => 1))


def WeylFunct : Prop :=
  ∀ (n : ℕ) (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsLattice K M →
    (weylH K lam M).mu = ((∑ i, lam.w i : ℤ) : ℝ) * (latK K M).mu + (stdDelH K lam).mu

end Defs

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def EEC (u : Pr.Word) (d : (colGSD W Ch u 0).D) (τ : X.Tau) : Submodule (𝓞 X.K) (Fin (R.N 0) → X.K) :=
  dualFr (tauLat X.emb τ (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh)



def EESlope (u : Pr.Word) : Prop :=
  ∀ (d : (colGSD W Ch u 0).D) (τ : X.Tau), (latK X.K (EEC W Ch u d τ)).mu = -(logTC Pr u) / (R.k : ℝ)

end Cols

end Formalism.L2.Col
