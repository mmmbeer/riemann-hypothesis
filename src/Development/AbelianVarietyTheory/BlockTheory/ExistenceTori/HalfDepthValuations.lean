import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.DepthPins
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.DIV.Cons

variable {D : D7}

def halfE (Q : Par D) (i : Fin 2) : Ideal (𝓞 D.host.E) :=
  Q.l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}

def piGBar (X : ErrX D) (i : Fin 2) : 𝓞 D.host.E := barE D (X.piG i)

open Classical in

def piOf (Q : Par D) (X : ErrX D) (i : Fin 2) : 𝓞 D.host.E :=
  if piGBar X i ∈ halfE Q i then piGBar X i else X.piG i

open Classical in

def vdOf (D : D7) (p : ℕ) : ℝ :=
  if p ∈ D.host.small then D.host.vdH p
  else if p = D.host.q ∨ p = D.host.d then 1 / 2 else 0

def pageAt (D : D7) (T : ℕ) : DepPage where
  T := T
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small
  f := D.R.f
  r := D.R.r
  vd := vdOf D

def depAt (Q : Par D) (X : ErrX D) (T : ℕ) (ka wL wF : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E where
  Q := pageAt D T
  aL j := wtA (wL j)
  aF j := wtA (wF j)
  nW j := (wL j).n
  Dp j := ∑ τ, ∑ i, (ka j).aP τ i
  Dm j := ∑ τ, ∑ i, (ka j).aM τ i
  pi := piOf Q X

section Rec

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

end Rec

theorem bar_eq_barE (Q : Par D) (a : 𝓞 D.host.E) : Q.H.bar a = barE D a := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact Q.H.bar_eq a

end GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations
