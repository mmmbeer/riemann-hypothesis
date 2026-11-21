import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable (E n SG) in

def unipLevel : Subgroup (GLG E n SG) :=
  Subgroup.pi Set.univ fun w : SG => uniUT n (𝓞 E ⧸ w.1.asIdeal) n []

def SameClass (d d' : DecoSet E n ST SG) : Prop :=
  ∃ (γ : UF E n) (h : GLG E n SG), h ∈ unipLevel E n SG ∧ ((γ, h) : UF E n × GLG E n SG) • d = d'

end Generic

variable (D : D7)

def conjInt : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

def condE : ℕ := D.host.QS * D.host.q * D.host.d

def TypeGenTie (πg : Fin 2 → 𝓞 D.host.E) : Prop :=
  ∀ i, (πg i : D.host.E) ∈ D.host.K ∧ πg i * conjInt D (πg i) = (D.host.g i : 𝓞 D.host.E) ∧
    ((condE D : ℕ) : 𝓞 D.host.E) ∣ πg i - 1

def LevelGenTie (πT : D.what₂.Word → 𝓞 D.host.E) : Prop :=
  ∀ u, (πT u : D.host.E) ∈ D.host.K ∧ πT u * conjInt D (πT u) = ((D.mem u).A.T : 𝓞 D.host.E) ∧
    ((condE D * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E) ∣ πT u - 1

open Classical in

def typePrimes (πg : Fin 2 → 𝓞 D.host.E) : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
  divs (conjInt D (πg 0)) ∪ divs (conjInt D (πg 1))

abbrev ColPt (πg : Fin 2 → 𝓞 D.host.E) (π : 𝓞 D.host.E) : Type :=
  letI := D.host.cmStar; DecoSet D.host.E (D.R.N 0) (divs π) (typePrimes D πg)

def TypePrimesLarge : Prop := ∀ i, 2 * D.R.f * D.R.k + 1 < D.host.g i

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

end
