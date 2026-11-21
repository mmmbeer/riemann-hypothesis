import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataErr
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyRepresentativeSystems

section Concrete

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable (E n SG) in

def levU : Subgroup (GLG E n SG) :=
  Subgroup.pi Set.univ fun w : SG => uniUT n (𝓞 E ⧸ w.1.asIdeal) n []

def SameCls (d d' : DecoSet E n ST SG) : Prop :=
  ∃ γ : UF E n, ∃ h ∈ levU E n SG, ((γ, h) : UF E n × GLG E n SG) • d = d'

theorem SameCls.symm {d d' : DecoSet E n ST SG} (h : SameCls d d') : SameCls d' d := by
  obtain ⟨γ, k, hk, rfl⟩ := h
  exact ⟨γ⁻¹, k⁻¹, inv_mem hk, inv_smul_smul ((γ, k) : UF E n × GLG E n SG) d⟩

theorem SameCls.trans {d d' d'' : DecoSet E n ST SG} (h : SameCls d d') (h' : SameCls d' d'') :
    SameCls d d'' := by
  obtain ⟨γ, k, hk, rfl⟩ := h
  obtain ⟨γ', k', hk', rfl⟩ := h'
  exact ⟨γ' * γ, k' * k, mul_mem hk' hk,
    mul_smul ((γ', k') : UF E n × GLG E n SG) ((γ, k) : UF E n × GLG E n SG) d⟩

end Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def conjInt (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

def primesT {D : D7} (X : ErrX D) (u : D.what₂.Word) : Finset (HeightOneSpectrum (𝓞 D.host.E)) := divs (X.piT u)

open Classical in

def primesG {D : D7} (X : ErrX D) : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
  divs (conjInt D (X.piG 0)) ∪ divs (conjInt D (X.piG 1))

abbrev ColPt {D : D7} (X : ErrX D) (u : D.what₂.Word) : Type :=
  DecoSet D.host.E D.R.k (primesT X u) (primesG X)

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyRepresentativeSystems
