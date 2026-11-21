import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TypePrimesOfLevel
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ConjugacyRepresentativeSystems

noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n n' : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def castPt (h : n = n') : DecoSet E n ST SG ≃ DecoSet E n' ST SG :=
  Equiv.cast (congrArg (fun m => DecoSet E m ST SG) h)

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem k_eq_N (D : D7) : D.R.k = D.R.N 0 := by simp [Ranks.N]

def ptEquiv (X : ErrX D) (u : D.what₂.Word) : ConjugacyRepresentativeSystems.ColPt X u ≃ UnipotentLevelStabilisers.ColPt D X.piG (X.piT u) :=
  castPt (k_eq_N D)

theorem norm_iff (π : 𝓞 D.host.E) (g : ℕ) :
    π * UnipotentLevelStabilisers.conjInt D π = (g : 𝓞 D.host.E) ↔
      (π : D.host.E) * D.host.conj (π : D.host.E) = (g : D.host.E) := by
  rw [← RingOfIntegers.coe_injective.eq_iff, map_mul, map_natCast]
  rfl

def errOf (X₀ : ErrX D) {πg : Fin 2 → 𝓞 D.host.E} {πT : D.what₂.Word → 𝓞 D.host.E}
    (hg : UnipotentLevelStabilisers.TypeGenTie D πg) (hT : UnipotentLevelStabilisers.LevelGenTie D πT) : ErrX D where
  piG := πg
  piG_K i := (hg i).1
  piG_norm i := (norm_iff _ _).mp (hg i).2.1
  piT := πT
  piT_K u := (hT u).1
  piT_norm u := (norm_iff _ _).mp (hT u).2.1
  piT_cong u := Ideal.mem_span_singleton.mpr (hT u).2.2
  vPl := X₀.vPl
  vPl_inj := X₀.vPl_inj
  norm_mem_place_ideal := X₀.norm_mem_place_ideal

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
