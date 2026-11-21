import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PerIntOnAmb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG

section
noncomputable section

namespace GlobalTheory.Core.Int

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7) (u : D.what₂.Word)

end GlobalTheory.Core.Int
end
end

section
noncomputable section

namespace GlobalTheory.Core.AtG

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable (D : D7) (EX : ErrX D) (u : D.what₂.Word)

def vDeg (i : Fin 2) (w : D.what₂.places.Pl) : ℝ := ∑ j ∈ Finset.Icc 1 D.R.m, vNN EX i u j w

def errF (D : D7) : ℝ := (D.R.f : ℝ) * D.R.m * (D.R.N D.R.m : ℝ) ^ 2

def errA (D : D7) : ℝ := errF D + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ)

def ColA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errF D)

def errStep (D : D7) : ℝ :=
  ∑ j ∈ Finset.range D.R.m, ((D.R.f : ℝ) * (D.R.N j : ℝ) * (D.R.N (j + 1) : ℝ) +
    2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ))

def ColStep : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errStep D)

def ColCoarse : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errA D)






example : ∑ j ∈ Finset.range 2, ((5 + j * 8) * (5 + (j + 1) * 8) + 2 * 2 ^ 2 * 21) = 674 ∧ 2 * 21 ^ 2 = 882 := by decide

example (D : D7) : errA D - errF D = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) := by unfold errA; ring

end GlobalTheory.Core.AtG
end
end

section
noncomputable section

namespace GlobalTheory.Core.AtG

open Formalism.BasicNotions NumberField GlobalTheory.Mem GlobalTheory.Mem.Col2

def BuiltG (D : D7) (EX : ErrX D) : Prop :=
  ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    I.Ok ∧ I.JetsIn ∧ I.Law0 l ∧
      (⟨D, EX.piG⟩ : Σ D' : D7, (Fin 2 → 𝓞 D'.host.E)) = ⟨I.rec7 l Z, X.piG⟩


theorem builtG_ind {Q : ∀ D : D7, ErrX D → Prop}
    (H : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Ok → I.JetsIn → I.Law0 l →
      ∀ EX : ErrX (I.rec7 l Z), EX.piG = X.piG → Q (I.rec7 l Z) EX) {D : D7} {EX : ErrX D} (h : BuiltG D EX) : Q D EX := by
  obtain ⟨B, X, I, l, Z, h1, h2, h3, e⟩ := h
  have e1 : D = I.rec7 l Z := congrArg Sigma.fst e
  subst e1
  exact H B X I l Z h1 h2 h3 EX (eq_of_heq (Sigma.mk.inj_iff.1 e).2)

end GlobalTheory.Core.AtG
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Core.AtG.BuiltModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

theorem under_inj (u : B.Word) (P Q : (B.primes X).vT u)
    (e : P.1.under (𝓞 B.host.F) = Q.1.under (𝓞 B.host.F)) : P = Q := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hc := GlobalTheory.MuOffMove.conjP_notMem_vT hPr P.2
  have hsp := (split_of_conj_ne₂ B.fields P.1 (P.1.under (𝓞 B.host.F)) hX (fun e => hc (e.symm ▸ P.2)) rfl).2
  refine Subtype.ext (((hsp Q.1).1 (congrArg HeightOneSpectrum.asIdeal e.symm)).resolve_right fun e' => hc (e' ▸ Q.2)).symm

def errOf (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) : ErrX (I.rec7 l Z) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong u := Ideal.mem_span_singleton.2 (X.piT_cong u)
  vPl u (P : (B.primes X).vT u) := P.1.under (𝓞 B.host.F)
  vPl_inj u := under_inj u
  norm_mem_place_ideal u (P : (B.primes X).vT u) :=
    (GlobalTheory.MuOffMove.natCast_mem_under (X := B.fields) P.1 (B.T u)).2 (T_mem (base_fields_primes_ok B X).2.1 u P)



theorem cong {D : D7} {EX : ErrX D} (h : BuiltG D EX) (i : Fin 2) :
    ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ EX.piG i - 1 :=
  builtG_ind (Q := fun D EX => ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ EX.piG i - 1)
    (fun _ X _ _ _ _ _ _ EX e => by rw [e]; exact X.piG_cong i) h



def negG {D : D7} (EX : ErrX D) : ErrX D :=
  { EX with
    piG := fun i => -EX.piG i
    piG_K := fun i => by simpa using neg_mem (EX.piG_K i)
    piG_norm := fun i => by simpa using EX.piG_norm i }



end GlobalTheory.Core.AtG.BuiltModel

end
end
