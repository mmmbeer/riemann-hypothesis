import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfKillsOne

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O)

abbrev EmbOver (K : Type) [Field K] [Algebra Qp K] [Algebra K₀ K] (e : K₀ →ₐ[Qp] LL) : Type :=
  {τ : K →ₐ[Qp] LL // ∀ x : K₀, τ (algebraMap K₀ K x) = e x}

def diag (n : ℕ) (a : O⟦X⟧) : LetA O n := fun _ => a

def KillsN {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (i : ZMod n) (a : O⟦X⟧) : Prop :=
  ∀ y ∈ W.Nl T' i, ∃ x ∈ W.Nl T i, W.map f x = diag n a • y

variable [NeZero n] {R} (jE : R.EE →ₐ[O] W.EE)

def vec {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) (x : DD R n r) : W.DD T :=
  ∑ i, ∑ k, jE (x i k) • b i k

omit [NeZero n] in

def KillsExt (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (T : LocLat G Qp LL O) (𝒦 : ZMod n → O⟦X⟧ → Prop) : Prop :=
  ∀ (Y U : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (pr : LatHom Y.L U.L),
    (∀ g x, U.ρ g x = x) → IsSESLat (Qp := Qp) ι pr → IsCrys PD Y.ρ →
      ∀ (i : ZMod n) (a : O⟦X⟧), 𝒦 i a → KillsN W pr i (j a)

omit [NeZero n] in

def JumpCmp [IsDomain O] (β : ∀ i, Fin R.e ≃ EmbOver K (W.emb i)) (T : LocLat G Qp LL O) {r : ℕ}
    (S : Sys R n r) : Prop :=
  ∀ (i : ZMod n) (τ : Fin R.e) (a : ℤ),
    (S.IsJump i τ a ↔ IsJumpV PD T.ρ (β i τ).1 a) ∧
      (S.count i τ a a : ℤ) = multV PD T.ρ (β i τ).1 a

example (T : LocLat G Qp LL O) (i : ZMod n) : KillsN W (latId T) i 1 := fun y hy =>
  ⟨y, hy, by rw [W.map_id]; exact (one_smul (LetA O n) y).symm⟩

example {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) : vec W jE b 0 = 0 := by
  simp [vec]

end Generic

variable {l : ℕ} [Fact l.Prime]

instance finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

instance neZero_finrank_maxUnramifiedSubfield (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) :=
  ⟨Module.finrank_pos.ne'⟩

end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
