import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def ImQ (E : Type) [Field E] (d : ℕ) : Prop :=
  0 < d ∧ ∃ x : E, x ^ 2 = -(d : E)

def SqAt (d q : ℕ) [Fact q.Prime] : Prop :=
  IsSquare (-(d : ℚ_[q]))

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def UsPl (d : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  IsSplitAt w ∧ ∀ (q : ℕ) (hq : q.Prime), ((q : ℕ) : 𝓞 E) ∈ w.asIdeal → @SqAt d q ⟨hq⟩

def ApartAll (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u ∈ S, Apart w u

def GenAt (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ B, (CG.mk π).HasSat w B → Gen a (normV w) B

structure NbrW (l : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (w₀ : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a)
    (π π' : CuspSub E a) : Prop where
  scope : ScopeOffT l T π'
  inf : ∀ τ, (CG.mk π').infChar τ = (CG.mk π).infChar τ
  level : HasLevel w₀ Kw π'

theorem apartAll_empty (w : HeightOneSpectrum (𝓞 E)) : ApartAll (∅ : Finset (HeightOneSpectrum (𝓞 E))) w :=
  fun _ h => absurd h (Finset.notMem_empty _)

example : ¬ ImQ ℚ 1 := fun ⟨_, x, hx⟩ => by
  have h := sq_nonneg x
  push_cast at hx
  linarith

end GlobalTheory.CongL

end
