import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published.Kato Polynomial
open CongruenceSubgroup UpperTheory.V.Alg
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Lit

def OrdPoly {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] (a b : ℤ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∃ (A : ValuationSubring Ω) (N : ℕ), A.valuation (l : Ω) < 1 ∧ 1 ≤ N ∧ ∀ s ∈ Ine (F := ℚ) A, (∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) →
    (V s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
      (X - C ((cycBar ℚ Ω l s ^ a : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar ℚ Ω l s ^ b : (Qbar l)ˣ) : Qbar l))

def KatoUseN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ (f : Af.Newform (2 * e + 1)) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
      f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → OrdPoly (e : ℤ) (-(e : ℤ)) W →
      ∀ (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → Af.KillsMu M φ → Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W φ))

structure InpN : Prop extends U3.CohInp where
  lemM : LemmaM
  lemM' : LemmaM'
  lemP : LemmaP
  kato : KatoUseN
  adK : Af.AdVanishK
  adQ : Af.AdVanishQ
  newAut : Af.NewformAut
  number : Af.CongruenceNumberRankThree

end UpperTheory.V.Lit
