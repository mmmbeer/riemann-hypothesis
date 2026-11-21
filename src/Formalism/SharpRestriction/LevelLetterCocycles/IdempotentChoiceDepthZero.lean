import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas

section
noncomputable section

namespace Formalism.MainNotions.ReducibleThreeDim

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.BasicNotions

section PartB

open Real

open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Real

def BD (s q d e : ℕ) : ℝ :=
  (2 : ℝ) ^ (s + 1) * (((e : ℝ) + 2) * logb 2 ((2 : ℝ) ^ (s + 2) * q * d) +
    ((e : ℝ) + 1) * logb 2 5 + 1 +
    logb 2 (((e : ℝ) + 1) * ((e + 1).factorial : ℝ) * ((e + 2).factorial : ℝ)))

section Field

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def ShaLengthBoundAt (LD : Formalism.GaloisCohomology.LData E Ω 2) (s q d : ℕ) : Prop :=
  ∀ e : ℕ, 1 ≤ e → Formalism.GaloisCohomology.shaLen LD (e : ℤ) ≠ ⊤ ∧
    ((Formalism.GaloisCohomology.shaLen LD (e : ℤ)).toNat : ℝ) ≤
      5 * BD s q d e + 2 * ((s : ℝ) + 2 + (padicValNat 2 e : ℝ))

def rd (E : Type) [Field E] [NumberField E] : ℝ :=
  |(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))

def CorAt (LD : Formalism.GaloisCohomology.LData E Ω 2) (s q d : ℕ) (C : ℝ) : Prop :=
  (∀ t : ℕ, (∀ e ∈ Finset.Ioo 0 t, Formalism.GaloisCohomology.shaLen LD (e : ℤ) ≠ ⊤) ∧
    ∑ e ∈ Finset.Ioo 0 t, ((Formalism.GaloisCohomology.shaLen LD (e : ℤ)).toNat : ℝ) ≤
      C * (2 : ℝ) ^ (s + 1) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (2 : ℝ) ^ s * q * d)) ∧
  (padicValNat 2 (classNumber E) : ℝ) ≤ C * (2 : ℝ) ^ (s + 1) * Real.log (rd E)

end Field

def ShaLengthVersionTwo : Prop :=
  ∀ (s q d : ℕ), HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (s + 2) q d ζ a b →
  ∀ (Ω : Type) [Field Ω] [Algebra (hostE ζ a b) Ω] [IsAlgClosure (hostE ζ a b) Ω]
    (LD : Formalism.GaloisCohomology.LData (hostE ζ a b) Ω 2), ShaLengthBoundAt LD s q d

def CyclotomicCorollaryBound (C : ℝ) : Prop :=
  ∀ (s q d : ℕ), HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (s + 2) q d ζ a b →
  ∀ (Ω : Type) [Field Ω] [Algebra (hostE ζ a b) Ω] [IsAlgClosure (hostE ζ a b) Ω]
    (LD : Formalism.GaloisCohomology.LData (hostE ζ a b) Ω 2), CorAt LD s q d C

end PartB

def Conclusion1 (_D : D7) : Prop := ShaLengthVersionTwo

def Conclusion2 (_D : D7) (C : ℝ) : Prop := CyclotomicCorollaryBound C

def PointsLemma (D : D7) : Prop := D.nd.ShaFinTwo

def ShaBoundTheoremB (D : D7) (C : ℝ) : Prop := Conclusion1 D ∧ Conclusion2 D C ∧ PointsLemma D

def epsL (l : ℕ) : ℝ := 1 / (l : ℝ) ^ 2

def TwLoc (D : D7) (i : D.nd.Loc) : Prop := D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0

section PartA

open Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.TruncatedSeriesCountingIdentities Formalism.BasicNotions.Loc ReciprocityTheory.Gal

variable {D : D7}

def Over (w : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = v.asIdeal

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

section AtW

variable {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
  (Cx : CoefExt D i w hw)

def jumpsR (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) : Set ℤ :=
  {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (locC Cx (rTwO D.nd i r x))) τ a}

end AtW

open Classical in
def JumpHost (large₂ : SizeData₂ D) (vplus : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : CoefExt D i w hw) (x : D.nd.X i) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    {a ∈ jumpsR i r Cx x τ | |(a : ℝ) - ((D.R.t : ℝ) - 1) / 2| ≤ large₂.etaSz ∧ ¬ (0 ≤ a ∧ a < D.R.t)}.ncard ≤ D.R.m ∧
    {a ∈ jumpsR i r Cx x τ | (large₂.Sc + large₂.etaSz + D.R.t : ℝ) < (if Over w vplus then (1 : ℝ) else -1) * a}.ncard =
      D.R.r - D.R.m ∧
    (∀ a : ℤ, 0 ≤ a → a < D.R.t → a ∈ jumpsR i r Cx x τ) ∧ (-1 : ℤ) ∉ jumpsR i r Cx x τ ∧
    (D.R.t : ℤ) ∉ jumpsR i r Cx x τ ∧
    ∀ a ∈ jumpsR i r Cx x τ, |(a : ℝ) - ((D.R.t : ℝ) - 1) / 2| ≤ large₂.etaSz ∨ (0 ≤ a ∧ a < D.R.t) ∨
      (large₂.Sc + large₂.etaSz + D.R.t : ℝ) < (if Over w vplus then (1 : ℝ) else -1) * a

def expo {X : Type} [AddCommGroup X] [Module (D.nd.O i) X] (M : Submodule (D.nd.O i) X) : ℕ :=
  sInf {c : ℕ | ∀ m ∈ M, ((D.nd.l i : D.nd.O i) ^ c) • m = 0}

def H0WeightInvariants (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (KOG (D.nd.O i) D.R.r) :=
  Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))

def H0DualInvariants (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (D.nd.O i) (KOG (D.nd.O i) D.R.r) :=
  Representation.invariants ((WKG (T2O D.nd i ρ π)).comp (decS D.nd w))

def c0 (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  max (max (expo i (H0WeightInvariants i ρ π w)) (expo i (H0DualInvariants i ρ π w)))
    (sSup {c : ℕ | ∃ w', IsConjPl D.host w w' ∧ c = expo i (H0DualInvariants i ρ π w')})

open Classical in
def jCol (π : D.nd.X i) (dc : Decl D i) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  if h : w ∈ dc.col then Br.jW D.loc D.nbr i w ((dc.cover w).1 (Or.inr h)) ρ π else 0

end PartA

end Formalism.MainNotions.ReducibleThreeDim
end
end

section
noncomputable section

namespace Formalism.MainNotions.IdempotentChoiceDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Obj51

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))

def IsOrthogonalIdempotentDecomposition (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) S.g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
    N.l i - 1 ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0)) ∧
    IsUnit (del51 N S S.π')) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))

end Obj51

end Formalism.MainNotions.IdempotentChoiceDepthZero
end
end
