import Mathlib
import Formalism.GaloisIrreducibility.Statement

open Finset Polynomial
open scoped ComplexOrder

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)

open Classical in

def BB (g N : ℕ) : Finset ℕ :=
  insert g ((Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))))

def BBCard : Prop :=
  ∀ g N : ℕ, 2 ≤ g → (BB g N).card ≤ 3 * N + 1

def BBDivides : Prop :=
  ∀ (l g d j : ℕ) (Y : ℝ), l.Prime → 1 ≤ d → 2 ≤ g → Y ≤ (g : ℝ) →
    g ^ d < l ^ (4 * padicValNat l (g ^ d - 1)) →
    Y < (l : ℝ) ^ (4 * j) → (∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y) →
    l ^ j ∣ g ^ d - 1

def ExcludedCount : Prop :=
  ∀ (N g₁ : ℕ) (Y : ℝ) (S : Finset ℕ), 1 ≤ N → 1 ≤ Y → g₁.Prime →
    (∀ g ∈ S, g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ ¬ Disjoint (BB g₁ N) (BB g N)) →
    (S.card : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))

def Prop1Core : Prop :=
  ∀ (N : ℕ) (Y : ℝ) (P : Finset ℕ), 1 ≤ N → 1 ≤ Y →
    (∀ g ∈ P, g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y) →
    ((3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < P.card) →
    ∃ g₁ ∈ P, ∃ g₂ ∈ P, g₁ ≠ g₂ ∧ Disjoint (BB g₁ N) (BB g₂ N)

def primeToPart {M : Type*} [Monoid M] (l : ℕ) (x : M) : M :=
  x ^ ((ordProj[l] (orderOf x)) ^ Nat.totient (ordCompl[l] (orderOf x)))

def PrimeToPartSpec : Prop :=
  ∀ (M : Type) [Monoid M] (l : ℕ) (x : M), l.Prime → IsOfFinOrder x →
    orderOf (primeToPart l x) = ordCompl[l] (orderOf x) ∧
      ∃ a : ℕ, x ^ (l ^ a) = primeToPart l x ^ (l ^ a)

def PrimeToPartEqIff : Prop :=
  ∀ (M : Type) [Monoid M] (l : ℕ) (x y : M), l.Prime → IsOfFinOrder x → IsOfFinOrder y →
    (primeToPart l x = primeToPart l y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a))

def GoodAt (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {ι J : Type} (N : ℕ)
    (f : ι → K[X]) (χ : ι → J → Kˣ) : Prop :=
  (∀ v, (f v).Monic ∧ (f v).natDegree = N ∧ (f v).coeff 0 ≠ 0) ∧
  (∀ v, Squarefree (f v)) ∧
  (∀ l : ℕ, l.Prime → l ∉ BB (Fintype.card K) N →
    ∀ v, Set.InjOn (primeToPart l) ((f v).rootSet L)) ∧
  (∀ l : ℕ, l.Prime → l ≠ Fintype.card K → ∀ v j, ∀ x ∈ (f v).rootSet L,
    primeToPart l x ≠ primeToPart l (algebraMap K L (χ v j : K)) ∧
    primeToPart l x ≠ primeToPart l (algebraMap K L ((χ v j)⁻¹ : Kˣ))) ∧
  (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ h : K[X], h ∣ f v ∧ h.natDegree = a) ∧
  (∃ v, ∃ P : K[X], Irreducible P ∧ P ∣ f v ∧ P.natDegree.Prime ∧
    N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N)

def Good (K₁ L₁ K₂ L₂ : Type) [Field K₁] [Fintype K₁] [Field L₁] [Algebra K₁ L₁]
    [Field K₂] [Fintype K₂] [Field L₂] [Algebra K₂ L₂] {ι₁ J₁ ι₂ J₂ : Type} (N : ℕ)
    (f₁ : ι₁ → K₁[X]) (χ₁ : ι₁ → J₁ → K₁ˣ) (f₂ : ι₂ → K₂[X]) (χ₂ : ι₂ → J₂ → K₂ˣ) : Prop :=
  GoodAt K₁ L₁ N f₁ χ₁ ∧ GoodAt K₂ L₂ N f₂ χ₂

open Classical in

def DivisorDegreeSubSum : Prop :=
  ∀ (K : Type) [Field K] (f : K[X]) (a : ℕ), f ≠ 0 →
    ((∃ h : K[X], h ∣ f ∧ h.natDegree = a) ↔
      IsSubSum ((UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree) a)

open Classical in

def LemmaP : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A)).card
      ≤ 7 * N.factorial

def monicOf {K : Type*} [Field K] {N : ℕ} (c : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ)

open Classical in

def SquarefreeCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 1 ≤ N →
    Fintype.card K ^ N ≤
      ((Finset.univ : Finset (Fin N → K)).filter
        (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card
      + 2 * Fintype.card K ^ (N - 1)

open Classical in

def IrredCountUpper : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    d * ((Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c))).card
      ≤ Fintype.card K ^ d

open Classical in

def IrredCountLower : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    Fintype.card K ^ d ≤
      d * ((Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c))).card
        + 2 * Fintype.card K ^ (d / 2)

open Classical in

def TypeCountExact : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((UniqueFactorizationMonoid.normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
    ∏ d ∈ Finset.Icc 1 N,
      (((Finset.univ : Finset (Fin d → K)).filter
        (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d)

open Classical in

def CycleTypeProb : Prop :=
  ∀ (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d)).card *
      ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial

def LemmaLWeight : Prop :=
  ∀ (d : Multiset ℕ) (g k : ℕ) (n : ℝ), (∀ x ∈ d, 1 ≤ x) → 2 ≤ g → 1 ≤ k → k ≤ d.sum →
    (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n →
    n ≤ ∑ i ∈ Finset.range (k + 1), (d.sum : ℝ) ^ i * (g : ℝ) ^ (k - i) →
    (1 - 1 / (g : ℝ)) / (g : ℝ) ^ d.sum ≤
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ∧
      (2 * d.sum ≤ g →
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ≤
          (1 + 6 * (d.sum : ℝ) / g) / (g : ℝ) ^ d.sum)

open Classical in

def CycleProbPrime : Prop :=
  ∀ N p : ℕ, p.Prime → p ≤ N → N < 2 * p →
    p * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => p ∈ σ.cycleType)).card
      = N.factorial

open Classical in

def CycleProbSum : Prop :=
  ∀ N : ℕ,
    (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) =
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
      (N.factorial : ℝ) / p

def PrimeRecipSum : Prop :=
  ∀ N : ℕ, 100 ≤ N →
    1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p

open Classical in

def SubfieldCount : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] (g d l : ℕ), l.Prime → 2 ≤ g → 2 ≤ d →
    Fintype.card L = g ^ d → l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g ^ d →
    (((Finset.univ : Finset Lˣ).filter
      (fun x => ∃ e, e ∣ d ∧ e < d ∧ primeToPart l x ^ (g ^ e - 1) = 1)).card : ℝ)
      ≤ d * (g : ℝ) ^ ((d : ℝ) / 2) * (g : ℝ) ^ ((d : ℝ) / 4)

open Classical in

def SamePartCount : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] (g d l : ℕ) (y : Lˣ), l.Prime → 2 ≤ g → 1 ≤ d →
    Fintype.card L = g ^ d →
    ((Finset.univ : Finset Lˣ).filter (fun x => primeToPart l x = primeToPart l y)).card
        = l ^ padicValNat l (g ^ d - 1) ∧
      (l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g ^ d →
        (((Finset.univ : Finset Lˣ).filter
          (fun x => primeToPart l x = primeToPart l y)).card : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4))

open Classical in

def ShareNV5 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → Type) [∀ v, Fintype (T v)]
    (w : ∀ v, T v → ℝ) (μ : (∀ v, T v) → ℝ) (K c : ℝ) (N J : ℕ) (P : Finset (Finset ι))
    (bad : ℕ → ∀ v, T v → Prop),
    P.card ≤ 2 → (∀ S ∈ P, S.card = J) → 0 ≤ K → 0 ≤ c →
    (∀ v t, 0 ≤ w v t) → (∀ v, ∑ t, w v t ≤ 1) → (∀ x, μ x ≤ K * ∏ v, w v (x v)) →
    (∀ a ∈ Icc 1 (N / 2), ∀ S ∈ P, ∀ v ∈ S, ∑ t ∈ univ.filter (bad a v), w v t ≤ c) →
    ∑ x ∈ univ.filter (fun x => ∃ S ∈ P, ∃ a ∈ Icc 1 (N / 2), ∀ v ∈ S, bad a v (x v)), μ x
      ≤ N * K * c ^ J

open Classical in

def FrobOrbitIrred : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (f : K[X]),
    f.Monic → Irreducible f →
    IsOrbit (fun x : L => x ^ Fintype.card K) (f.aroots L).toFinset ∧
      (f.aroots L).toFinset.card = f.natDegree

def centralIdem {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : MonoidAlgebra ℂ G :=
  ∑ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) •
    MonoidAlgebra.of ℂ G g

def CentralIdempotent : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V),
    (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    centralIdem ρ * centralIdem ρ = centralIdem ρ ∧
      ∀ x : MonoidAlgebra ℂ G, centralIdem ρ * x = x * centralIdem ρ

def CentralIdemOrthogonal : Prop :=
  ∀ (G V W : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial V] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    (∀ U : Submodule ℂ V, (∀ g, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) →
    (¬ ∃ φ : V ≃ₗ[ℂ] W, ∀ g x, φ (ρ g x) = σ g (φ x)) →
    centralIdem ρ * centralIdem σ = 0

def CentralIdemSelfAdjoint : Prop :=
  ∀ (G V : Type) [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    ρ.character g⁻¹ = (starRingEnd ℂ) (ρ.character g) ∧
      (centralIdem ρ).coeff g⁻¹ = (starRingEnd ℂ) ((centralIdem ρ).coeff g)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
