import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteGenOfWeakAxioms

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace AlgT

variable (d : Data K ι Ω WT A)

abbrev OmT (c : ι) : Type := FractionRing (MvPolynomial (TVar d.D d.N) (Ω c))

def iKp (c : ι) : KTp K d.D d.N →+* OmT d c :=
  (algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c)).comp
    (MvPolynomial.map (algebraMap K (Ω c)))

theorem iKp_injective (c : ι) : Function.Injective (iKp d c) :=
  (IsFractionRing.injective (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c)).comp
    (MvPolynomial.map_injective _ (algebraMap K (Ω c)).injective)

def iK (c : ι) : KTf K d.D d.N →+* OmT d c :=
  IsFractionRing.lift (A := KTp K d.D d.N) (g := iKp d c) (iKp_injective d c)

def iΩ (c : ι) : Ω c →+* OmT d c :=
  (algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c)).comp MvPolynomial.C

def xT (c : ι) (j : Fin (d.N + 1)) : OmT d c :=
  iΩ d c (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))

def sT (c : ι) (i : Fin (d.D + 1)) : OmT d c :=
  ∑ j, algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c) (MvPolynomial.X (i, j)) * xT d c j

def yT (c : ι) (k : Fin d.D) : OmT d c := sT d c k.succ / sT d c 0

def A0 (c : ι) : Subring (OmT d c) := Subring.closure (Set.range (iK d c) ∪ Set.range (yT d c))

def Fy (c : ι) : Subfield (OmT d c) := Subfield.closure (Set.range (iK d c) ∪ Set.range (yT d c))

def evY (c : ι) : MvPolynomial (Fin d.D) (KTf K d.D d.N) →+* OmT d c :=
  MvPolynomial.eval₂Hom (iK d c) (yT d c)

def uT (c : ι) (e : ℕ) (f : A c) : OmT d c :=
  iΩ d c (ratio (Ω := Ω c) f (d.w (d.jc c) c ^ e)) / sT d c 0 ^ e

def combP (c : ι) (e m : ℕ) (q : Fin m → KTp K d.D d.N) (f : Fin m → A c) :
    MvPolynomial (TVar d.D d.N) (Ω c) :=
  ∑ i, MvPolynomial.map (algebraMap K (Ω c)) (q i) *
    MvPolynomial.C (ratio (Ω := Ω c) (f i) (d.w (d.jc c) c ^ e))

def uC (c : ι) (e m : ℕ) (q : Fin m → KTp K d.D d.N) (f : Fin m → A c) : OmT d c :=
  algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c) (combP d c e m q f) / sT d c 0 ^ e

def phiS (c : ι) : MvPolynomial (TVar d.D d.N) (Ω c) →+* OmS (Ω c) d.D d.N :=
  (MvPolynomial.aeval (R := Ω c) (sImg (D := d.D) (d.jc c) (d.x c))).toRingHom

def pS (c : ι) : Ideal (MvPolynomial (TVar d.D d.N) (Ω c)) := RingHom.ker (phiS d c)

instance pS_isPrime (c : ι) : (pS d c).IsPrime := RingHom.ker_isPrime _

abbrev RS (c : ι) : Type := Localization.AtPrime (pS d c)

abbrev mmS (c : ι) : Ideal (RS d c) := IsLocalRing.maximalIdeal (RS d c)

end AlgT

open AlgT

def TrdegD (d : Data K ι Ω WT A) (c : ι) : Prop :=
  Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j =>
    ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) = d.D

def NormOrderStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, TrdegD d c →
    ∀ [FiniteDimensional (Fy d c) (OmT d c)],
    ∀ (e n : ℕ) (g : MvPolynomial (TVar d.D d.N) (Ω c)),
    algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (RS d c) g ∈ mmS d c ^ n →
    ∀ Q : MvPolynomial (Fin d.D) (KTf K d.D d.N),
      ((Algebra.norm (Fy d c) (algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c) g /
        sT d c 0 ^ e) : Fy d c) : OmT d c) = evY d c Q →
      ∀ α ∈ Q.support, n * Module.finrank (Fy d c) (OmT d c) ≤ α.sum fun _ k => k

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
