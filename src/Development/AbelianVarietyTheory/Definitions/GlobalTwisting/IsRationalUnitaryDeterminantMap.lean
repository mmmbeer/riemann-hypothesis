import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Formalism.FrobeniusOrbits.HostThickExists

section
open NumberField IntermediateField
open scoped Pointwise

namespace GlobalTheory.GH

noncomputable def cmConj (E : Type) [Field E] [NumberField E] [IsCMField E] : E ≃ₐ[ℚ] E :=
  (IsCMField.complexConj E).restrictScalars ℚ

structure GField (e : ℕ) where
  q : ℕ
  d : ℕ

  hyp : Formalism.FrobeniusOrbits.HostHyp q d
  q_ne_three : q ≠ 3
  two_le_e : 2 ≤ e
  E : Type
  [instField : Field E]
  [instNF : NumberField E]
  [instCM : IsCMField E]
  [instAb : IsAbelianGalois ℚ E]

  aE : E

  bE : E
  aE_sq : aE ^ 2 = -(q : E)
  bE_sq : bE ^ 2 = -(d : E)

  N : ℕ
  N_pos : 0 < N
  cyc : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)
  dvd_N : 2 ^ (e + 2) * q * d ∣ N

  N_split : ∀ p : ℕ, p.Prime → p ∣ N → p ≠ 2 → p ≠ d → jacobiSym (-(d : ℤ)) p = 1

  inertia_qd : ∀ p : ℕ, p = q ∨ p = d → ∀ P : Ideal (𝓞 E), P.IsPrime → ((p : ℕ) : 𝓞 E) ∈ P →
    ∀ σ τ : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → (∀ x : 𝓞 E, τ • x - x ∈ P) → σ = 1 ∨ τ = 1 ∨ σ = τ

  thE : E
  thE_spec : ∀ φ : E →+* ℂ, ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 ^ (e + 2)) ∧ φ thE = ζ + ζ⁻¹

  hp : (E ≃ₐ[ℚ] E) →* Formalism.FrobeniusOrbits.HGrp e
  hp_spec : ∀ (φ : E →+* ℂ) (ζ : ℂ), IsPrimitiveRoot ζ (2 ^ (e + 2)) → φ thE = ζ + ζ⁻¹ →
    ∀ (σ : E ≃ₐ[ℚ] E) (u : (ZMod (2 ^ (e + 2)))ˣ), hp σ = Formalism.FrobeniusOrbits.hcl e u ↔
      φ (σ thE) = ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val

attribute [instance] GField.instField GField.instNF GField.instCM GField.instAb

structure GHost (e : ℕ) extends GField e where

  big : ℕ
  qd_big : big < q ∧ big < d
  splitBound : ℕ
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ splitBound → jacobiSym (-(d : ℤ)) p = 1
  φ₀ : E →+* ℂ
  φ₀_mem : φ₀ bE = Complex.I * (Real.sqrt d : ℂ)
  𝔟 : Ideal (𝓞 E)
  𝔟_spec : differentIdeal (𝓞 ℚ⟮bE⟯) (𝓞 E) = 𝔟 * (cmConj E • 𝔟) ∧ 𝔟 ⊔ cmConj E • 𝔟 = ⊤
  levelPrimes : Finset ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes
  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i
  ccK : Ideal (𝓞 ℚ⟮bE⟯)
  ccK_ne_bot : ccK ≠ ⊥
  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 ℚ⟮bE⟯)}
  ccK_split : ∀ P : Ideal (𝓞 ℚ⟮bE⟯), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(d : ℤ)) (Ideal.absNorm P) = 1
  ccK_coprime : Nat.Coprime (Ideal.absNorm ccK) (30 * N) ∧ ∀ p ∈ levelPrimes, Nat.Coprime (Ideal.absNorm ccK) p

namespace GHost

variable {e : ℕ} (H : GHost e)

abbrev F : Subfield H.E := maximalRealSubfield H.E

abbrev K : IntermediateField ℚ H.E := ℚ⟮H.bE⟯

abbrev GG : Type := H.E ≃ₐ[ℚ] H.E

noncomputable def conj : H.E ≃ₐ[ℚ] H.E := cmConj H.E

@[instance_reducible] noncomputable def cmStar : StarRing H.E := NumberField.IsCMField.starRing H.E

def Psi : Subgroup H.GG := MulAction.stabilizer H.GG H.bE

noncomputable def emb (σ : H.GG) : H.E →+* ℂ := H.φ₀.comp (σ : H.E →+* H.E)

noncomputable def f : ℕ := Module.finrank ℚ H.F

def n (_H : GHost e) : ℕ := 2 ^ e

noncomputable def w : ℕ := NumberField.Units.torsionOrder H.E

noncomputable def rdE : ℝ := |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))

noncomputable def v : ℝ := H.rdE / 2

noncomputable def ka : ℝ := Real.pi / H.v

def sqrtMinusD : H.E := H.bE

noncomputable def xi0 : H.E := -1 / ((Ideal.absNorm H.ccK : H.E) * H.sqrtMinusD)

noncomputable def ccE : Ideal (𝓞 H.E) := Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK

noncomputable def AA0 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E))⁻¹

noncomputable def AA : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  (H.ccE : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) * H.AA0

end GHost

end GlobalTheory.GH
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.GH

def IsRoot {L : Type} [Field L] (x : L) : Prop := ∃ m : ℕ, 0 < m ∧ x ^ m = 1

structure CMData0 {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    {I : Type} (φ : I → L →+* ℂ) : Prop where
  real : IsTotallyReal F
  cplx : IsTotallyComplex L
  rank : Module.finrank F L = 2
  ne : c ≠ 1
  bij : Function.Bijective fun i => InfinitePlace.mk (φ i)



variable {e : ℕ} (H : GHost e)

instance psiFintype : Fintype H.Psi := Fintype.ofFinite _

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

def embPsi (g : H.Psi) : H.E →+* ℂ := H.emb (g : H.GG)

def IsConjPl (w w' : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → (x ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def IsSplitPl (v : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∃ x : 𝓞 H.E, x ∈ v.asIdeal ∧ ∀ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y ∉ v.asIdeal

def WtOK (a : H.Psi → ℤ) : Prop := ∀ ζ : H.E, IsRoot ζ → ∏ τ, embPsi H τ ζ ^ a τ = 1

structure IsClsF (ξ : HChar H.E) : Prop where
  unitary : ξ.IsUnitary
  unr : ∀ v, ξ.UnrAt v
  inf : ∀ k, ξ.inf k = 1
  triv : ξ.TrivOn H.F

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : GHost e} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (a : H.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -a τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (b : ℕ) (hb : b.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (b : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime b hb) ^ (2 * (j + 1)))⁻¹

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

variable (H)

def congG : Set (Ideles H.E) :=
  {a | a ∈ unitIdl H.E ∧ ∀ k v, OverP H (H.g k) v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1}

def KD : Subgroup (Ideles H.E) :=
  Subgroup.closure (congG H ∪ {a | ∃ v k, a = locF H.F v k})

abbrev DtT : Type := Ideles H.E ⧸ KD H

open Classical in

def tildeD (χ : HChar H.E) : DtT H →* ℂˣ :=
  if h : KD H ≤ (χ.1.comp (finPartI H.E)).ker then QuotientGroup.lift (KD H) (χ.1.comp (finPartI H.E)) h else 1

def IsRationalUnitaryDeterminantMap (f : (letI := H.cmStar; unitary H.E) →* DtT H) : Prop :=
  letI := H.cmStar
  ∀ (k : H.Eˣ) (z : unitary H.E), (z : H.E) * H.conj (k : H.E) = k → QuotientGroup.mk (diagUnits H.E k) = f z

open Classical in

def e1T : (letI := H.cmStar; unitary H.E) →* DtT H := if h : ∃ f, IsRationalUnitaryDeterminantMap H f then h.choose else 1

def IsTwist (S : Set ℕ) (ξ : HChar H.E) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) ∧ ξ.TrivOn H.F ∧ (∀ v, ξ.TameAt v) ∧
    ∀ v, ¬ ξ.UnrAt v → IsSplitPl H v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ Ideal.absNorm v.asIdeal ∉ S

structure HFrame {m : ℕ} (a : Fin m → H.Psi → ℚ) where
  P : PiBar H
  W : Omg H
  mu0 : Fin m → HChar H.E
  eta : HChar H.E
  chiPsi : HChar H.E
  del : HChar H.E
  del' : HChar H.E
  isMu0 : ∀ j, IsMu0 P W (a j) j.1 (mu0 j)
  isEta : IsEtaT H eta
  isChi : IsChiPsi H chiPsi
  isDel : IsDelta (H := H) H.pde del
  isDel' : IsDelta (H := H) H.pde' del'

end GlobalTheory.GH
end
end
