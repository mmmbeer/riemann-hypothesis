import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

section Field

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

def Amb.jetSet : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ),
    InRange Sall D c N N' x ∧ z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m}

def Amb.jetField : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (A.jetSet a b Sall D)

def rangeIF {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange

end Field

open Cardinal in

def FixedOfAut : Prop :=
  ∀ k : IntermediateField ℚ ℂ, #k ≤ ℵ₀ → ∀ z : ℂ, (∀ s : ℂ ≃+* ℂ, (∀ x ∈ k, s x = x) → s z = z) → z ∈ k

section KR

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1)

def kRGen : Set ℂ :=
  {z | ∃ τ x, z = TaylorLogMetric.embT D τ x} ∪ {TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc δ), TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc δ)} ∪
    {z | ∃ t : ℂ, t ∉ B.L.lattice ∧ (((2 * D0) ^ 2 : ℕ) : ℂ) * t ∈ B.L.lattice ∧ (z = B.L.weierstrassP t ∨ z = B.L.derivWeierstrassP t)} ∪
    Set.range cD ∪ {TaylorLogMetric.taylor D (B.thZero 1 1) α}

def kR : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (kRGen B cD D0 α)

end KR

def Amb.GalInv {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (k : IntermediateField ℚ ℂ) : Prop :=
  ∀ s : ℂ ≃+* ℂ, (∀ x ∈ k, s x = x) → ∀ z ∈ A.jetSet a b Sall D, s z = z

section Norm

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ)

def RatKHyp0 : Prop :=
  s.Ok ∧ TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ ∧ Even a ∧ Even b ∧ 0 < D0 ∧
    (ambOf s B χ cD : Amb X).LaHyp a b Sall ∧ ∀ P ∈ Sall, (2 : 𝓞 X.E) ∉ P.asIdeal

def RatKHyp (α : TaylorLogMetric.Mono D 1 1) : Prop :=
  RatKHyp0 s B χ cD a b Sall D0 ∧ TaylorLogMetric.taylor D (B.thZero 1 1) α ≠ 0

end Norm

def RatKGal : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1), RatKHyp s B χ cD a b Sall D0 α →
    (ambOf s B χ cD : Amb X).GalInv a b Sall D0 (kR B cD D0 α)

section Tied

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.VQTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Set.range (t.ent.ev u μ i c) =
    {f | ∃ P ∈ DIV.VV D.what₂.LL (lam u i), f = evG ((t.O u μ).frm i) (sh u i) D.what₂.embLL P}

def KerEntTied.WtTie {ex : Extra D L hT Gi Gl K Y cX} (_t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ) : Prop :=
  ∀ u μ i, i < D.R.m → (∀ τ r, (lam u i τ).natW r + n u i τ = nuT D u i τ r) ∧ (∀ τ, sh u i τ + (D.chTw u μ).sSharp i τ = n u i τ) ∧
    (∀ τ, sh u (i + 1) τ = -(D.chTw u μ).sDiv i τ) ∧ JetInVV D.what₂.LL (lam u i) (lam u (i + 1)) (n u i)

end Tied

section Choice

abbrev fieldsWithK (X : Fields) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (e : X.Tau → X.E →+* M) : Fields :=
  { X with K := M, fieldK := inferInstance, nfK := inferInstance, starK := inferInstance, emb := e }

def Amb.withK {X : Fields} (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M) :
    Amb (fieldsWithK X M fun τ => (X.embC A.σ₀ τ).codRestrict M (hM τ)) where
  σ₀ := algebraMap M ℂ
  δ := A.δ
  d := A.d
  sc := A.sc
  AA := A.AA
  cD := A.cD
  e := A.e
  chiF := A.chiF

end Choice

def JetFieldLeKR : Prop :=
  RatKGal → ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1), RatKHyp s B χ cD a b Sall D0 α →
    FiniteDimensional ℚ (kR B cD D0 α) → (ambOf s B χ cD : Amb X).jetField a b Sall D0 ≤ kR B cD D0 α

open Classical in

def degAt {ι : Type} {a b : ℕ} (m : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := (m.support.filter fun k => k.1 = τ).sum fun k => m k

def Amb.JetsRatDeg {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m

def JetsRatDegOf : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ), A.JetsRat a b Sall D → A.JetsRatDeg a b Sall D dg

def JetLocal : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K),
    (∀ m, (∀ τ, degAt m τ = ∑ r, ((lam τ).natW r + n τ)) → J m = J' m) → ∀ P ∈ DIV.VV K lam, jetMap J n P = jetMap J' n P

def KerEntTied.RK {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (m : DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ),
    (∀ τ, degAt m τ = ∑ r, nuT D u i τ r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k = ((D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c') * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') m

end Formalism.L2.Ker
