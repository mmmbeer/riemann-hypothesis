import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField

noncomputable section

namespace Formalism.MainNotions.PGAL

open Formalism.BasicNotions NumberField

section BaseChange

variable {K : Type} [Field K] [NumberField K] [StarRing K]

open Classical in

def frS (A : HLat K) (s : K →+* ℂ) : Matrix A.ι A.ι ℂ :=
  if (InfinitePlace.mk s).embedding = s then A.X (InfinitePlace.mk s)
  else (A.X (InfinitePlace.mk s)).map (starRingEnd ℂ)

def ptS (A : HLat K) (s : K →+* ℂ) (x : A.V) : EuclideanSpace ℂ A.ι :=
  (WithLp.equiv 2 (A.ι → ℂ)).symm (Matrix.mulVec (frS A s)⁻¹ (fun i => s (A.b.repr x i)))

def spS (A : HLat K) (s : K →+* ℂ) (U : Submodule K A.V) : Submodule ℂ (EuclideanSpace ℂ A.ι) :=
  Submodule.span ℂ (ptS A s '' (U : Set A.V))

def mapS (A B : HLat K) (s : K →+* ℂ) (φ : A.V →ₗ[K] B.V) :
    EuclideanSpace ℂ A.ι →ₗ[ℂ] EuclideanSpace ℂ B.ι :=
  Matrix.toEuclideanLin ((frS B s)⁻¹ * (LinearMap.toMatrix A.b B.b φ).map s * frS A s)

end BaseChange

structure Loc (D : D7) (Z : DivX D) where

  MtjH : ℕ → HLat D.what₂.LL
  MtjH_good : ∀ j, (MtjH j).Good

  jT : ∀ j, (MtjH j).V ≃ₗ[D.what₂.LL] D.what₂.MtL D.what₂.mu0 j

  jT_lat : ∀ j x, x ∈ (MtjH j).L ↔ ∃ c : D.what₂.Mt D.what₂.mu0 j → 𝓞 D.what₂.LL,
    D.what₂.jMt D.what₂.mu0 j (jT j x) =
      ∑ v ∈ (D.what₂.MtLat D.what₂.mu0 j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  jT_norm : ∀ j x, Formalism.HermitianLatticesTheory.normAt (MtjH j).b (MtjH j).X (InfinitePlace.mk D.what₂.embLL) x =
    ‖D.what₂.jMt D.what₂.mu0 j (jT j x)‖

  TT : Type
  hk : ∀ j, TT → Module.End D.what₂.LL (MtjH j).V
  hk_comm : ∀ j t t', Commute (hk j t) (hk j t')
  hkAd : TT → TT

  ix : EigIdx D Z

section Objects

variable (D : D7) (Z : DivX D) (Y : Loc D Z)

open Classical in

def thL (j : ℕ) : (Y.MtjH j).V →ₗ[D.what₂.LL] (Z.MjH j).V :=
  if h : ∀ x : D.what₂.MtL D.what₂.mu0 j, ∃ y, Z.jM j y = D.what₂.thetaP D.what₂.mu0 j (D.what₂.jMt D.what₂.mu0 j x) then
    (Idx.thetaL Z D.what₂.mu0 j h) ∘ₗ (Y.jT j).toLinearMap
  else 0

def jC (j : ℕ) : (Y.MtjH j).V →ₛₗ[D.what₂.embLL] D.what₂.Mt D.what₂.mu0 j :=
  (D.what₂.jMt D.what₂.mu0 j).comp (Y.jT j).toLinearMap

def MjPart (j : ℕ) (π : D.what₂.FT) : Submodule D.what₂.LL (Z.MjH j).V := (DV.sum₃ Y.ix j (Y.ix.cOf π)).comap (Z.jM j)

def goodPartRationalPoints (j : ℕ) : Submodule D.what₂.LL (Y.MtjH j).V := (LinearMap.range (D.what₂.eMt D.what₂.mu0 j)).comap (jC D Z Y j)

def ZjL (j : ℕ) : Submodule D.what₂.LL (Y.MtjH j).V := (Idx.Z0 D D.what₂.mu0 j).comap (jC D Z Y j)

def KerL (j : ℕ) : Submodule D.what₂.LL (Y.MtjH j).V := LinearMap.ker (thL D Z Y j) ⊓ goodPartRationalPoints D Z Y j

def ZjPart (j : ℕ) (π : D.what₂.FT) : Submodule D.what₂.LL (Y.MtjH j).V :=
  ZjL D Z Y j ⊓ (MjPart D Z Y j π).comap (thL D Z Y j)

def thS (j : ℕ) (s : D.what₂.LL →+* ℂ) :
    EuclideanSpace ℂ (Y.MtjH j).ι →ₗ[ℂ] EuclideanSpace ℂ (Z.MjH j).ι :=
  mapS (Y.MtjH j) (Z.MjH j) s (thL D Z Y j)

def IsLamS (j : ℕ) (π : D.what₂.FT) (s : D.what₂.LL →+* ℂ) (c : ℝ) : Prop :=
  ∀ y ∈ spS (Z.MjH j) s (MjPart D Z Y j π), thS D Z Y j s (LinearMap.adjoint (thS D Z Y j s) y) = (c : ℂ) • y

def LogLamDef : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, MjPart D Z Y j π ≠ ⊥ → ∀ s c, IsLamS D Z Y j π s c → Z.logLam j π s = Real.log c

end Objects

def SameK (D : D7) (s : D.what₂.LL →+* ℂ) : Prop :=
  ∃ g : D.R.Psi, s.comp D.embE = D.host.emb (g : D.R.GG)

structure CjDat (D : D7) (s : D.what₂.LL →+* ℂ) where

  ga : Equiv.Perm D.what₂.Tau
  ga_def : ∀ τ, (s.comp D.embE).comp
      ((D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG) : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E) =
    D.host.emb ((D.eTau (ga τ) : D.R.Psi) : D.R.GG)

  MtC : ℕ → Type
  [iMt : ∀ j, NormedAddCommGroup (MtC j)]
  [iMti : ∀ j, InnerProductSpace ℂ (MtC j)]
  [iMtf : ∀ j, FiniteDimensional ℂ (MtC j)]

  MjC : ℕ → Type
  [iMj : ∀ j, NormedAddCommGroup (MjC j)]
  [iMji : ∀ j, InnerProductSpace ℂ (MjC j)]
  [iMjf : ∀ j, FiniteDimensional ℂ (MjC j)]

  thC : ∀ j, MtC j →ₗ[ℂ] MjC j

  eC : ∀ j, MtC j →ₗ[ℂ] MtC j
  eC_idem : ∀ j, eC j ∘ₗ eC j = eC j
  eC_sa : ∀ j, (eC j).IsSymmetric

  isotC : ∀ j, D.what₂.FT → Submodule ℂ (MjC j)

attribute [instance] CjDat.iMt CjDat.iMti CjDat.iMtf CjDat.iMj CjDat.iMji CjDat.iMjf

abbrev CjFam (D : D7) : Type 1 := ∀ s : D.what₂.LL →+* ℂ, SameK D s → CjDat D s

def sumHkC (D : D7) {s : D.what₂.LL →+* ℂ} (c : CjDat D s) (j : ℕ) : ℝ :=
  ∑ ρ, (InnerProductFormulaField.logHk (D.R.sigW j).1 (DV.aPlus D j (c.ga.symm ρ)) +
    InnerProductFormulaField.logHk (D.R.sigW j).2 (fun i => DV.aMinus D j (c.ga.symm ρ) ((D.R.sigW j).2 - 1 - i)))

section Statements

variable (D : D7) (L : SizeData₂ D) (Z : DivX D) (Y : Loc D Z) (Cj : CjFam D)

def kernelIdempotentPoints (j : ℕ) : Submodule D.what₂.LL (Y.MtjH j).V := (LinearMap.ker (D.what₂.eMt D.what₂.mu0 j)).comap (jC D Z Y j)

def eig (j : ℕ) (c : Y.TT → D.what₂.LL) : Submodule D.what₂.LL (Y.MtjH j).V :=
  ⨅ t, LinearMap.ker (Y.hk j t - c t • (1 : Module.End D.what₂.LL (Y.MtjH j).V))

def ThetaRationalityOverField : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m →
    (∀ x : D.what₂.MtL D.what₂.mu0 j, ∃ y, Z.jM j y = D.what₂.thetaP D.what₂.mu0 j (D.what₂.jMt D.what₂.mu0 j x)) ∧
    (∀ π, Submodule.span ℂ (Z.jM j '' (MjPart D Z Y j π : Set (Z.MjH j).V)) = DV.sum₃ Y.ix j (Y.ix.cOf π)) ∧
    goodPartRationalPoints D Z Y j ⊔ kernelIdempotentPoints D Z Y j = ⊤ ∧
    Submodule.span ℂ (jC D Z Y j '' (ZjL D Z Y j : Set (Y.MtjH j).V)) = Idx.Z0 D D.what₂.mu0 j

def EmbeddingAgreesOnSubfieldUpToConjugation : Prop :=
  ∀ s : D.what₂.LL →+* ℂ, SameK D s ∨ SameK D (ComplexEmbedding.conjugate s)

def ConjugateDatumSingularValueBound (C : ℝ) : Prop :=
  ∀ s (h : SameK D s) j, 1 ≤ j → j ≤ D.R.m → ∀ π, (Cj s h).isotC j π ≠ ⊥ →
    ∃ lam : ℝ, 0 < lam ∧
      (∀ x ∈ (Cj s h).isotC j π,
        (Cj s h).thC j (LinearMap.adjoint ((Cj s h).thC j) x) = (lam : ℂ) • x) ∧
      |Real.log lam - sumHkC D (Cj s h) j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * InnerProductFormulaField.Lp D L

def RealPlaceHeightSumNonneg : Prop := ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ InnerProductFormulaField.sumHkM D j

def ThetaKillsComplementOfGoodPart : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m →
    D.what₂.thetaP D.what₂.mu0 j ∘ₗ D.what₂.eMt D.what₂.mu0 j = D.what₂.thetaP D.what₂.mu0 j

def DoubleCosetAdjoint' : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (s : D.what₂.LL →+* ℂ) t,
    LinearMap.adjoint (mapS (Y.MtjH j) (Y.MtjH j) s (Y.hk j t)) = mapS (Y.MtjH j) (Y.MtjH j) s (Y.hk j (Y.hkAd t))

def GoodPartEigenspaceKernelSplitting : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ CC : Set (Y.TT → D.what₂.LL),
    ZjL D Z Y j = (⨆ c ∈ CC, goodPartRationalPoints D Z Y j ⊓ eig D Z Y j c) ∧
    KerL D Z Y j = (⨆ c ∈ CCᶜ, goodPartRationalPoints D Z Y j ⊓ eig D Z Y j c) ∧
    goodPartRationalPoints D Z Y j = ⨆ c, goodPartRationalPoints D Z Y j ⊓ eig D Z Y j c

def IsotypicPartsInternalDirectSum : Prop := Rows.IsotInternal D.what₂

def ThetaBijectiveReference : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m →
    Function.Bijective ((D.what₂.thetaP D.what₂.mu0 j).domRestrict (Idx.Z0 D D.what₂.mu0 j))

def admitted (C : ℝ) : Prop :=
  ThetaRationalityOverField D Z Y ∧ EmbeddingAgreesOnSubfieldUpToConjugation D ∧ ConjugateDatumSingularValueBound D L Cj C ∧ RealPlaceHeightSumNonneg D ∧ ThetaKillsComplementOfGoodPart D ∧ DoubleCosetAdjoint' D Z Y ∧ GoodPartEigenspaceKernelSplitting D Z Y ∧ IsotypicPartsInternalDirectSum D ∧ ThetaBijectiveReference D

def EmbeddingIsometryIdentity : Prop :=
  ∀ s (h : SameK D s) j, 1 ≤ j → j ≤ D.R.m →
    ∃ (uT : EuclideanSpace ℂ (Y.MtjH j).ι ≃ₗᵢ[ℂ] (Cj s h).MtC j)
      (uM : EuclideanSpace ℂ (Z.MjH j).ι ≃ₗᵢ[ℂ] (Cj s h).MjC j)
      (Rz : (Cj s h).MjC j ≃ₗᵢ[ℂ] (Cj s h).MjC j) (ka : ℂ),
      ‖ka‖ = 1 ∧
      (∀ π, ((Cj s h).isotC j π).map Rz.toLinearEquiv.toLinearMap = (Cj s h).isotC j π) ∧
      (∀ x, uM (thS D Z Y j s x) = ka • Rz ((Cj s h).thC j (uT x))) ∧
      (∀ π, (spS (Z.MjH j) s (MjPart D Z Y j π)).map uM.toLinearEquiv.toLinearMap = (Cj s h).isotC j π) ∧
      (spS (Y.MtjH j) s (goodPartRationalPoints D Z Y j)).map uT.toLinearEquiv.toLinearMap = LinearMap.range ((Cj s h).eC j) ∧
      (spS (Y.MtjH j) s (kernelIdempotentPoints D Z Y j)).map uT.toLinearEquiv.toLinearMap = LinearMap.ker ((Cj s h).eC j)

def ConjugationNormInvariance : Prop :=
  ∀ j (s : D.what₂.LL →+* ℂ),
    (∀ x, ‖ptS (Z.MjH j) (ComplexEmbedding.conjugate s) x‖ = ‖ptS (Z.MjH j) s x‖) ∧
    (∀ x, ‖ptS (Y.MtjH j) (ComplexEmbedding.conjugate s) x‖ = ‖ptS (Y.MtjH j) s x‖) ∧
    ∀ π c, IsLamS D Z Y j π s c → IsLamS D Z Y j π (ComplexEmbedding.conjugate s) c

def ThetaAdjointPositiveScalar (C : ℝ) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ →
    ∃ lam : ℝ, 0 < lam ∧ IsLamS D Z Y j π s lam ∧
      |Real.log lam - InnerProductFormulaField.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * InnerProductFormulaField.Lp D L

def LogEigenvalueDeviation (C : ℝ) : Prop :=
  LogLamDef D Z Y → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ → ∀ s : D.what₂.LL →+* ℂ,
    |Z.logLam j π s - InnerProductFormulaField.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * InnerProductFormulaField.Lp D L

def LogEigenvalueLowerBound (C : ℝ) : Prop :=
  LogLamDef D Z Y → ∀ j ∈ SizeData₂.lifts D, ∀ π, D.what₂.isot j π ≠ ⊥ → ∀ s : D.what₂.LL →+* ℂ,
    InnerProductFormulaField.sumHkP D j - C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ Z.logLam j π s

def LogEigenvaluesConjugateInvariant : Prop :=
  LogLamDef D Z Y → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ → ∀ s : D.what₂.LL →+* ℂ,
    Z.logLam j π (ComplexEmbedding.conjugate s) = Z.logLam j π s

def ConclusionE : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) j, 1 ≤ j → j ≤ D.R.m →
    (∀ x ∈ spS (Y.MtjH j) s (goodPartRationalPoints D Z Y j), ∀ y ∈ spS (Y.MtjH j) s (kernelIdempotentPoints D Z Y j), inner ℂ x y = 0) ∧
    spS (Y.MtjH j) s (ZjL D Z Y j) = (LinearMap.ker (thS D Z Y j s))ᗮ ⊓ spS (Y.MtjH j) s (goodPartRationalPoints D Z Y j) ∧
    spS (Y.MtjH j) s (ZjL D Z Y j) = LinearMap.range (LinearMap.adjoint (thS D Z Y j s ∘ₗ
      ((spS (Y.MtjH j) s (goodPartRationalPoints D Z Y j)).starProjection :
        EuclideanSpace ℂ (Y.MtjH j).ι →ₗ[ℂ] EuclideanSpace ℂ (Y.MtjH j).ι))) ∧
    (∀ π c, IsLamS D Z Y j π s c → ∀ x ∈ spS (Y.MtjH j) s (ZjPart D Z Y j π),
      LinearMap.adjoint (thS D Z Y j s) (thS D Z Y j s x) = (c : ℂ) • x) ∧
    ∀ π, Module.finrank ℂ (spS (Z.MjH j) s (MjPart D Z Y j π)) = Module.finrank ℂ (DV.sum₃ Y.ix j (Y.ix.cOf π)) ∧
      Module.finrank ℂ (spS (Y.MtjH j) s (ZjPart D Z Y j π)) = Module.finrank ℂ (DV.sum₃ Y.ix j (Y.ix.cOf π))

def Stmt (C K : ℝ) : Prop :=
  admitted D L Z Y Cj C → EmbeddingIsometryIdentity D Z Y Cj →
    ConjugationNormInvariance D Z Y ∧ ThetaAdjointPositiveScalar D L Z Y C ∧ LogEigenvalueDeviation D L Z Y C ∧ LogEigenvaluesConjugateInvariant D Z Y ∧ ConclusionE D Z Y ∧
      (0 ≤ C → 0 ≤ InnerProductFormulaField.Lp D L → InnerProductFormulaField.Lp D L ≤ K * L.La → LogEigenvalueLowerBound D L Z Y (C * K))

end Statements

section Rows

variable (D : D7) (Z : DivX D) (E : EigIdx D Z) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE) (A : AmbForm D S)

structure LocX where
  TX : Type
  hkX : TX → Module.End D.what₂.LL (A.MtH D.what₂.mu0).V
  hkX_comm : ∀ t t', Commute (hkX t) (hkX t')

  hkXAd : TX → TX

  cs : E.Pi → TX → D.what₂.LL

def KapConj : Prop := ∀ s : D.what₂.LL →+* ℂ, Z.kapR (ComplexEmbedding.conjugate s) = Z.kapR s

variable {D Z E S A} in

def LocX.eig (W : LocX D Z E S A) (c : W.TX → D.what₂.LL) : Submodule D.what₂.LL (A.MtH D.what₂.mu0).V :=
  ⨅ t, LinearMap.ker (W.hkX t - c t • (1 : Module.End D.what₂.LL (A.MtH D.what₂.mu0).V))

end Rows

section DecRows

variable (D : D7) (Z : DivX D) (E : EigIdx D Z) (A : AmbForm D (RowSide.sharp D)) (W : LocX D Z E (RowSide.sharp D) A)

end DecRows

section Family

variable {eps : ℝ}

def KudlaFamilyStatement (C K : ℝ) (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) (YF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Loc (Fm.D x i) (Fm.X x i))
    (CjF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, CjFam (Fm.D x i)) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Stmt (Fm.D x i) (Fm.L x i) (Fm.X x i) (YF x hx i) (CjF x hx i) C K

end Family

abbrev ObjClass : Type 1 := ∀ {D : D7} {Z : DivX D}, Loc D Z → CjFam D → Prop

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem frS_det (A : HLat K) (hA : ∀ v, IsUnit (A.X v).det) (s : K →+* ℂ) : IsUnit (frS A s).det := by
  unfold frS
  split_ifs with h
  · exact hA _
  · have : ((A.X (InfinitePlace.mk s)).map (starRingEnd ℂ)).det = starRingEnd ℂ (A.X (InfinitePlace.mk s)).det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (hA _).map (starRingEnd ℂ)


theorem ptS_inj (A : HLat K) (hA : ∀ v, IsUnit (A.X v).det) (s : K →+* ℂ) (x : A.V) (h : ptS A s x = 0) : x = 0 := by
  unfold ptS at h
  have h0 : Matrix.mulVec (frS A s)⁻¹ (fun i => s (A.b.repr x i)) = 0 := by
    have := congrArg (WithLp.equiv 2 (A.ι → ℂ)) h
    simpa using this
  have h2 : (frS A s) * (frS A s)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (frS_det A hA s)
  have h3 : (fun i => s (A.b.repr x i)) = 0 := by
    have := congrArg (Matrix.mulVec (frS A s)) h0
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have h4 : A.b.repr x = 0 := by
    ext i
    have := congrFun h3 i
    simpa using this
  simpa using h4

theorem spS_ne_bot (A : HLat K) (hA : ∀ v, IsUnit (A.X v).det) (s : K →+* ℂ) (U : Submodule K A.V) (hU : U ≠ ⊥) :
    spS A s U ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := U.ne_bot_iff.mp hU
  intro h
  have : ptS A s x ∈ spS A s U := Submodule.subset_span ⟨x, hx, rfl⟩
  rw [h, Submodule.mem_bot] at this
  exact hx0 (ptS_inj A hA s x this)

end

theorem sumHkC_eq (D : D7) {s : D.what₂.LL →+* ℂ} (c : CjDat D s) (j : ℕ) : sumHkC D c j = InnerProductFormulaField.sumHk D j := by
  unfold sumHkC InnerProductFormulaField.sumHk
  exact Equiv.sum_comp c.ga.symm (fun τ => InnerProductFormulaField.logHk (D.R.sigW j).1 (DV.aPlus D j τ) +
    InnerProductFormulaField.logHk (D.R.sigW j).2 (fun i => DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)))

section GlueD

variable (D : D7) (L : SizeData₂ D) (Z : DivX D) (Y : Loc D Z) (Cj : CjFam D)

theorem isotypicPart_ne_bot {D : D7} {Z : DivX D} (E : EigIdx D Z) (j : ℕ) (π : D.what₂.FT) (h : D.what₂.isot j π ≠ ⊥) :
    DV.sum₃ E j (E.cOf π) ≠ ⊥ := by
  intro h0
  apply h
  have : D.what₂.isot j π ≤ DV.sum₃ E j (E.cOf π) :=
    le_iSup₂ (f := fun (π' : D.what₂.FT) (_ : E.cOf π' = E.cOf π) => D.what₂.isot j π') π rfl
  exact le_bot_iff.mp (h0 ▸ this)


theorem MjPart_ne_bot (hR : ThetaRationalityOverField D Z Y) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (π : D.what₂.FT)
    (h : D.what₂.isot j π ≠ ⊥) : MjPart D Z Y j π ≠ ⊥ := by
  intro h0
  apply isotypicPart_ne_bot Y.ix j π h
  rw [← ((hR j h1 h2).2.1 π), h0]
  simp


theorem lamS_of_ident (C : ℝ) (hR : ThetaRationalityOverField D Z Y) (hA : ConjugateDatumSingularValueBound D L Cj C) (hI : EmbeddingIsometryIdentity D Z Y Cj)
    (s : D.what₂.LL →+* ℂ) (h : SameK D s) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (π : D.what₂.FT)
    (hne : D.what₂.isot j π ≠ ⊥) :
    ∃ lam : ℝ, 0 < lam ∧ IsLamS D Z Y j π s lam ∧
      |Real.log lam - InnerProductFormulaField.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * InnerProductFormulaField.Lp D L := by
  obtain ⟨uT, uM, Rz, ka, hka, hRz, hth, hpart, -, -⟩ := hI s h j h1 h2
  have hC : (Cj s h).isotC j π ≠ ⊥ := by
    rw [← hpart π]
    intro h0
    have := spS_ne_bot (Z.MjH j) (Z.MjH_good j).1 s _ (MjPart_ne_bot D Z Y hR j h1 h2 π hne)
    apply this
    rw [Submodule.map_eq_bot_iff] at h0
    exact h0
  obtain ⟨lam, hpos, heig, hsz⟩ := hA s h j h1 h2 π hC
  refine ⟨lam, hpos, ?_, by rwa [sumHkC_eq] at hsz⟩
  intro y hy
  set T := thS D Z Y j s with hT
  set T' := (Cj s h).thC j with hT'
  have hy' : uM y ∈ (Cj s h).isotC j π := by
    rw [← hpart π]; exact ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ : ∃ z ∈ (Cj s h).isotC j π, Rz z = uM y := by
    have : uM y ∈ ((Cj s h).isotC j π).map Rz.toLinearEquiv.toLinearMap := by rw [hRz π]; exact hy'
    obtain ⟨z, hz, e⟩ := this
    exact ⟨z, hz, e⟩
  have key : uT (LinearMap.adjoint T y) = (starRingEnd ℂ ka) • LinearMap.adjoint T' z := by
    refine ext_inner_right ℂ fun w => ?_
    have e1 : inner ℂ (uT (LinearMap.adjoint T y)) w = inner ℂ (LinearMap.adjoint T y) (uT.symm w) := by
      rw [← uT.inner_map_map, uT.apply_symm_apply]
    rw [e1, LinearMap.adjoint_inner_left, ← uM.inner_map_map, hth, uT.apply_symm_apply, ← hzy, inner_smul_right,
      Rz.inner_map_map, inner_smul_left, LinearMap.adjoint_inner_left]
    simp
  apply uM.injective
  rw [hth, key, map_smul, map_smul, heig z hz, map_smul, hzy, map_smul, smul_smul, smul_smul]
  congr 1
  have : ka * (starRingEnd ℂ) ka = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hka]; simp
  rw [this, one_mul]

theorem conj_conj' (s : D.what₂.LL →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate s) = s := by
  ext x; simp

theorem stmtD (C : ℝ) (hR : ThetaRationalityOverField D Z Y) (hK : EmbeddingAgreesOnSubfieldUpToConjugation D) (hA : ConjugateDatumSingularValueBound D L Cj C) (hI : EmbeddingIsometryIdentity D Z Y Cj)
    (hc : ConjugationNormInvariance D Z Y) : ThetaAdjointPositiveScalar D L Z Y C := by
  intro s j h1 h2 π hne
  rcases hK s with h | h
  · exact lamS_of_ident D L Z Y Cj C hR hA hI s h j h1 h2 π hne
  · obtain ⟨lam, hp, hl, hs⟩ := lamS_of_ident D L Z Y Cj C hR hA hI _ h j h1 h2 π hne
    refine ⟨lam, hp, ?_, hs⟩
    have := (hc j (ComplexEmbedding.conjugate s)).2.2 π lam hl
    rwa [conj_conj'] at this




end GlueD

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cj {ι : Type} (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => starRingEnd ℂ (v.ofLp i))

theorem cj_cj {ι : Type} (v : EuclideanSpace ℂ ι) : cj (cj v) = v := by
  ext i; simp [cj]

theorem cj_add {ι : Type} (v w : EuclideanSpace ℂ ι) : cj (v + w) = cj v + cj w := by
  ext i; simp [cj]

theorem cj_smul {ι : Type} (a : ℂ) (v : EuclideanSpace ℂ ι) : cj (a • v) = starRingEnd ℂ a • cj v := by
  ext i; simp [cj]

theorem cj_inner {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : inner ℂ (cj v) (cj w) = starRingEnd ℂ (inner ℂ v w) := by
  simp [cj, PiLp.inner_apply, map_sum]

theorem map_conj_inv {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : IsUnit M.det) :
    (M.map (starRingEnd ℂ))⁻¹ = (M⁻¹).map (starRingEnd ℂ) := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem frS_conj (A : HLat K) (s : K →+* ℂ) (hs : ComplexEmbedding.conjugate s ≠ s) :
    frS A (ComplexEmbedding.conjugate s) = (frS A s).map (starRingEnd ℂ) := by
  unfold frS
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq s with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact fun e => hs e.symm)]
  · rw [if_pos h, if_neg (by rw [h]; exact hs)]
    ext i j; simp

theorem toEuc_cj {ι κ : Type} [Fintype ι] [DecidableEq ι] (M : Matrix κ ι ℂ) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (M.map (starRingEnd ℂ)) (cj v) = cj (Matrix.toEuclideanLin M v) := by
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply]
  unfold cj
  congr 1
  funext i
  exact (RingHom.map_mulVec (starRingEnd ℂ) M v.ofLp i).symm

theorem ptS_conj (A : HLat K) (hA : ∀ v, IsUnit (A.X v).det) (s : K →+* ℂ) (hs : ComplexEmbedding.conjugate s ≠ s) (x : A.V) :
    ptS A (ComplexEmbedding.conjugate s) x = cj (ptS A s x) := by
  unfold ptS cj
  rw [frS_conj A s hs, map_conj_inv _ (frS_det A hA s)]
  show WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  funext i
  exact (RingHom.map_mulVec (starRingEnd ℂ) (frS A s)⁻¹ (fun i => s (A.b.repr x i)) i).symm

theorem mapS_conj (A B : HLat K) (hB : ∀ v, IsUnit (B.X v).det) (s : K →+* ℂ)
    (hs : ComplexEmbedding.conjugate s ≠ s) (φ : A.V →ₗ[K] B.V) (v : EuclideanSpace ℂ A.ι) :
    mapS A B (ComplexEmbedding.conjugate s) φ (cj v) = cj (mapS A B s φ v) := by
  unfold mapS
  rw [← toEuc_cj, frS_conj A s hs, frS_conj B s hs, map_conj_inv _ (frS_det B hB s), Matrix.map_mul, Matrix.map_mul]
  congr 3

theorem adj_conj (A B : HLat K) (hB : ∀ v, IsUnit (B.X v).det) (s : K →+* ℂ)
    (hs : ComplexEmbedding.conjugate s ≠ s) (φ : A.V →ₗ[K] B.V) (y : EuclideanSpace ℂ B.ι) :
    LinearMap.adjoint (mapS A B (ComplexEmbedding.conjugate s) φ) (cj y) = cj (LinearMap.adjoint (mapS A B s φ) y) := by
  refine ext_inner_right ℂ fun w => ?_
  rw [LinearMap.adjoint_inner_left]
  conv_lhs => rw [← cj_cj w]
  conv_rhs => rw [← cj_cj w]
  rw [mapS_conj A B hB s hs, cj_inner, cj_inner, LinearMap.adjoint_inner_left]



end

theorem conj_ne (D : D7) (s : D.what₂.LL →+* ℂ) : ComplexEmbedding.conjugate s ≠ s := by
  intro h
  have hr : ComplexEmbedding.IsReal s := h
  have h1 : (InfinitePlace.mk s).IsReal := ⟨s, hr, rfl⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk s))) h1


theorem nV_le (R : Ranks) : R.nV ≤ R.N R.m := by
  unfold Ranks.nV Ranks.N Ranks.r
  have h1 : R.t ≤ R.m * R.t := Nat.le_mul_of_pos_left _ (by have := R.two_le_m; omega)
  have h2 : R.m * (R.t + 1) = R.m * R.t + R.m := by ring
  have := R.two_le_m
  omega

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]


end


end Formalism.MainNotions.PGAL

end
