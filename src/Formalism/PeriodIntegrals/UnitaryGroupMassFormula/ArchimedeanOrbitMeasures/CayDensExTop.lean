import Mathlib

section
open Matrix LinearMap Module

noncomputable section

namespace HcS.E

def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)

end HcS.E
end
end

section
open Module

noncomputable section

namespace HcS.HermitianLatticesTheory

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm

def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  HcS.E.hdual h L

def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L

end Defs

end HcS.HermitianLatticesTheory
end
end

section
noncomputable section

open Matrix TensorProduct

namespace HcS.UG

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  simp [cT, Matrix.map_one]

def UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def Upq (p q : ℕ) : Subgroup (GL (Fin p ⊕ Fin q) ℂ) := UJ (starRingEnd ℂ) (Jpq p q)

end Points

section Split

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

end Split

section Abstract

variable {G : Type} [Group G]

end Abstract

section Tj

variable {L : Type} [Field L]

end Tj

section Coeff

variable (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]

end Coeff

section More

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

end More

open NumberField IsDedekindDomain

end HcS.UG
end
end

section
open NumberField

noncomputable section

namespace HcS.HermitianLatticesTheory

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

end HcS.HermitianLatticesTheory

namespace HcS.HermitianLatticesTheory

open NumberField

end HcS.HermitianLatticesTheory
end
end

section
noncomputable section

namespace HcS.BasicNotions

open NumberField IsDedekindDomain
open scoped TensorProduct

structure CMData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] : Prop where
  cmUnram : HcS.HermitianLatticesTheory.IsCMUnram E
  totReal : NumberField.IsTotallyReal F
  deg2 : Module.finrank F E = 2
  fixed : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range

def CMData.sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : E →ₐ[F] E :=
  { starRingEnd E with
    commutes' := fun a => (hc.fixed (algebraMap F E a)).2 ⟨a, rfl⟩ }

structure HSpace (E : Type) [Field E] [NumberField E] [StarRing E] where
  V : Type
  [acg : AddCommGroup V]
  [modE : Module E V]
  [modO : Module (𝓞 E) V]
  [tower : IsScalarTower (𝓞 E) E V]
  [fd : FiniteDimensional E V]

  hT : V →ₗ⋆[E] V →ₗ[E] E
  herm : hT.IsSymm
  nondeg : hT.Nondegenerate
  rank : ℕ
  rank_eq : Module.finrank E V = rank

  frame : Module.Basis (Fin rank) E V

  sig : (E →+* ℂ) → ℕ × ℕ

  L0 : Submodule (𝓞 E) V
  standardTuple_isLattice : Submodule.IsLattice E L0
  baseLattice_isUnimodular : HcS.HermitianLatticesTheory.IsUnimodular hT L0

attribute [instance] HSpace.acg HSpace.modE HSpace.modO HSpace.tower HSpace.fd

namespace HSpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def gram (S : HSpace E) : Matrix (Fin S.rank) (Fin S.rank) E :=
  fun i j => S.hT (S.frame i) (S.frame j)

end HSpace

namespace Spaces

end Spaces

end HcS.BasicNotions

end
end

section
noncomputable section

namespace HcS.BasicNotions

open MeasureTheory Filter Topology Matrix

def UpqT (P Q : ℕ) : Type := HcS.UG.Upq P Q

instance (P Q : ℕ) : Group (UpqT P Q) := inferInstanceAs (Group (HcS.UG.Upq P Q))
instance (P Q : ℕ) : TopologicalSpace (UpqT P Q) :=
  inferInstanceAs (TopologicalSpace (HcS.UG.Upq P Q))
instance (P Q : ℕ) : MeasurableSpace (UpqT P Q) := borel (UpqT P Q)

def UpqT.mat {P Q : ℕ} (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  let g' : HcS.UG.Upq P Q := g; ((g'.1 : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)

def lieU (P Q : ℕ) : Submodule ℝ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) where
  carrier := {X | Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * HcS.UG.Jpq P Q + Yᴴ * HcS.UG.Jpq P Q + (HcS.UG.Jpq P Q * X + HcS.UG.Jpq P Q * Y)
        = (Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X) + (Yᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * Y) := by
          abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX,
      smul_zero]

instance (P Q : ℕ) : MeasurableSpace (lieU P Q) := borel (lieU P Q)

def entries {P Q : ℕ} (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ := fun ij => Z ij.1 ij.2

def IsOmegaLeb {P Q : ℕ} (lam : Measure (lieU P Q)) : Prop :=
  lam.IsAddHaarMeasure ∧
    ((lam.prod lam).map (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) = volume

def ballU (P Q : ℕ) (r : ℝ) : Set (lieU P Q) :=
  {X | ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r}

def OmegaDensity {P Q : ℕ} (μ : Measure (UpqT P Q)) (c : ENNReal) : Prop :=
  ∃ lam : Measure (lieU P Q), IsOmegaLeb lam ∧
    Tendsto (fun r : ℝ => μ {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c)

structure CDHaar where
  cd : ∀ P Q : ℕ, Measure (UpqT P Q)
  haar : ∀ P Q, (cd P Q).IsHaarMeasure
  prob : ∀ N, IsProbabilityMeasure (cd N 0)
  trick : ∀ P Q, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity (cd P Q) c ∧ OmegaDensity (cd (P + Q) 0) c

end HcS.BasicNotions
end
end

section
noncomputable section

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

variable (R : Type) [CommRing R] [Algebra F R]

def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)

def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  HcS.UG.UJ (sigR R σ) (JR R J)

end Alg

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)

scoped instance measTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    MeasurableSpace (R ⊗[F] E) := borel (R ⊗[F] E)

def HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Type := HR R σ J

variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

instance : Group (HA R σ J) := inferInstanceAs (Group (HR R σ J))
instance [TopologicalSpace R] : TopologicalSpace (HA R σ J) :=
  inferInstanceAs (TopologicalSpace (HR R σ J))
instance [TopologicalSpace R] : MeasurableSpace (HA R σ J) := borel (HA R σ J)

def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1

end Top

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev AF := AdeleRing (𝓞 F) F

abbrev Ainf := InfiniteAdeleRing F

abbrev Af := FiniteAdeleRing (𝓞 F) F

end Adeles

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section AdeleAnalysis

variable {F : Type} [Field F] [NumberField F]

scoped instance measAF : MeasurableSpace (AF F) := borel _
scoped instance measAinf : MeasurableSpace (Ainf F) := borel _
scoped instance measAf : MeasurableSpace (Af F) := borel _

variable (F)

def IsCharAF (ψ : AddChar (AF F) ℂ) : Prop :=
  Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ a : F, ψ (algebraMap F (AF F) a) = 1) ∧ ∃ x, ψ x ≠ 1

end AdeleAnalysis

section Tuples

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Tuples

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section More

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end More

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section HMeasures

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end HMeasures

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
end
end

section
noncomputable section

namespace HcS.MainNotions.StandardLattice

open NumberField HcS.BasicNotions Finset
open scoped ENNReal

section SW

open HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end SW

section Vol

open HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end Vol

section DS

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

end DS

section Fam

end Fam

end HcS.MainNotions.StandardLattice
end
end

section
noncomputable section

namespace HcS.L2.Fam.SG.Tau

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Loc

variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def LieU : AddSubgroup (Matrix (Fin M) (Fin M) (R ⊗[F] E)) where
  carrier := {X | HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0}
  zero_mem' := by
    show HcS.UG.cT (sigR R σ) 0 * JR R J + JR R J * 0 = 0
    simp [HcS.UG.cT]
  add_mem' := by
    intro X Y hX hY
    have e : HcS.UG.cT (sigR R σ) (X + Y) = HcS.UG.cT (sigR R σ) X + HcS.UG.cT (sigR R σ) Y := by
      ext i j; simp [HcS.UG.cT]
    show HcS.UG.cT (sigR R σ) (X + Y) * JR R J + JR R J * (X + Y) = 0
    have h1 : HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0 := hX
    have h2 : HcS.UG.cT (sigR R σ) Y * JR R J + JR R J * Y = 0 := hY
    rw [e, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]
  neg_mem' := by
    intro X hX
    have e : HcS.UG.cT (sigR R σ) (-X) = -HcS.UG.cT (sigR R σ) X := by
      ext i j; simp [HcS.UG.cT]
    show HcS.UG.cT (sigR R σ) (-X) * JR R J + JR R J * (-X) = 0
    have h1 : HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0 := hX
    rw [e, neg_mul, mul_neg, ← neg_add, h1, neg_zero]

instance measLie [TopologicalSpace R] : MeasurableSpace (LieU R σ J) := borel _

variable {J} {J' : Matrix (Fin M) (Fin M) E} (g : GL (Fin M) (R ⊗[F] E))

variable [TopologicalSpace R] [IsTopologicalRing R]

end Loc

end Defs

section Gaps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)

end Gaps

end HcS.L2.Fam.SG.Tau

end
end

section
noncomputable section

namespace HcS.L2.Fam.SG.Tau.InfCmpCut

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau Matrix
  MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal

end HcS.L2.Fam.SG.Tau.InfCmpCut
end
end

section
noncomputable section

namespace HcInf

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (emb : T → (E →+* ℂ)) (cd : CDHaar)

def CdFin : Prop := ∀ P Q : ℕ, SigmaFinite (cd.cd P Q)

def HaarUnique : Prop :=
  ∀ (W : HSpace E) (P Q : ℕ) (Φ : HA (Ainf F) hc.sig W.gram ≃ᵐ (T → UpqT P Q)),
    (∀ b c, Φ (b * c) = Φ b * Φ c) → Continuous Φ → Continuous Φ.symm →
    ∀ μ : Measure (HA (Ainf F) hc.sig W.gram), μ.IsHaarMeasure →
      ∃ k : ℝ≥0∞, μ.map Φ = k • Measure.pi (fun _ : T => cd.cd P Q)

variable {F E hc T emb cd}

end HcInf
end
end

section
noncomputable section

namespace HcInf

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.StandardLattice HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes HcS.L2.Fam.SG.Tau
  HcS.L2.Fam.SG.Tau.InfCmpCut Matrix MeasureTheory Filter Topology
open scoped TensorProduct ENNReal NNReal

section Upq

variable (P Q : ℕ)

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem cT_eq (X : Mat) : HcS.UG.cT (starRingEnd ℂ) X = Xᴴ := by
  ext i j
  simp [HcS.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]

theorem Jpq_mul_self : HcS.UG.Jpq P Q * HcS.UG.Jpq P Q = 1 := by
  simp [HcS.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jpq_conjTranspose : (HcS.UG.Jpq P Q)ᴴ = HcS.UG.Jpq P Q := by
  simp [HcS.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem mem_Upq_iff (g : GL (Fin P ⊕ Fin Q) ℂ) :
    g ∈ HcS.UG.Upq P Q ↔ (g : Mat)ᴴ * HcS.UG.Jpq P Q * (g : Mat) = HcS.UG.Jpq P Q := by
  unfold HcS.UG.Upq
  rw [← cT_eq]
  rfl

def toS (g : UpqT P Q) : HcS.UG.Upq P Q := g

theorem mat_eq (g : UpqT P Q) : UpqT.mat g = ((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ) : Mat) := rfl

theorem mat_inv (g : UpqT P Q) :
    (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) =
      HcS.UG.Jpq P Q * (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q := by
  have hmem : (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q * UpqT.mat g = HcS.UG.Jpq P Q := by
    rw [mat_eq]
    exact (mem_Upq_iff P Q _).mp (toS P Q g).2
  have hAB : UpqT.mat g * (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) = 1 := by
    rw [mat_eq, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat)
      = (HcS.UG.Jpq P Q * ((UpqT.mat g)ᴴ * HcS.UG.Jpq P Q * UpqT.mat g)) *
          (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) := by
        rw [hmem, Jpq_mul_self, Matrix.one_mul]
    _ = HcS.UG.Jpq P Q * (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q *
          (UpqT.mat g * (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAB, Matrix.mul_one]

theorem isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  have hv : IsInducing (fun g : UpqT P Q => ((toS P Q g : HcS.UG.Upq P Q) : GL (Fin P ⊕ Fin Q) ℂ)) := by
    rw [isInducing_iff]
    ext s
    rw [isOpen_induced_iff]
    show HcS.BasicNotions.instTopologicalSpaceUpqT._aux_1 P Q s ↔ _
    unfold HcS.BasicNotions.instTopologicalSpaceUpqT._aux_1
    rfl
  have he : IsInducing ((Units.embedProduct Mat) ∘
      (fun g : UpqT P Q => ((toS P Q g : HcS.UG.Upq P Q) : GL (Fin P ⊕ Fin Q) ℂ))) :=
    Units.isEmbedding_embedProduct.isInducing.comp hv
  have hcomp : (Units.embedProduct Mat) ∘
      (fun g : UpqT P Q => ((toS P Q g : HcS.UG.Upq P Q) : GL (Fin P ⊕ Fin Q) ℂ)) =
      (fun X : Mat => (X, MulOpposite.op (HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q))) ∘ UpqT.mat := by
    funext x
    exact Prod.ext rfl (congrArg MulOpposite.op (mat_inv P Q x))
  rw [hcomp] at he
  refine IsInducing.of_comp ?_ ?_ he
  · exact Units.continuous_val.comp hv.continuous
  · exact continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))

theorem range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {X : Mat | Xᴴ * HcS.UG.Jpq P Q * X = HcS.UG.Jpq P Q} := by
  ext X
  constructor
  · rintro ⟨g, rfl⟩
    show (UpqT.mat g)ᴴ * HcS.UG.Jpq P Q * UpqT.mat g = HcS.UG.Jpq P Q
    rw [mat_eq]
    exact (mem_Upq_iff P Q _).mp (toS P Q g).2
  · intro hX
    have hX' : Xᴴ * HcS.UG.Jpq P Q * X = HcS.UG.Jpq P Q := hX
    have hl : (HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q) * X = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX', Jpq_mul_self]
    have hr : X * (HcS.UG.Jpq P Q * Xᴴ * HcS.UG.Jpq P Q) = 1 := mul_eq_one_comm.mp hl
    let u : GL (Fin P ⊕ Fin Q) ℂ := ⟨X, _, hr, hl⟩
    have hu : u ∈ HcS.UG.Upq P Q := (mem_Upq_iff P Q u).mpr hX'
    exact ⟨(⟨u, hu⟩ : HcS.UG.Upq P Q), rfl⟩

theorem isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat P Q, fun a b h => ?_⟩, ?_⟩
  · exact Subtype.ext (Units.ext h)
  · rw [range_mat]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const

instance : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (HcS.UG.Upq P Q))

instance : BorelSpace (UpqT P Q) := ⟨rfl⟩

instance : LocallyCompactSpace (UpqT P Q) := by
  haveI : LocallyCompactSpace Mat :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isClosedEmbedding_mat P Q).locallyCompactSpace

instance : SecondCountableTopology (UpqT P Q) := by
  haveI : SecondCountableTopology Mat :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isInducing_mat P Q).secondCountableTopology

instance : SigmaCompactSpace (UpqT P Q) := inferInstance

end Upq


variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (T : Type) [Fintype T] (cd : CDHaar)


end HcInf
end
end
