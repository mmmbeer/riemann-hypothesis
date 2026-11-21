import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

open MeasureTheory Polynomial
open scoped ENNReal

namespace PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.Tf.Loc

noncomputable section

section Helpers

variable {n : ℕ} {k E : Type*} [Field k] [Field E] [Algebra k E]

def starσ (σ : E ≃ₐ[k] E) (M : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  (M.map σ).transpose

variable [ValuativeRel E]

def EntriesIn (ϖ : E) (m : ℕ) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, ValuativeRel.valuation E (M i j) ≤ ValuativeRel.valuation E ϖ ^ m

def IsUnitLift (σ : E ≃ₐ[k] E) (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E) : Prop :=
  c ∈ unitGL (n := Fin n) E ∧
    (∃ p : E[X], (∀ i, ValuativeRel.valuation E (p.coeff i) ≤ 1) ∧
      (c : Matrix (Fin n) (Fin n) E) = aeval ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p) ∧
    c * theta1 σ c = (γ : GL (Fin n) E)

end Helpers

def B1 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ (1 : GL (Fin n) E))),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E)
          (μc : Measure (twCent (theta1 σ) c))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          IsUnitLift σ γ c → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (theta1 σ) c => (x : GL (Fin n) E)) μc =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))) =>
              ((t : unitaryGL σ (1 : GL (Fin n) E)) : GL (Fin n) E)) μγ →
          twOrbIntegralC (theta1 σ) μE c μc (unitFnC E) = orbIntegralC μU γ μγ (unitFnUC σ 1)) ∧
      (∀ (δ : GL (Fin n) E) (μδ : Measure (twCent (theta1 σ) δ)),
          ((normU σ 1 δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          (¬ ∃ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E),
              IsUnitLift σ γ c ∧ TwConjugate (theta1 σ) c δ) →
          twOrbIntegralC (theta1 σ) μE δ μδ (unitFnC E) = 0) ∧
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          (∃ i, 1 < ValuativeRel.valuation E
              (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.coeff i)) →
          orbIntegralC μU γ μγ (unitFnUC σ 1) = 0)

section Split

variable {F : Type*} [Field F]

def thetaSplit {n : ℕ} : Monoid.End (GL (Fin n) F × GL (Fin n) F) where
  toFun p := (invTransposeGL p.2, invTransposeGL p.1)
  map_one' := Prod.ext (map_one _) (map_one _)
  map_mul' _ _ := Prod.ext (map_mul _ _ _) (map_mul _ _ _)

variable {a b : ℕ}

def blockDiag (A : GL (Fin a) F) (D : GL (Fin b) F) : GL (Fin a ⊕ Fin b) F :=
  ⟨Matrix.fromBlocks (A : Matrix (Fin a) (Fin a) F) 0 0 (D : Matrix (Fin b) (Fin b) F),
    Matrix.fromBlocks ((A⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
      ((D⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F),
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩

def unipN (X : Matrix (Fin a) (Fin b) F) : GL (Fin a ⊕ Fin b) F :=
  ⟨Matrix.fromBlocks 1 X 0 1, Matrix.fromBlocks 1 (-X) 0 1,
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩

def adN (A : GL (Fin a) F) (D : GL (Fin b) F) :
    Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F where
  toFun X := (A : Matrix (Fin a) (Fin a) F) * X * ((D⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

def adNbar (A : GL (Fin a) F) (D : GL (Fin b) F) :
    Matrix (Fin b) (Fin a) F →ₗ[F] Matrix (Fin b) (Fin a) F where
  toFun Y := (D : Matrix (Fin b) (Fin b) F) * Y * ((A⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

def discrGM (A : GL (Fin a) F) (D : GL (Fin b) F) : F :=
  LinearMap.det (LinearMap.id - adN A D) * LinearMap.det (LinearMap.id - adNbar A D)

def intSet (F : Type*) [Field F] [ValuativeRel F] : Set F := {y | ValuativeRel.valuation F y ≤ 1}

variable [ValuativeRel F] [MeasurableSpace F]

def modF (μF : Measure F) (x : F) : ℝ :=
  (μF ((fun y => x * y) '' intSet F) / μF (intSet F)).toReal

variable [TopologicalSpace F] [MeasurableSpace (GL (Fin a ⊕ Fin b) F)]

def constTerm (μF : Measure F) (μG : Measure (GL (Fin a ⊕ Fin b) F))
    (μN : Measure (Fin a → Fin b → F)) (f : GL (Fin a ⊕ Fin b) F → ℂ)
    (p : GL (Fin a) F × GL (Fin b) F) : ℂ :=
  (((modF μF ((p.1 : Matrix (Fin a) (Fin a) F).det)) ^ ((b : ℝ) / 2) *
      (modF μF ((p.2 : Matrix (Fin b) (Fin b) F).det)) ^ (-((a : ℝ) / 2)) : ℝ) : ℂ) *
    ∫ k, Set.indicator ((unitGL (n := Fin a ⊕ Fin b) F : Subgroup _) : Set (GL (Fin a ⊕ Fin b) F))
      (fun k => ∫ X, f (k⁻¹ * blockDiag p.1 p.2 * unipN (Matrix.of X) * k) ∂μN) k ∂μG

end Split

def B3 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (μF : Measure F), μF.IsAddHaarMeasure →
    (∀ (n : ℕ) [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
        (μ : Measure (GL (Fin n) F)), μ.IsHaarMeasure →
      ∀ (f₁ f₂ : GL (Fin n) F → ℂ), IsLocallyConstant f₁ → HasCompactSupport f₁ →
        IsLocallyConstant f₂ → HasCompactSupport f₂ →
      ∀ (δ : GL (Fin n) F × GL (Fin n) F) (μδ : Measure (twCent thetaSplit δ))
        (μγ : Measure (Subgroup.centralizer ({δ.1 * invTransposeGL δ.2} : Set (GL (Fin n) F)))),
        ((δ.1 * invTransposeGL δ.2 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).charpoly.Separable →
        μγ.IsHaarMeasure →
        Measure.map (fun x : twCent thetaSplit δ => (x : GL (Fin n) F × GL (Fin n) F).1) μδ =
          Measure.map (fun t : Subgroup.centralizer ({δ.1 * invTransposeGL δ.2} : Set (GL (Fin n) F)) =>
            (t : GL (Fin n) F)) μγ →
        twOrbIntegralC thetaSplit (μ.prod μ) δ μδ (fun p => f₁ p.1 * f₂ p.2) =
          orbIntegralC μ (δ.1 * invTransposeGL δ.2) μγ
            (fun y => ∫ h, f₁ h * f₂ (invTransposeGL (h⁻¹ * y)) ∂μ)) ∧
    (∀ (a b : ℕ) [MeasurableSpace (GL (Fin a ⊕ Fin b) F)] [BorelSpace (GL (Fin a ⊕ Fin b) F)]
        [MeasurableSpace (GL (Fin a) F)] [BorelSpace (GL (Fin a) F)]
        [MeasurableSpace (GL (Fin b) F)] [BorelSpace (GL (Fin b) F)]
        (μG : Measure (GL (Fin a ⊕ Fin b) F)) (μa : Measure (GL (Fin a) F))
        (μb : Measure (GL (Fin b) F)) (μN : Measure (Fin a → Fin b → F)),
        μG.IsHaarMeasure → μa.IsHaarMeasure → μb.IsHaarMeasure → μN.IsAddHaarMeasure →
        μG (unitGL (n := Fin a ⊕ Fin b) F : Set (GL (Fin a ⊕ Fin b) F)) = 1 →
        μa (unitGL (n := Fin a) F : Set (GL (Fin a) F)) = 1 →
        μb (unitGL (n := Fin b) F : Set (GL (Fin b) F)) = 1 →
        μN {X | ∀ i j, ValuativeRel.valuation F (X i j) ≤ 1} = 1 →
      ∀ (f : GL (Fin a ⊕ Fin b) F → ℂ), IsLocallyConstant f → HasCompactSupport f →
      ∀ (A : GL (Fin a) F) (D : GL (Fin b) F)
        (μγG : Measure (Subgroup.centralizer ({blockDiag A D} : Set (GL (Fin a ⊕ Fin b) F))))
        (μγM : Measure (Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)))),
        ((blockDiag A D : GL (Fin a ⊕ Fin b) F) :
          Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F).charpoly.Separable →
        μγM.IsHaarMeasure →
        Measure.map (fun t : Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)) =>
            blockDiag (t : GL (Fin a) F × GL (Fin b) F).1 (t : GL (Fin a) F × GL (Fin b) F).2) μγM =
          Measure.map (fun t : Subgroup.centralizer ({blockDiag A D} : Set (GL (Fin a ⊕ Fin b) F)) =>
            (t : GL (Fin a ⊕ Fin b) F)) μγG →
        orbIntegralC μG (blockDiag A D) μγG f =
          (((modF μF (discrGM A D)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            orbIntegralC (μa.prod μb) (A, D) μγM (constTerm μF μG μN f))

def torusO (F : Type*) [Field F] [ValuativeRel F] {m : ℕ} : Set (GL (Fin m) F) :=
  {t | t ∈ unitGL (n := Fin m) F ∧ ∀ i j : Fin m, i ≠ j → (t : Matrix (Fin m) (Fin m) F) i j = 0}

end

end PositivityTheory.Rg.Bc.ArchbcB.B
