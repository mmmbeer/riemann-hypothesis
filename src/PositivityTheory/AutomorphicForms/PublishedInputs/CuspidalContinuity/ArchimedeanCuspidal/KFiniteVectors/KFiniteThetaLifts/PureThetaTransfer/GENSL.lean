import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.AdmM
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import GroundTheory.HeightsAndTheta.Theta.WeilBox

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic ComplexConjugate
open scoped ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

section C

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def bM (M : Matrix (Fin 2) (Fin 2) F) (x y : Fin 2 → F) : F := x ⬝ᵥ M *ᵥ y

def nM (M : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F) : F := bM M x x / 2

def muM (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) : Measure (Fin 2 → F) :=
  ENNReal.ofReal ((modulus M.det : ℝ) ^ (1 / 2 : ℝ)) • GroundTheory.Heights₂.Theta.selfDualPi (ι := Fin 2) χ

def FTb (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (Φ : (Fin 2 → F) → ℂ) (y : Fin 2 → F) : ℂ :=
  ∫ x, Φ x * (χ (bM M y x) : ℂ) ∂muM χ M

open Classical in

def rWC (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ) (a b c d : F)
    (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F) : ℂ :=
  if c = 0 then (χ (a * b * nM M z) : ℂ) * eta a * ((modulus a : ℝ) : ℂ) * Φ (a • z)
  else lam * eta (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
    ∫ u, (χ ((a * nM M z + d * nM M u - bM M z u) / c) : ℂ) * Φ u ∂muM χ M

def rWCm (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ) (g : Matrix (Fin 2) (Fin 2) F) :
    ((Fin 2 → F) → ℂ) → (Fin 2 → F) → ℂ :=
  rWC χ M lam eta (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def SBC : Set ((Fin 2 → F) → ℂ) := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}

end C

def ForF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F], Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F], P F

def TRANS : Prop := ForF fun F _ _ _ _ _ _ => ∀ (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] [BorelSpace E] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ)
  (M : Matrix (Fin 2) (Fin 2) F) (j : (Fin 2 → F) ≃ₗ[F] E), Continuous j → Continuous j.symm →
  (∀ x, Algebra.norm F (j x) = nM M x) → (∀ x y, Algebra.trace F E (σ (j x) * j y) = bM M x y) →
  Measure.map j (muM χ M) = μE → ∀ (a b c d : F) (Φ : E → ℂ) (z : Fin 2 → F),
    rWC χ M lam (GL2LocalData.nsg E) a b c d (fun x => Φ (j x)) z = GL2LocalData.rW χ σ μE lam a b c d Φ (j z)

def REPC : Prop := ForF fun F _ _ _ _ _ _ => ∀ (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] [BorelSpace E] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ)
  (M : Matrix (Fin 2) (Fin 2) F) (j : (Fin 2 → F) ≃ₗ[F] E), Continuous j → Continuous j.symm →
  (∀ x, Algebra.norm F (j x) = nM M x) → (∀ x y, Algebra.trace F E (σ (j x) * j y) = bM M x y) →
  Measure.map j (muM χ M) = μE →
  (∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Φ ∈ GL2LocalData.SBE E,
    GL2LocalData.rWm χ σ μE lam h Φ ∈ GL2LocalData.SBE E ∧ GL2LocalData.rWm χ σ μE lam (g * h) Φ = GL2LocalData.rWm χ σ μE lam g (GL2LocalData.rWm χ σ μE lam h Φ)) →
  ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Φ ∈ (SBC : Set ((Fin 2 → F) → ℂ)),
    rWCm χ M lam (GL2LocalData.nsg E) h Φ ∈ (SBC : Set ((Fin 2 → F) → ℂ)) ∧
      rWCm χ M lam (GL2LocalData.nsg E) (g * h) Φ = rWCm χ M lam (GL2LocalData.nsg E) g (rWCm χ M lam (GL2LocalData.nsg E) h Φ)

def RCWF : Prop := ForF fun F _ _ _ _ _ _ => ∀ (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ),
  eta 1 = 1 → M.IsSymm → ∀ (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F),
    rWCm χ M lam eta !![0, 1; -1, 0] Φ z = lam * FTb χ M Φ z

def bMR (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2 → ℝ) : ℝ := x ⬝ᵥ M *ᵥ y

def nMR (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ℝ := bMR M x x / 2

def muMR (M : Matrix (Fin 2) (Fin 2) ℝ) : Measure (Fin 2 → ℝ) := ENNReal.ofReal (|M.det| ^ (1 / 2 : ℝ)) • volume

def rWCR (M : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℂ) (eta : ℝ → ℂ) (a b c d : ℝ) (Φ : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  if c = 0 then
    Complex.exp (2 * Real.pi * Complex.I * ((a * b * nMR M z : ℝ) : ℂ)) * eta a * ((|a| : ℝ) : ℂ) * Φ (a • z)
  else lam * eta (-c) * ((|c|⁻¹ : ℝ) : ℂ) *
    ∫ u, Complex.exp (2 * Real.pi * Complex.I * (((a * nMR M z + d * nMR M u - bMR M z u) / c : ℝ) : ℂ)) * Φ u ∂muMR M

def rWCRm (M : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℂ) (eta : ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ((Fin 2 → ℝ) → ℂ) → (Fin 2 → ℝ) → ℂ :=
  rWCR M lam eta (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def schwartzR2 : Set ((Fin 2 → ℝ) → ℂ) := {Φ | ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ, ∀ x, f (WithLp.toLp 2 x) = Φ x}

def TRANSR : Prop := ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (j : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ),
  (∀ x, Complex.normSq (j x) = nMR M x) → (∀ x y, 2 * (conj (j x) * j y).re = bMR M x y) →
  Measure.map j (muMR M) = volC → ∀ (a b c d : ℝ) (Φ : ℂ → ℂ) (z : Fin 2 → ℝ),
    rWCR M Complex.I sgR a b c d (fun x => Φ (j x)) z = rWR a b c d Φ (j z)

def REPCR : Prop := RWRREP → ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (j : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ),
  (∀ x, Complex.normSq (j x) = nMR M x) → (∀ x y, 2 * (conj (j x) * j y).re = bMR M x y) →
  Measure.map j (muMR M) = volC → ∀ g h : Matrix (Fin 2) (Fin 2) ℝ, g.det = 1 → h.det = 1 → ∀ Φ ∈ schwartzR2,
    rWCRm M Complex.I sgR h Φ ∈ schwartzR2 ∧ rWCRm M Complex.I sgR (g * h) Φ = rWCRm M Complex.I sgR g (rWCRm M Complex.I sgR h Φ)

end Ad3.K.QuadraticBaseChangeGL3.Th
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

def GENSL : Prop := ∀ P : GL (Fin 2) ℚ → Prop, P 1 → (∀ (b : ℚ) γ, P γ → P (uni2 b * γ)) →
  (∀ γ' γ : GL (Fin 2) ℚ, γ'.val = !![0, 1; -1, 0] → P γ → P (γ' * γ)) → ∀ γ : GL (Fin 2) ℚ, (γ.val).det = 1 → P γ

variable (K) in

def THN : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ (b : ℚ), ∀ g ∈ Gp M, thP n t M (dia2 (uni2 b) * g) = thP n t M g

variable (K) in

def THW : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ γ' : GL (Fin 2) ℚ, γ'.val = !![0, 1; -1, 0] →
    ∀ g ∈ Gp M, thP n t M (dia2 γ' * g) = thP n t M g

variable (K) in

def THSOF : Prop := GENSL → THN K → THW K → THS K

def LPIF : Prop := GL2LocalData.WRep → GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c,
  ∀ γ g : GL (Fin 2) F, (γ.val).det = 1 → GL2LocalData.piE E χ σ η c (γ * g) Φ = GL2LocalData.rWE E χ σ η γ.val (GL2LocalData.piE E χ σ η c g Φ)

def LPIS : Prop := GL2LocalData.SRep → GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ : Fˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBE (F × F),
  ∀ γ g : GL (Fin 2) F, (γ.val).det = 1 → GL2LocalData.piS χ c₁ (γ * g) Φ = GL2LocalData.rWS χ γ.val (GL2LocalData.piS χ c₁ g Φ)

def LPIR : Prop := RWRREP → ∀ (cf : ℂˣ → ℂ), ∀ Φ ∈ SchC, ∀ γ g : GL (Fin 2) ℝ, (γ.val).det = 1 →
  piRc cf (γ * g) Φ = rWRm γ.val (piRc cf g Φ)

def IntB (β : Module.Basis (Fin 2) ℚ K) : Prop := ∀ x : K, IsIntegral ℤ x ↔ ∀ i, ∃ m : ℤ, β.repr x i = m

def gramQ (β : Module.Basis (Fin 2) ℚ K) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => Algebra.trace ℚ K (β i) * Algebra.trace ℚ K (β j) - Algebra.trace ℚ K (β i * β j)

def crd (R : Type) [Field R] [Algebra ℚ R] (β : Module.Basis (Fin 2) ℚ K) (ξ : K) : Fin 2 → R :=
  fun i => algebraMap ℚ R (β.repr ξ i)

def FTbR (M : Matrix (Fin 2) (Fin 2) ℝ) (Φ : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : ℂ :=
  ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((bMR M y x : ℝ) : ℂ)) ∂muMR M

def IntAt (v : Pl) (x : Fin 2 → ℚ) : Prop := ∀ i, algebraMap ℚ (Qv v) (x i) ∈ 𝒪[Qv v]

open Classical in

def CPOIS : Prop := ∀ (M : Matrix (Fin 2) (Fin 2) ℚ), M.IsSymm → M.det ≠ 0 → ∀ S : Finset Pl,
  (∀ v ∉ S, (∀ i j, algebraMap ℚ (Qv v) (M i j) ∈ 𝒪[Qv v]) ∧ (modulus (algebraMap ℚ (Qv v) M.det) : ℝ) = 1) →
  ∀ Fi ∈ schwartzR2, ∀ Fv : ∀ v : S, (Fin 2 → Qv v.1) → ℂ, (∀ v, Fv v ∈ (SBC : Set ((Fin 2 → Qv v.1) → ℂ))) →
    (∑' x : Fin 2 → ℚ, Fi (fun i => (x i : ℝ)) * (∏ v : S, Fv v (fun i => algebraMap ℚ (Qv v.1) (x i))) *
        (if ∀ v ∉ S, IntAt v x then 1 else 0)) =
      ∑' x : Fin 2 → ℚ, FTbR (M.map (algebraMap ℚ ℝ)) Fi (fun i => (x i : ℝ)) *
        (∏ v : S, FTb (GP.psiF v.1)⁻¹ (M.map (algebraMap ℚ (Qv v.1))) (Fv v) (fun i => algebraMap ℚ (Qv v.1) (x i))) *
        (if ∀ v ∉ S, IntAt v x then 1 else 0)

namespace LM
variable {c : HeckeCharacter K} {v : Pl}

def lam : LM c v → ℂ
  | sp .. => 1
  | ns w _ η _ => GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η

end LM

variable (K) in

def LAMP : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∏ᶠ v, (M v).lam = -Complex.I

variable (K) in

def JEX : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (d : LM c v), d.ok →
  ∀ β : Module.Basis (Fin 2) ℚ K, IntB β →
  match d with
  | @LM.sp _ _ _ _ _ w₁ w₂ _ _ _ => ∃ j : (Fin 2 → Qv v) ≃ₗ[Qv v] (Qv v × Qv v), Continuous j ∧ Continuous j.symm ∧
      (∀ x, (j x).1 * (j x).2 = nM ((gramQ β).map (algebraMap ℚ (Qv v))) x) ∧
      (∀ x y, Algebra.trace (Qv v) (Qv v × Qv v) (GL2LocalData.swapE (j x) * j y) = bM ((gramQ β).map (algebraMap ℚ (Qv v))) x y) ∧
      Measure.map j (muM (GP.psiF v)⁻¹ ((gramQ β).map (algebraMap ℚ (Qv v)))) = GL2LocalData.muS (GP.psiF v)⁻¹ ∧
      (∀ ξ : K, j (crd (Qv v) β ξ) = (dg1 v w₁ ξ, dg1 v w₂ ξ)) ∧
      ∀ x, (j x).1 ∈ 𝒪[Qv v] ∧ (j x).2 ∈ 𝒪[Qv v] ↔ ∀ i, x i ∈ 𝒪[Qv v]
  | @LM.ns _ _ _ _ _ w _ σ _ _ => ∃ j : (Fin 2 → Qv v) ≃ₗ[Qv v] Kv K w, Continuous j ∧ Continuous j.symm ∧
      (∀ x, Algebra.norm (Qv v) (j x) = nM ((gramQ β).map (algebraMap ℚ (Qv v))) x) ∧
      (∀ x y, Algebra.trace (Qv v) (Kv K w) (σ (j x) * j y) = bM ((gramQ β).map (algebraMap ℚ (Qv v))) x y) ∧
      Measure.map j (muM (GP.psiF v)⁻¹ ((gramQ β).map (algebraMap ℚ (Qv v)))) =
        selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹) ∧
      (∀ ξ : K, j (crd (Qv v) β ξ) = algebraMap K (Kv K w) ξ) ∧
      ∀ x, j x ∈ 𝒪[Kv K w] ↔ ∀ i, x i ∈ 𝒪[Qv v]

variable (K) in

def JEXR : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ β : Module.Basis (Fin 2) ℚ K,
  ∃ j : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ, (∀ x, Complex.normSq (j x) = nMR ((gramQ β).map (algebraMap ℚ ℝ)) x) ∧
    (∀ x y, 2 * (conj (j x) * j y).re = bMR ((gramQ β).map (algebraMap ℚ ℝ)) x y) ∧
    Measure.map j (muMR ((gramQ β).map (algebraMap ℚ ℝ))) = volC ∧ ∀ ξ : K, j (crd ℝ β ξ) = embC K ξ

variable (K) in

def IBEX : Prop := Module.finrank ℚ K = 2 → ∃ β : Module.Basis (Fin 2) ℚ K, IntB β

variable (K) in

def THWOF : Prop := LPIF → LPIS → LPIR → GL2LocalData.WRep → GL2LocalData.SRep → RWRREP → GL2LocalData.WSB → TRANS → REPC → RCWF → TRANSR → REPCR →
  CPOIS → LAMP K → JEX K → JEXR K → IBEX K → THW K

end Ad3.K.QuadraticBaseChangeGL3.Th
end
end
