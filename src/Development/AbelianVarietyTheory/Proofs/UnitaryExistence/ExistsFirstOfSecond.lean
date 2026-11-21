import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LatticeEmbeddingHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.UnimodularStandardLattice

section
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.XiDetCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.CoefChangeCompare
open scoped TensorProduct

section Lattices

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

def latHat0 (L0 : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ x i}

def finVec (v : Fin r → E) : Fin r → AdE F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

variable {F}

def gLat (L0 : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Set (Fin r → AdE F E) :=
  g.mulVec '' (latHat0 F L0 : Set (Fin r → AdE F E))

def latG (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat L0 g ∧ w = a • v}

def latGHat (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat L0 g, w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a) * z i}

variable (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

end Lattices

section Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  [Fact (IsRealIn F E)] {r : ℕ}

def Reads (xi : (AdE F E)ˣ →* ℂˣ) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ x u : (AdE F E)ˣ, (x : AdE F E) = u * conjA F (x : AdE F E) → ((xi u : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)

def TrivFix (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1

def TrivRat (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1

theorem exists_extend {A M : Type} [CommGroup A] [CommGroup M] (Φ : A →* M) (hΦ : Function.Injective Φ) (χ : A →* ℂˣ) :
    ∃ κ : M →* ℂˣ, ∀ x, κ (Φ x) = χ x := by
  letI : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  letI : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  exact ⟨MonoidHom.toAdditive.symm ρ, fun x => DFunLike.congr_fun hρ (Additive.ofMul x)⟩

end Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r rk : ℕ}
variable {𝔾 : Type} [Group 𝔾]

section First

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin rk) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin rk → E)) (AA : Set E)

variable {Th : Type} (arch : Th → 𝔾 → Matrix (Fin rk) (Fin rk) ℂ)

open Classical in

def DictBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → Th) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((Fu.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (Fu.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (Fu.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = Fu.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fu.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : 𝔾, ∃ γ ∈ Γ,
      ((U.X (dict h).1).Λ : Set (Fin r → E)) =
        (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (arch (th (dict h).1 τ) (γ * h)) * x₀ τ.1

variable (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (IsInf : (E →+* ℂ) → Th → Prop)

end First

section Mark

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def embOf (k : U.Comp) : (Fu.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap

variable {L0 AA ι}

end Mark

section Value

variable [Fact (IsRealIn F E)]

def XiValAtC {c : Coeff l} (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → toC (evR Xo c f y) = c0 * ((ξ x : Circle) : ℂ)

variable (Xo) in

def XiValC (c : Coeff l) (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAtC c0 Gm ι ξ σ Fu φ f

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) {L0 : Submodule (𝓞 E) (Fin r → E)} {AA : Set E}
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
  (ψ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E))

def Reaches (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ (i : Fin Fu.n) (gm : Matrix (Fin r) (Fin r) (AdE F E)), IsUnitaryA Gm gm → LatAt ι (ψ i) gm →
    MarkAt l ι (ψ i) (Fu.t i) gm → ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) lab P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → ∃ h : 𝔾, (fin h).1 = gm ∧ ik (dict h).1 = i ∧
        ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un (dict h).1 ⟨(dict h).2, hx⟩) y

variable {Γ fin U dict Fu ik φ ψ} {Gm : Matrix (Fin r) (Fin r) E} {xi : (AdE F E)ˣ →* ℂˣ} {ξ : (AdE F E)ˣ →* Circle}
  {c0 : ℂ} {f : Rul Xo c}

end Value

section Covers

variable [Fact (IsRealIn F E)] (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E))
  (AA : Set E) {Th : Type} (arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ) (IsInf : (E →+* ℂ) → Th → Prop)

variable {Γ fin L0 AA arch IsInf} {gram : Matrix (Fin r) (Fin r) E} {xi0 : E}

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : 𝔾 → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin Fu.n} {φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ} {th : ∀ k, (U.X k).Ψ → Th}

end One

variable {c : Coeff l} {σ0 : c.F →+* ℂ} {Tup : Type*} {dδ : Tup → DeltaDat Xo c n}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle} {c0 : ℂ}

end Covers

section Comparison₂

section Act

variable (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

variable {c} {c' : Coeff l} (hle : c.F ≤ c'.F)

end Act

variable (Γ : Subgroup 𝔾)

def adelFn {Comp : Type} {X : Comp → Data E r} (dict : 𝔾 → Σ k, Frame (X k).Ψ r) (mu : 𝔾 → ℂ) (P : FDSec X) : 𝔾 → ℂ :=
  fun g => mu g * P (dict g).1 (dict g).2

def jOnQ {Comp : Type} {X : Comp → Data E r} {C : Type} (rd : C → FDSec X) (dict : 𝔾 → Σ k, Frame (X k).Ψ r) (mu : 𝔾 → ℂ)
    (f : C) : Quotient (QuotientGroup.rightRel Γ) → ℂ := fun q => adelFn dict mu (rd f) q.out

variable (Xo) in

def IsSumDown (c : Coeff l) {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]
    (dδ : DeltaDat Xo c n) (w : Cl → (Fin n → LevQ Dw dδ.l₂) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ vc : Cl → k, (∀ cl, ShortValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w cl q)) (La cl) 1 (Nc cl)
          (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (io (x cl))) y₂ (vc cl)) ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ *
          ∑ cl, algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) * vc cl

variable (Xo) in

def RowFirst (c : Coeff l) {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] {σ0 : c.F →+* ℂ} (U : Unf Xo c σ0 r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c.F) (ep : ∀ t, Cl' t → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
    (LL : IntermediateField ℚ ℂ) (Cu : Submodule c.F (Rul Xo c)) (cst : U.Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cst k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      (∃ f ∈ Cu, IsSumDown Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      (∀ f ∈ sec Xo c a n, IsSumDown Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : Quotient (QuotientGroup.rightRel Γ), ph * thAd t x q =
          ze * cst (dict q.out).1 * (lieFac Dw xr a : ℂ) * jOnQ Γ (rdU U) dict mu (act z f) q)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F) {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def TieFirst (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    (dict : 𝔾 → Σ k, Frame ((unifExt hle U σ0').X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
    (cst : (unifExt hle U σ0').Comp → ℂ) (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspSums hle U ∧ ActSums hle act act' ∧
    RowFirst Xo Γ c' (unifExt hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unifExt hle U) a n) cst ph

variable (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
  (dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
  (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)] (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
  (La : ∀ t, Cl' t → GenLat E n) (Nc gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F)
  (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
  (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
  (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ)

end Comparison₂

section Whole

variable [Fact (IsRealIn F E)] {Γ : Subgroup 𝔾} {fin : 𝔾 →* GL (Fin r) (AdE F E)} {L0 : Submodule (𝓞 E) (Fin r → E)}
  {AA : Set E} {Th : Type} {arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ} {IsInf : (E →+* ℂ) → Th → Prop}
  {gram : Matrix (Fin r) (Fin r) E} {xi0 : E} {c c' : Coeff l} {hle : c.F ≤ c'.F} {Vs : Type} [AddCommGroup Vs]
  [Module c'.F Vs] {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
  {dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r} {mu : 𝔾 → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)} {Tup : Type*} {dδ : Tup → DeltaDat Xo c' n}
  {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)] {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F}
  {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F}
  {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop}
  {cst : (U (sig0 c)).Comp → ℂ} {ph : ℂ}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((sig0 c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle}

end Whole

end GlobalTheory.XiDetCompare
end
end

section
noncomputable section

namespace GlobalTheory.DictPinCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix

abbrev conjHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toRingEquiv.toRingHom

section First

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)

def gramOf : Matrix (Fin n) (Fin n) E := Matrix.of fun a b => hT (fr a) (fr b)

def latHat : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Fin𝔸 F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ fr.repr x i}

def archM (th' : Inf𝔸 F ⊗[F] E →+* ℂ) (h : G) : Matrix (Fin n) (Fin n) ℂ := (infHom h).1.map th'

def finVec (v : Fin n → E) : Fin n → Fin𝔸 F ⊗[F] E := fun i => (1 : Fin𝔸 F) ⊗ₜ v i

def gLat (g : G) : Set (Fin n → Fin𝔸 F ⊗[F] E) :=
  (finHom g).1.mulVec '' (latHat F fr L0 : Set (Fin n → Fin𝔸 F ⊗[F] E))

def latG (g : G) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat F fr L0 finHom g ∧ w = a • v}

def latGHat (g : G) : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat F fr L0 finHom g,
    w = fun i => ((1 : Fin𝔸 F) ⊗ₜ a) * z i}

def LatEmb {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG F fr L0 AA finHom 1

def LatIsom {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ E (xi0 * hT (fr.equivFun.symm (ι x)) (fr.equivFun.symm (ι y)))

def ModelW (hr : n = r) (X : Data E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) (gramOf fr hT)).transpose ∧ X.ξ0 = -xi0

def IsOrthogonalFrame (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def halfVec (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : Fin n → Fin𝔸 F ⊗[F] E :=
  fun i => ((1 : Fin𝔸 F) ⊗ₜ (b : E)) * z i

def KfHalf (Kf : Subgroup G) (M : ℕ) (Mh : Ideal (𝓞 E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC ∧ ∀ b ∈ Mh, ∀ z ∈ latHat F fr L0, ∃ y ∈ latHat F fr L0,
    (finHom k).1.mulVec (halfVec F b z) - halfVec F b z = M • y

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

open Classical in

def DictLat (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 E] (Fin n → E)) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((Fm.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (Fm.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (Fm.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = Fm.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fm.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : G, ∃ γ ∈ GQ,
      ((U.X (dict h).1).Λ : Set (Fin r → E)) =
        (fun v : Fin n → E => v ∘ Fin.cast hr.symm) '' (latG F fr L0 AA finHom (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        ∃ w ∈ latGHat F fr L0 AA finHom (γ * h),
        finVec F ((φ (dict h).1 (Fm.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (finHom (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM F infHom (th (dict h).1 τ) (γ * h)) * x₀ τ.1

def AdPinWith (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (Q : ∀ k, (Dw.La → (U.X k).Λ) → Prop) : Prop :=
  ∃ (hr : n = r)
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
    (LatEmb F fr L0 AA finHom ι ∧ LatIsom fr hT xi0 Dw.EF ι ∧ (∀ k τ, IsArchAt F τ.1 (th k τ)) ∧
      DictLat F fr L0 AA infHom finHom GQ U hr dict ι e Fm ik φ th x₀) ∧
    ∀ k, Q k fun a => φ k (Fm.t (ik k) a)

def AdPin (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∃ (hr : n = r)
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
    LatEmb F fr L0 AA finHom ι ∧ LatIsom fr hT xi0 Dw.EF ι ∧ (∀ k τ, IsArchAt F τ.1 (th k τ)) ∧
      DictLat F fr L0 AA infHom finHom GQ U hr dict ι e Fm ik φ th x₀

def TypeClause (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (q : ℕ) (X : Data E r) : Prop :=
  X.p0 = q ∧ ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0

def flipForm (x y : W) : E := hT y x

def IsRatPoints : Prop :=
  (∀ γ ∈ GQ, ∃ γ₀, IsRatUnitary fr (flipForm hT) γ₀ ∧ finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀) ∧
    ∀ γ₀, IsRatUnitary fr (flipForm hT) γ₀ →
      ∃ γ ∈ GQ, finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀

end First

section Compare

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)

def coord : W ≃ₗ[𝓞 E] (Fin n → E) := fr.equivFun.restrictScalars (𝓞 E)

theorem finVec_coord (v : W) : finVec F (coord fr v) = toFin F fr v := rfl

theorem latGHat_eq (g : G) : latGHat F fr L0 AA finHom g = latAd F fr L0 (AA : Submodule (𝓞 E) E) (finHom g) := by
  unfold latGHat latAd
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨a, ha, z, hz, rfl⟩
  · rintro ⟨a, ha, z, hz, rfl⟩
    exact ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩

theorem coord_smul (a : E) (v : W) : coord fr (a • v) = a • coord fr v := fr.equivFun.map_smul a v

theorem latG_eq (g : G) : latG F fr L0 AA finHom g =
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 (AA : Submodule (𝓞 E) E) (finHom g)).map (coord fr).toLinearMap := by
  unfold latG GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, v, ⟨z, hz, hv⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (coord fr).surjective v
    exact ⟨a • x, ⟨a, ha, x, ⟨z, hz, hv.symm⟩, rfl⟩, coord_smul fr a x⟩
  · rintro ⟨_, ⟨a, ha, x, ⟨z, hz, hv⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, coord fr x, ⟨z, hz, hv.symm⟩, coord_smul fr a x⟩

theorem mem_latG_iff (g : G) (v : W) : coord fr v ∈ latG F fr L0 AA finHom g ↔
    v ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 (AA : Submodule (𝓞 E) E) (finHom g) := by
  rw [latG_eq]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← (coord fr).injective h]
  · exact fun h => ⟨v, h, rfl⟩

theorem latHat_eq_hat : GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 =
    GlobalTheory.AdLat.hat F ((L0.map (coord fr).toLinearMap : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat GlobalTheory.AdLat.hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

theorem span_coord (hsp : Submodule.span E (L0 : Set W) = ⊤) :
    Submodule.span E ((L0.map (coord fr).toLinearMap : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  have h : ((L0.map (coord fr).toLinearMap : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      fr.equivFun.toLinearMap '' (L0 : Set W) := rfl
  rw [h, ← Submodule.map_span, hsp, Submodule.map_top, LinearEquiv.range]

theorem latG_one (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (𝔄 : Submodule (𝓞 E) E) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 𝔄 1 = latBase L0 𝔄 := by
  refine le_antisymm (Submodule.span_mono ?_) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latBase_le_latG_one F fr L0 𝔄)
  rintro _ ⟨a, ha, x, ⟨z, hz, hx⟩, rfl⟩
  refine ⟨a, ha, x, ?_, rfl⟩
  rw [Units.val_one, Matrix.one_mulVec] at hx
  rw [← hx, latHat_eq_hat] at hz
  obtain ⟨y, hy, h⟩ := ((GlobalTheory.AdLat.hat_rational_points_and_approx F E n _ (hfg.map _) (span_coord fr L0 hsp)).1
    (coord fr x)).1 hz
  rwa [← (coord fr).injective h]

theorem trace_flip (hherm : ∀ x y, cc (hT x y) = hT y x) (hxi : cc xi0 = -xi0) (x y : W) :
    Algebra.trace ℚ E (xi0 * flipForm hT x y) = -Algebra.trace ℚ E (xi0 * hT x y) := by
  have h := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (xi0 * hT x y)
  rw [← h, ← map_neg]
  congr 1
  show xi0 * hT y x = -(IsCMField.complexConj E (xi0 * hT x y))
  rw [map_mul, ← hherm x y]
  unfold cc at hxi ⊢
  rw [hxi]; ring

theorem latEmb_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hherm : ∀ x y, cc (hT x y) = hT y x) (hxi : cc xi0 = -xi0)
    (ι : Dw.La →ₗ[𝓞 E] W) :
    (LatEmb F fr L0 AA finHom ((coord fr).toLinearMap ∘ₗ ι) ∧ LatIsom fr hT xi0 Dw.EF ((coord fr).toLinearMap ∘ₗ ι)) ↔
      IsLatEmb (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 Dw ι := by
  unfold LatEmb LatIsom IsLatEmb
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact (coord fr).injective.of_comp_iff ι
  · rw [latG_eq, map_one, latG_one fr L0 hfg hsp, LinearMap.range_comp]
    exact (Submodule.map_injective_of_injective (coord fr).injective).eq_iff
  · have e : ∀ x, fr.equivFun.symm (((coord fr).toLinearMap ∘ₗ ι) x) = ι x := fun x => fr.equivFun.symm_apply_apply _
    simp only [e, trace_flip hT xi0 hherm hxi]
    constructor <;> rintro ⟨ε, h⟩ <;> refine ⟨-ε, fun x y => ?_⟩ <;> rw [h] <;> simp

theorem hT_expand (y x : W) : hT y x = ∑ a, ∑ b, fr.repr x a * gramOf fr hT b a * cc (fr.repr y b) := by
  conv_lhs => rw [← fr.sum_repr y, ← fr.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  show fr.repr x a * (cc (fr.repr y b) * hT (fr b) (fr a)) = fr.repr x a * hT (fr b) (fr a) * cc (fr.repr y b)
  ring

theorem model_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (hr : n = r) (q : ℕ) (X : Data E r)
    (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im) :
    (ModelW fr hT xi0 hr X ∧ TypeClause H q X) ↔ IsModelOf H hr fr (flipForm hT) xi0 q X := by
  subst hr
  have hG : X.Gm = -(Matrix.reindex (finCongr rfl) (finCongr rfl) (gramOf fr hT)).transpose ↔
      ∀ x y : W, herm X.Gm (crd rfl fr x) (crd rfl fr y) = -flipForm hT x y := by
    constructor
    · intro h x y
      rw [h, flipForm, hT_expand fr hT y x, herm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [crd]
    · intro h
      ext a b
      have := h (fr a) (fr b)
      simp [herm, crd, Finsupp.single_apply, cc, apply_ite, flipForm] at this
      simp [gramOf, this]
  unfold ModelW TypeClause IsModelOf
  rw [hG]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, h3, h4, Or.inr h2, fun τ hτ => ?_⟩
    rw [h2, map_neg, Complex.neg_im]
    exact neg_neg_of_pos (hsgn τ ((h4 τ).1 hτ))
  · rintro ⟨h1, h3, h4, h2, h5⟩
    refine ⟨⟨h1, h2.resolve_left fun h => ?_⟩, h3, h4⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ X.Ψ
      · exact ⟨τ, hτ⟩
      · exact ⟨_, not_not.1 fun h' => hτ ((X.cmType τ).2 h')⟩
    have := h5 τ hτ
    rw [h] at this
    exact lt_asymm this (hsgn τ ((h4 τ).1 hτ))


def fixMod {R : Type} [CommRing R] (k : Matrix (Fin n) (Fin n) R) (M : ℕ) (P : AddSubgroup (Fin n → R)) :
    AddSubgroup (Fin n → R) where
  carrier := {v | ∃ y ∈ P, k *ᵥ v - v = M • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro v w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [Matrix.mulVec_add, smul_add, ← h, ← h']; abel⟩
  neg_mem' := by
    rintro v ⟨y, hy, h⟩
    exact ⟨-y, neg_mem hy, by rw [Matrix.mulVec_neg, smul_neg, ← h]; abel⟩

theorem fixMod_smul {R : Type} [CommRing R] {k : Matrix (Fin n) (Fin n) R} {M : ℕ} {P P' : AddSubgroup (Fin n → R)}
    (s : R) (hs : ∀ y ∈ P, s • y ∈ P') {v : Fin n → R} (hv : v ∈ fixMod k M P) : s • v ∈ fixMod k M P' := by
  obtain ⟨y, hy, h⟩ := hv
  exact ⟨s • y, hs y hy, by rw [Matrix.mulVec_smul, ← smul_sub, h, smul_comm]⟩

theorem mem_fixMod_iff {R : Type} [CommRing R] {k : Matrix (Fin n) (Fin n) R} {M : ℕ} {P : AddSubgroup (Fin n → R)}
    {v : Fin n → R} : v ∈ fixMod k M P ↔ ∃ y ∈ P, v - k *ᵥ v = M • y := by
  constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, neg_sub]⟩

abbrev ad (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] (a : E) : Fin𝔸 F ⊗[F] E := 1 ⊗ₜ a

omit [NumberField E] [IsCMField E] in
theorem ad_mul (a b : E) : ad F (a * b) = ad F a * ad F b := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [IsCMField E] in
theorem mem_of_mul_inv {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E)}
    {z : Fin n → Fin𝔸 F ⊗[F] E} (h : ∀ a ∈ I, ∀ b ∈ I⁻¹, ad F (a * b) • z ∈ P) : z ∈ P := by
  have key : ∀ c ∈ I * I⁻¹, ad F c • z ∈ P := fun c hc =>
    FractionalIdeal.mul_induction_on hc h fun x y hx hy => by
      rw [ad, TensorProduct.tmul_add, add_smul]; exact add_mem hx hy
  have := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  rwa [ad, ← Algebra.TensorProduct.one_def, one_smul] at this

theorem mul_inv_smul_mem {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹)
    {z : Fin n → Fin𝔸 F ⊗[F] E} (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    ad F (a * b) • z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  have hab : a * b ∈ I * I⁻¹ := FractionalIdeal.mul_mem_mul ha hb
  rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hab
  obtain ⟨s, hs⟩ := hab
  rw [latHat_eq_hat] at hz ⊢
  rw [← hs]
  exact GlobalTheory.AdLat.Translate.hat_smul_ring _ s hz

omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W] in
theorem toFin_smul (a : E) (x : W) : toFin F fr (a • x) = ad F a • toFin F fr x := by
  funext i
  simp [toFin, Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W] in
theorem toFin_mem {x : W} (hx : x ∈ L0) : toFin F fr x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, hx, rfl⟩

omit [IsCMField E] in
theorem smul_mem_latAd_one {a : E} (ha : a ∈ AA) {z : Fin n → Fin𝔸 F ⊗[F] E}
    (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) : ad F a • z ∈ latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 :=
  AddSubgroup.subset_closure ⟨a, ha, z, hz, by rw [Units.val_one, Matrix.one_mulVec]⟩

theorem inv_smul_mem_latHat (hA : AA ≠ 0) {b : E} (hb : b ∈ AA⁻¹) {w : Fin n → Fin𝔸 F ⊗[F] E}
    (hw : w ∈ latAd F fr L0 (AA : Submodule (𝓞 E) E) 1) : ad F b • w ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    rw [Units.val_one, Matrix.one_mulVec, smul_smul, ← ad_mul, mul_comm]
    exact mul_inv_smul_mem fr L0 hA ha hb hz
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

omit [NumberField E] [IsCMField E] in
theorem halfVec_eq (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : halfVec F b z = ad F (algebraMap (𝓞 E) E b) • z := rfl

def FixesHalf (k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)) (M : ℕ) (Mh : Ideal (𝓞 E)) : Prop :=
  ∀ b ∈ Mh, ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0,
    ad F (algebraMap (𝓞 E) E b) • z ∈ fixMod k M (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)

theorem FixesHalf.mulVec_mem {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : FixesHalf fr L0 k M Mh) (hM : (M : 𝓞 E) ∈ Mh) (hM0 : M ≠ 0) :
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  have hI : (Mh : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => hM0 (by rw [h0, Ideal.mem_bot] at hM; exact_mod_cast hM)
  intro z hz
  refine mem_of_mul_inv hI fun a ha b hb => ?_
  obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  obtain ⟨y, hy, e⟩ := h a' ha' z hz
  have eM : ad F (algebraMap (𝓞 E) E (M : 𝓞 E)) = (M : Fin𝔸 F ⊗[F] E) := by
    rw [map_natCast]
    exact map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] Fin𝔸 F ⊗[F] E) M
  have e' : ad F (algebraMap (𝓞 E) E a' * b) • k *ᵥ z =
      ad F (algebraMap (𝓞 E) E a' * b) • z + ad F (algebraMap (𝓞 E) E (M : 𝓞 E) * b) • y := by
    rw [Matrix.mulVec_smul, sub_eq_iff_eq_add'] at e
    rw [mul_comm _ b, mul_comm _ b, ad_mul, ad_mul, mul_smul, mul_smul, mul_smul, ← smul_add, e, eM,
      Nat.cast_smul_eq_nsmul]
  rw [e']
  exact add_mem (mul_inv_smul_mem fr L0 hI ha hb hz)
    (mul_inv_smul_mem fr L0 hI (FractionalIdeal.mem_coeIdeal_of_mem _ hM) hb hy)

omit [IsCMField E] in
theorem latAd_eq_of_stab {k : GL (Fin n) (Fin𝔸 F ⊗[F] E)}
    (h1 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)
    (h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 := by
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    exact smul_mem_latAd_one fr L0 AA ha (h1 z hz)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, _, h2 z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]

omit [NumberField E] [IsCMField E] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] in
theorem toFin_add (x y : W) : toFin F fr (x + y) = toFin F fr x + toFin F fr y := by
  funext i
  simp [toFin, TensorProduct.tmul_add]

omit [NumberField E] [IsCMField E] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] in
theorem toFin_zero : toFin F fr (0 : W) = 0 := by
  funext i
  simp [toFin]

theorem FixesHalf.base {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : FixesHalf fr L0 k M Mh) {u : W} (hu : u ∈ latBase L0 (AA : Submodule (𝓞 E) E)) : ∀ b ∈ Mh,
    toFin F fr (b • u) ∈ fixMod k M (latAd F fr L0 (AA : Submodule (𝓞 E) E) 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hu
    intro b hb
    rw [← algebraMap_smul E b, smul_comm, toFin_smul, toFin_smul]
    exact fixMod_smul _ (fun y hy => smul_mem_latAd_one fr L0 AA ha hy) (h b hb _ (toFin_mem fr L0 hx))
  | zero =>
    intro b _
    rw [smul_zero, toFin_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro b hb
    rw [smul_add, toFin_add]
    exact add_mem (hx b hb) (hy b hb)
  | smul s x _ hx =>
    intro b hb
    rw [smul_smul]
    exact hx _ (Mh.mul_mem_right s hb)

theorem fixesHalf_of_base (hA : AA ≠ 0) {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : ∀ u ∈ latBase L0 (AA : Submodule (𝓞 E) E), ∀ b ∈ Mh,
      toFin F fr (b • u) ∈ fixMod k M (latAd F fr L0 (AA : Submodule (𝓞 E) E) 1)) : FixesHalf fr L0 k M Mh := by
  intro b hb z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hz
    have e : (fun i => t ⊗ₜ[F] fr.repr x i) = (t ⊗ₜ[F] (1 : E) : Fin𝔸 F ⊗[F] E) • toFin F fr x :=
      GlobalTheory.AdLat.Translate.gen_eq t (coord fr x)
    rw [e, smul_comm]
    refine fixMod_smul (P := GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) _ (fun y hy => ?_)
      (mem_of_mul_inv hA fun a ha a' ha' => ?_)
    · rw [latHat_eq_hat] at hy ⊢
      exact GlobalTheory.AdLat.Translate.hat_smul_int ht hy
    · have h5 := h (a • x) (Submodule.subset_span ⟨a, ha, x, hx, rfl⟩) b hb
      rw [← algebraMap_smul E b, smul_comm, toFin_smul, toFin_smul] at h5
      rw [mul_comm, ad_mul, mul_smul]
      exact fixMod_smul _ (fun y hy => inv_smul_mem_latHat fr L0 AA hA ha' hy) h5
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem level_elem_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0) (ι : Dw.La →ₗ[𝓞 E] W)
    (hι : LinearMap.range ι = latBase L0 (AA : Submodule (𝓞 E) E)) (cj : E ≃ₐ[F] E)
    (k : GL (Fin n) (Fin𝔸 F ⊗[F] E)) (hdet : k.1.det * GlobalTheory.AdLat.sg (Fin𝔸 F) cj k.1.det = 1) :
    FixesHalf fr L0 k.1 l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔
      latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 ∧
        ∀ a ∈ half Dw l, CongrAt F fr L0 (AA : Submodule (𝓞 E) E) l.M k (ι a) (ι a) := by
  constructor
  · intro h
    have hM : (l.M : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have h0 := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
      rw [← l.prod] at h0
      exact (Ideal.mem_inf.1 (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h0)).2
    have h1 := h.mulVec_mem fr L0 hM (by have := l.three_le; omega)
    have h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
      rw [latHat_eq_hat] at h1 ⊢
      exact GlobalTheory.AdLat.inv_mulVec_mem_hat F E n _ k cj (hfg.map _) (span_coord fr L0 hsp) h1 hdet
    have h3 := latAd_eq_of_stab fr L0 AA h1 h2
    refine ⟨h3, fun a ha => ?_⟩
    unfold CongrAt
    rw [h3, ← mem_fixMod_iff]
    refine Submodule.smul_induction_on (p := fun a => toFin F fr (ι a) ∈ fixMod k.1 l.M _) ha (fun b hb x _ => ?_)
      fun x y hx hy => ?_
    · rw [map_smul]
      exact h.base fr L0 AA (by rw [← hι]; exact LinearMap.mem_range_self ι x) b hb
    · rw [map_add, toFin_add]
      exact add_mem hx hy
  · rintro ⟨h3, h⟩
    refine fixesHalf_of_base fr L0 AA hA fun u hu b hb => ?_
    rw [← hι] at hu
    obtain ⟨x, rfl⟩ := hu
    have h5 := h (b • x) (Submodule.smul_mem_smul hb Submodule.mem_top)
    unfold CongrAt at h5
    rwa [h3, ← mem_fixMod_iff, map_smul] at h5

theorem mem_unitaryOver_iff (cj : E ≃ₐ[F] E) (h : W → W → E) (A : Type) [CommRing A] [Algebra F A]
    (g : GL (Fin n) (A ⊗[F] E)) : g ∈ unitaryOver F cj fr h A ↔
      g.1ᵀ * (Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b)) * g.1.map (GlobalTheory.AdLat.sg A cj) =
        Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b) := by
  set B : Matrix (Fin n) (Fin n) (A ⊗[F] E) := Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b) with hB
  have e : ∀ (C : Matrix (Fin n) (Fin n) (A ⊗[F] E)) x y,
      ∑ a, ∑ b, x a * C a b * GlobalTheory.AdLat.sg A cj (y b) = x ⬝ᵥ C *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) := fun C x y => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Function.comp]
  have e2 : ∀ x y, (g.1 *ᵥ x) ⬝ᵥ B *ᵥ (GlobalTheory.AdLat.sg A cj ∘ (g.1 *ᵥ y)) =
      x ⬝ᵥ (g.1ᵀ * B * g.1.map (GlobalTheory.AdLat.sg A cj)) *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) := fun x y => by
    have : GlobalTheory.AdLat.sg A cj ∘ (g.1 *ᵥ y) = g.1.map (GlobalTheory.AdLat.sg A cj) *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) :=
      funext fun i => RingHom.map_mulVec (GlobalTheory.AdLat.sg A cj).toRingHom g.1 y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
  change (∀ x y, ∑ a, ∑ b, (g.1 *ᵥ x) a * B a b * GlobalTheory.AdLat.sg A cj ((g.1 *ᵥ y) b) =
    ∑ a, ∑ b, x a * B a b * GlobalTheory.AdLat.sg A cj (y b)) ↔ _
  simp only [e, e2]
  refine ⟨fun hh => ?_, fun hh x y => by rw [hh]⟩
  ext a b
  have e3 : GlobalTheory.AdLat.sg A cj ∘ (Pi.single b 1 : Fin n → A ⊗[F] E) = Pi.single b 1 := by
    funext i
    by_cases hi : i = b <;> simp [hi]
  have := hh (Pi.single a 1) (Pi.single b 1)
  simpa [e3] using this

theorem det_of_unitary (cj : E ≃ₐ[F] E) (hnd : (gramOf fr hT).det ≠ 0) (A : Type) [CommRing A] [Algebra F A]
    {g : GL (Fin n) (A ⊗[F] E)} (hg : g ∈ unitaryOver F cj fr (flipForm hT) A) :
    g.1.det * GlobalTheory.AdLat.sg A cj g.1.det = 1 := by
  have h := congrArg Matrix.det ((mem_unitaryOver_iff fr cj _ A g).1 hg)
  have hB : (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)) =
      (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom.mapMatrix (gramOf fr hT)ᵀ := rfl
  have hu : IsUnit (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)).det := by
    rw [hB, ← RingHom.map_det, Matrix.det_transpose]
    exact (IsUnit.mk0 _ hnd).map _
  have hs : (g.1.map (GlobalTheory.AdLat.sg A cj)).det = GlobalTheory.AdLat.sg A cj g.1.det :=
    (RingHom.map_det (GlobalTheory.AdLat.sg A cj).toRingHom g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at h
  refine hu.mul_left_cancel ?_
  rw [mul_one]
  linear_combination h

theorem level_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0) (hnd : (gramOf fr hT).det ≠ 0) (cj : E ≃ₐ[F] E)
    (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
    (ι : Dw.La →ₗ[𝓞 E] W) (hι : LinearMap.range ι = latBase L0 (AA : Submodule (𝓞 E) E)) (Kf : Subgroup G) :
    KfHalf F fr L0 finHom GfC Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔
      IsLevelStab F fr L0 (AA : Submodule (𝓞 E) E) l ι infHom finHom Kf := by
  refine forall_congr' fun k => iff_congr Iff.rfl (and_congr (hGf k) ?_)
  exact level_elem_iff fr L0 AA l hfg hsp hA ι hι cj _ (det_of_unitary fr hT cj hnd _ (hU k))

theorem latMark_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hr : n = r)
    (ι : Dw.La →ₗ[𝓞 E] W) (X : Data E r) (mk : Dw.La → X.Λ) (g : G) :
    (((X.Λ : Set (Fin r → E)) =
        (fun v : Fin n → E => v ∘ Fin.cast hr.symm) '' (latG F fr L0 AA finHom g : Set _)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ latGHat F fr L0 AA finHom g,
        finVec F ((mk a : Fin r → E) ∘ Fin.cast hr) -
          (finHom g).1.mulVec (finVec F (((coord fr).toLinearMap ∘ₗ ι) a)) = (l.M : ℕ) • w) ↔
      LatMark F hr fr L0 (AA : Submodule (𝓞 E) E) l ι X mk (finHom g) := by
  subst hr
  refine and_congr ?_ (forall₂_congr fun a _ => ?_)
  · have e : (fun v : Fin n → E => v ∘ Fin.cast (rfl : n = n).symm) = id := rfl
    rw [e, Set.image_id, SetLike.coe_set_eq, SetLike.ext_iff, (coord fr).surjective.forall]
    exact forall_congr' fun v => iff_congr Iff.rfl (mem_latG_iff fr L0 AA finHom g v)
  · have e : toFin F fr (vec rfl fr (mk a : Fin n → E)) = finVec F ((mk a : Fin n → E) ∘ Fin.cast rfl) := by
      have : vec rfl fr (mk a : Fin n → E) = fr.equivFun.symm (mk a : Fin n → E) := (fr.equivFun_symm_apply _).symm
      rw [this, ← finVec_coord]
      exact congrArg _ (fr.equivFun.apply_symm_apply _)
    unfold CongrAt
    rw [e, latGHat_eq]
    rfl

omit [IsCMField E] in
theorem isArchAt_unique [IsTotallyReal F] {τ : E →+* ℂ} {th th' : Inf𝔸 F ⊗[F] E →+* ℂ} (h : IsArchAt F τ th)
    (h' : IsArchAt F τ th') : th = th' := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rw [GlobalTheory.InfAdeleCM.hom_tmul τ th h.1 h.2, GlobalTheory.InfAdeleCM.hom_tmul τ th' h'.1 h'.2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem dictLat_iff (hQ : IsRatPoints F fr hT infHom finHom GQ) (U : Unf Xo c σ r) (hr : n = r)
    (dict : G → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] W) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) :
    DictLat F fr L0 AA infHom finHom GQ U hr dict ((coord fr).toLinearMap ∘ₗ ι) e Fm ik φ (fun _ τ => th τ.1) x₀ ↔
      IsFamilyOf U e Fm ik φ ∧ IsDictOf F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) l ι U.X
        (fun k a => φ k (Fm.t (ik k) a)) th x₀ infHom finHom dict := by
  refine and_congr Iff.rfl (forall_congr' fun h => ?_)
  constructor
  · rintro ⟨γ, hγ, h1, h2, h3⟩
    obtain ⟨γ₀, hu, e1, e2⟩ := hQ.1 γ hγ
    refine ⟨γ₀, hu, ?_, ?_⟩
    · rw [← e1, ← map_mul]
      exact (latMark_iff fr L0 AA finHom l hr ι _ _ _).1 ⟨h1, h2⟩
    · rw [← e2, ← map_mul]
      exact h3
  · rintro ⟨γ₀, hu, h1, h3⟩
    obtain ⟨γ, hγ, e1, e2⟩ := hQ.2 γ₀ hu
    rw [← e1, ← map_mul] at h1
    rw [← e2, ← map_mul] at h3
    obtain ⟨h1, h2⟩ := (latMark_iff fr L0 AA finHom l hr ι _ _ _).2 h1
    exact ⟨γ, hγ, h1, h2, h3⟩


theorem AdPinWith.adPin {U : Unf Xo c σ r} {dict : G → Σ k, Frame (U.X k).Ψ r}
    {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)} {Q : ∀ k, (Dw.La → (U.X k).Λ) → Prop}
    (h : AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ Q) :
    AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ := by
  obtain ⟨hr, g, e, Fm, ik, φ, th, h1, _⟩ := h
  exact ⟨hr, g, e, Fm, ik, φ, th, h1⟩

def embW (hr : n = r) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Dw.La →ₗ[𝓞 E] W :=
  (coord fr).symm.toLinearMap ∘ₗ LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀

theorem coord_embW (hr : n = r) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) :
    (coord fr).toLinearMap ∘ₗ embW fr hr ι₀ = LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀ :=
  LinearMap.ext fun _ => (coord fr).apply_symm_apply _

theorem embW_surjective (hr : n = r) : Function.Surjective (embW (Dw := Dw) fr hr) := by
  subst hr
  exact fun ι => ⟨(coord fr).toLinearMap ∘ₗ ι, LinearMap.ext fun _ => (coord fr).symm_apply_apply _⟩

def SidePins (U : Unf Xo c σ r) (hr : n = r) (Kf : Subgroup G) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  (∀ k, ModelW fr hT xi0 hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    KfHalf F fr L0 finHom GfC Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ∧ ∀ k, TypeClause H Dw.q (U.X k)

section Joint

variable [IsTotallyReal F] (cj : E ≃ₐ[F] E) (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0)
  (hherm : ∀ x y, cc (hT x y) = hT y x) (hnd : (gramOf fr hT).det ≠ 0) (hxi : cc xi0 = -xi0)
  (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im)
  (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
  (hQ : IsRatPoints F fr hT infHom finHom GQ)
  (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G)

include hfg hsp hA hherm hnd hxi hsgn hU hGf hQ

theorem joint_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf ↔
      ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk ∧
          ∃ gk : G, LatMark F hr fr L0 (AA : Submodule (𝓞 E) E) l (embW fr hr ι₀) (U.X k) mk (finHom gk) := by
  constructor
  · rintro ⟨g, e, Fm, ik, φ, ι, th, x₀, h1, h2, h3, h4, h5, h6⟩
    obtain ⟨ι₀, rfl⟩ := embW_surjective fr hr ι
    have hm := fun k => (model_iff fr hT xi0 H hr Dw.q (U.X k) hsgn).2 (h4 k).1
    have hl := (latEmb_iff fr hT L0 AA xi0 finHom Dw hfg hsp hherm hxi _).2 h2
    have hd := (dictLat_iff fr hT L0 AA infHom finHom GQ hQ U hr dict _ e Fm ik φ th x₀).2 ⟨h1, h6⟩
    rw [coord_embW] at hl hd
    exact ⟨x₀, ι₀, ⟨fun k => (hm k).1, fun k => (h4 k).2.1,
      (level_iff fr hT L0 AA infHom finHom GfC l hfg hsp hA hnd cj hU hGf _ h2.2.1 Kf).2 h5, fun k => (hm k).2⟩,
      hr, g, e, Fm, ik, φ, fun _ τ => th τ.1, ⟨hl.1, hl.2, fun _ τ => h3 τ.1, hd⟩, fun k => (h4 k).2.2⟩
  · rintro ⟨x₀, ι₀, ⟨s1, s2, s3, s4⟩, hr', g, e, Fm, ik, φ, th, ⟨h1, h2, h3, h4⟩, h5⟩
    choose th' hth using fun τ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) τ
    obtain rfl : th = fun _ τ => th' τ.1 := funext fun k => funext fun τ => isArchAt_unique (h3 k τ) (hth τ.1)
    rw [← coord_embW fr] at h1 h2 h4
    have hl := (latEmb_iff fr hT L0 AA xi0 finHom Dw hfg hsp hherm hxi _).1 ⟨h1, h2⟩
    have hd := (dictLat_iff fr hT L0 AA infHom finHom GQ hQ U hr dict _ e Fm ik φ th' x₀).1 h4
    exact ⟨g, e, Fm, ik, φ, embW fr hr ι₀, th', x₀, hd.1, hl, hth,
      fun k => ⟨(model_iff fr hT xi0 H hr Dw.q (U.X k) hsgn).1 ⟨s1 k, s4 k⟩, s2 k, h5 k⟩,
      (level_iff fr hT L0 AA infHom finHom GfC l hfg hsp hA hnd cj hU hGf _ hl.2.1 Kf).1 s3, hd.2⟩

theorem first_of_second
    (h : GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf) :
    ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧ AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ := by
  obtain ⟨x₀, ι₀, h1, h2⟩ :=
    (joint_iff fr hT L0 AA xi0 infHom finHom GQ GfC cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf).1 h
  exact ⟨x₀, ι₀, h1, h2.adPin⟩


end Joint


def withGroup (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (hle : Γ ≤ X.Γ)
    (hidx : ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab X.Gm X.Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ) (m : ℕ) (hm : 0 < m)
    (htr : ∀ ξ ∈ X.Λ, herm X.Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
      ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ ((m : E) * s * X.κ0)) : Data E r :=
  { X with
    Γ := Γ
    Γ_stab := fun γ h => X.Γ_stab γ (hle h)
    Γ_index := hidx
    Γ_free := fun γ h => X.Γ_free γ (hle h)
    χ_mul := fun la γ h γ' h' => X.χ_mul la γ (hle h) γ' (hle h')
    χ_add := fun la la' γ h => X.χ_add la la' γ (hle h)
    χ_fin := fun la => (X.χ_fin la).imp fun _ h => ⟨h.1, fun γ hγ => h.2 γ (hle hγ)⟩
    m := m
    m_pos := hm
    transv := htr }


section Adelic

variable (cj : E ≃ₐ[F] E)

def infU (h : W → W → E) : AdelicU F cj fr h →* GL (Fin n) (Inf𝔸 F ⊗[F] E) :=
  (Subgroup.subtype _).comp (MonoidHom.fst _ _)

def finU (h : W → W → E) : AdelicU F cj fr h →* GL (Fin n) (Fin𝔸 F ⊗[F] E) :=
  (Subgroup.subtype _).comp (MonoidHom.snd _ _)

def ratU (h : W → W → E) : Subgroup (AdelicU F cj fr h) :=
  (MonoidHom.range ((Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Inf𝔸 F ⊗[F] E).toRingHom).prod (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Fin𝔸 F ⊗[F] E).toRingHom))).comap
    ((infU fr cj h).prod (finU fr cj h))




end Adelic



end Compare

end GlobalTheory.DictPinCompare
end
end

section
noncomputable section

namespace GlobalTheory.DictPinCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase IsLatEmb IsModelOf IsOrthoFrame IsArchAt IsRatUnitary ratTo LatMark
  IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def formOf (V : HSp D) : V.V →ₛₗ[conjHom D.host.E] V.V →ₗ[D.host.E] D.host.E := V.hT

section Record

variable (T : Formalism.L2.Pj.Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ)

end Record

end GlobalTheory.DictPinCompare
end
end

section
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open GlobalTheory.XiDetCompare (Reads TrivRat TrivFix XiValC XiValAtC embOf Reaches)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def GenOff (bad : ℕ) (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)})

def ReadsId {K : IntermediateField ℚ ℂ} (χ : (AE D)ˣ →* Circle) (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K) : Prop :=
  ∀ 𝔠 x, GenOff bad 𝔠 x → ((B 𝔠 : K) : ℂ) = ((χ x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔠 : ℝ) : ℝ) : ℂ)

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

theorem DefinedMod.of_dvd {χ : (AE D)ˣ →* Circle} {m m' : ℕ} (h : DefinedMod χ m) (hd : m ∣ m') : DefinedMod χ m' := by
  intro x hx h1
  refine h x hx (AddSubgroup.closure_mono ?_ h1)
  rintro _ ⟨a, ha, o, ho, rfl⟩
  exact ⟨a, ha, o, Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hd) ho, rfl⟩

end Scalar

section Value

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
variable (V : HSp D) (hr : V.rank = r)

def iotaV (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι

def finR : GA D V →* GL (Fin r) (AdE D.host.F D.host.E) :=
  (Units.map (Matrix.reindexRingEquiv (AdE D.host.F D.host.E) (finCongr hr)).toMonoidHom).comp (finHom V)

def gramR : Matrix (Fin r) (Fin r) D.host.E := -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

def DictWith (Q : ∀ (g : ℕ) (lab : Fin g → D.host.E →+* ℂ)
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab) (ik : U.Comp → Fin F.n),
    (∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) → Prop) : Prop :=
  IsUnf U ∧ (∀ k, ModelW V hr (U.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U V hr dict (iotaV V hr ι) e F ik φ th x₀ ∧ Q g _ F ik φ

def IsDict : Prop := DictWith V hr U dict ι x₀ fun _ _ _ _ _ => True

def ValDict (c0 : ℂ) (xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ) (f : Rul Xo c) : Prop :=
  DictWith V hr U dict ι x₀ fun _ _ F ik φ => ∀ h γ : GA D V, MarkBy U V hr dict (iotaV V hr ι) F ik φ h γ →
    rdU U f (dict h).1 (dict h).2 = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

def Onto : Prop :=
  (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) ∧ (∀ k, ∃ h, (dict h).1 = k) ∧
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictLat U V hr dict (iotaV V hr ι) e F ik φ th x₀ →
      Function.Bijective ik ∧ ∀ ψ, (∀ k, ψ (ik k) = embOf (Unf.ofPj U) F ik φ k) →
        Reaches (finR V hr) (Unf.ofPj U) dict F ik ψ (gramR V hr) ι

variable {V hr U dict ι x₀} {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end One

section Diag

variable {V} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ V.rank} {dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {g : ℕ}

end Diag

section Compare

variable {V hr} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end Compare

theorem cXiVal_iff {c : Coeff l} (σ0 : c.F →+* ℂ) {Tup : Type} (d : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ (σ0.comp ((d t).eF.symm : (d t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ) :
    CXiVal V hr σ0 d U₂ dict₂ (iotaV V hr ι) x₀ xi ↔ ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧
      ∀ t, ValDict V hr (U₂ t) (dict₂ t) ι x₀ c0 (xi t) (d t).cδ := Iff.rfl

end Value

section Record

variable {D : D7} {T : CoreJ D} {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ) {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)
  (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)
  (hr : (T.V j (sig0 T.Q.c)).rank = D.R.r) (B : D.what₂.Tup → Ideal (𝓞 D.host.E) → c'.F)
  (epF : D.what₂.Tup → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E) → c'.F) (cond : ℕ) (hw : VVc c' lam)
  (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((sig0 c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
  (dict₂ : ∀ t, GA D (T.V j (sig0 T.Q.c)) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : D.what₂.Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ)

def Bound : Prop :=
  InR D j ∧ LawsJ T ∧ WeightPin j ka lam ∧ CharPin T Tt j ξ PQ ∧
    (∀ k, IsomEmb ((T.U j (sig0 T.Q.c)).X k).Gm ((T.U j (sig0 T.Q.c)).X k).ξ0 (T.Q.Dw j) (T.iota j)) ∧
    EquivPin j h (wtA ka) ∧
    (∀ t, (d t).I ≤ PQ t ∧ Squarefree (d t).pd ∧
      (∀ p : ℕ, p.Prime → p ∣ (d t).pd → Ideal.span {(p : 𝓞 D.host.E)} ⊔ PQ t ≠ ⊤) ∧ IsTwist (ξ t) (d t).pd) ∧
    (∀ t, bad t ≠ 0 ∧ DefinedMod (muRec Tt t j) (bad t)) ∧
    (∀ t, ClassesAt D.R.r T.Q.l.M (d t).l₂.M (bad t) (PQ t) (Lh t) (gam t) ∧ ∃ m : ℕ, 0 < m ∧ vol t = ((m : c'.F))⁻¹) ∧
    SpansMod (Mfr T.Q.l) β ∧ ∀ t, DatumVal T.Q.l (d t).l₂ (r_le_nV D) (ξ t) (PQ t) β (φ t)

def Ties : Prop :=
  ∀ t, Reads (xi t) (ξ t) ∧ ReadsId (chiSplit Tt t j) (bad t) (B t) ∧
    Onto _ hr (U₂ t) (dict₂ t) (T.iota j) (T.x₀ j (sig0 T.Q.c))

variable {Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi}


theorem Bound.nonempty (hB : Bound Tt j h ka lam PQ β Cl Lh gam vol ξ bad d φ) :
    Nonempty D.what₂.Tup ∧ ∀ t, Nonempty (Cl t) :=
  ⟨⟨D.what₂.mu0⟩, fun t => ((hB.2.2.2.2.2.2.2.2.1 t).1.1 (stdLat _ _) GlobalTheory.Survey.UnimodularStandardLattice.unimod_std
    (GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std _) (GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std _)).exists.elim fun k _ => ⟨k⟩⟩

variable (Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi)

end Record

end GlobalTheory.ClassTieCompare
end
end
