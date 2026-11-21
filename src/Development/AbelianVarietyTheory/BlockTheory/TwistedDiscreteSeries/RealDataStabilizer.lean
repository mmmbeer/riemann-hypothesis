import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult
  MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

variable {D : D7}

abbrev Bas (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Pol (S T : HSp D) : Type := MvPolynomial (FVar D T.rank S.rank) ℂ

abbrev MIdx (S T : HSp D) : Type := FVar D T.rank S.rank →₀ ℕ

abbrev cmp (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (θ τ) g

def entries (S : SPar) : Finset ℚ := S.image Prod.fst

def entry (S : SPar) (l : ℕ) : ℚ := ((entries S).sort (· ≥ ·)).getD l 0

def hw (S : SPar) (n : ℕ) (l : Fin n) : ℤ := ⌊entry S l - ((n : ℚ) + 1 - 2 * ((l : ℕ) + 1)) / 2⌋

def StrictInterlace (n : ℕ) (A B : Finset ℚ) : Prop :=
  ∃ (a : Fin (n + 1) → ℚ) (b : Fin n → ℚ), A = Finset.univ.image a ∧ B = Finset.univ.image b ∧
    ∀ i : Fin n, b i < a i.castSucc ∧ a i.succ < b i

section Pair

variable (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ)

def vacChar (g : GA D S) (h : GA D T) : ℂ :=
  ∏ τ, (cmp θ S τ g).det ^ ⌊e τ - (T.rank : ℚ) / 2⌋ * (cmp θ T τ h).det ^ (-⌊e τ - (S.rank : ℚ) / 2⌋)

def subst (g : GA D S) (h : GA D T) (x : FVar D T.rank S.rank) : Pol S T :=
  ∑ i, ∑ c, MvPolynomial.C (((BT x.1)⁻¹ * cmp θ T x.1 h * BT x.1) i x.2.1 * ((BS x.1)⁻¹ * cmp θ S x.1 g⁻¹ * BS x.1) x.2.2 c) *
    MvPolynomial.X (x.1, i, c)

def polAct (g : GA D S) (h : GA D T) : Pol S T →ₗ[ℂ] Pol S T :=
  vacChar θ e g h • (MvPolynomial.aeval (subst θ BS BT g h)).toLinearMap

variable (π : CoefA S) (π' : CoefA T)

abbrev Ker (π : CoefA S) (π' : CoefA T) : Type := Module.Dual ℂ π.W →ₗ[ℂ] π'.W →ₗ[ℂ] Pol S T

def mfact (α : MIdx S T) : ℝ := α.prod fun _ n => (n.factorial : ℝ)

def fock (Φ Φ' : Pol S T) : ℂ := ∑ α ∈ Φ.support, Φ.coeff α * star (Φ'.coeff α) * (mfact α : ℂ)

end Pair

def fp (V : HSp D) (g : GA D V) : GfC V := ⟨GlobalTheory.LevelNbhd.finPartG V g, GlobalTheory.LevelNbhd.finPartG_mem_GfC V g⟩

abbrev VFun {V : HSp D} (c : CoefA V) : Type := GfC V → Module.Dual ℂ c.W

def scal {V : HSp D} (c : CoefA V) (G : VFun c) (v : c.W) (h : GA D V) : ℂ := G (fp V h) (c.ρ h v)

def ratFin (V : HSp D) : Subgroup (GfC V) := ((GQ V).map (finHom V)).comap ((finHom V).comp (GfC V).subtype)

abbrev Cls (V : HSp D) (K : Subgroup (GfC V)) : Type := DoubleCoset.Quotient (ratFin V : Set (GfC V)) (K : Set (GfC V))

def stab (V : HSp D) (K : Subgroup (GfC V)) (x : GfC V) : Set (GfC V) := {γ | γ ∈ ratFin V ∧ x⁻¹ * γ * x ∈ K}

def ClassFin (V : HSp D) (K : Subgroup (GfC V)) : Prop := Finite (Cls V K) ∧ ∀ x, (stab V K x).Finite

def classSum {V : HSp D} (K : Subgroup (GfC V)) {M : Type} [AddCommGroup M] [Module ℂ M] (F : GfC V → M) : M :=
  ∑ᶠ c : Cls V K, ((stab V K c.out).ncard : ℂ)⁻¹ • F c.out

section Global

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T)

def pt (f : WO S T → ℂ) : Pol S T →ₗ[ℂ] (WO S T → ℂ) := pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f

variable {π : CoefA S} {π' : CoefA T}

def Th (om : Om S T) (f : WO S T → ℂ) (g : GA D S) (h : GA D T) : Pol S T →ₗ[ℂ] ℂ :=
  LinearMap.proj (0 : WO S T) ∘ₗ om (g, h) ∘ₗ pt ψ θ BS BT f

end Global

section Last

variable {V A L : HSp D} (o : OrthDec V A L) (π : CoefA V) (δ : CoefA A)

def per (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (φ : GA D V → ℂ) (φ' : GA D A → ℂ) : ℂ :=
  ∫ h in 𝓕, φ (o.emb (h, 1)) * φ' h ∂μ

end Last

section Chain

variable (P : TPar D) (θ : InfFam D) (X : ℕ → HSp D) {X' L : HSp D} (o : OrthDec (X D.R.m) X' L) (B : ∀ j, Bas (X j))

def eAt (j : ℕ) (τ : D.what₂.Tau) : ℚ := if h : j < D.R.m then P.e τ ⟨j, h⟩ else 0

abbrev act (j : ℕ) (g : GA D (X j)) (h : GA D (X (j + 1))) : Pol (X j) (X (j + 1)) →ₗ[ℂ] Pol (X j) (X (j + 1)) :=
  polAct θ (B j) (B (j + 1)) (eAt P j) g h

abbrev MForm (π₀ : CoefA (X 0)) (δ : CoefA X') : Type :=
  π₀.W →ₗ[ℂ] δ.W →ₗ[ℂ] MultilinearMap ℂ (fun j : Fin D.R.m => Pol (X j) (X (j + 1))) ℂ

def LL (π₀ : CoefA (X 0)) (δ : CoefA X') : Submodule ℂ (MForm X π₀ δ) where
  carrier := {l | ∀ (g : ∀ j, GA D (X j)) (h : GA D X'), (∀ j < D.R.m, g j ∈ GinfC (X j)) → h ∈ GinfC X' →
    g D.R.m = o.emb (h, 1) → ∀ v w Φ,
      l (π₀.ρ (g 0) v) (δ.ρ h w) (fun j => act P θ X B j (g j) (g (j + 1)) (Φ j)) = l v w Φ}
  zero_mem' := fun _ _ _ _ _ _ _ _ => rfl
  add_mem' := fun {a b} ha hb g h h1 h2 h3 v w Φ => by
    simp only [LinearMap.add_apply, _root_.add_apply, ha g h h1 h2 h3, hb g h h1 h2 h3]
  smul_mem' := fun c a ha g h h1 h2 h3 v w Φ => by
    simp only [LinearMap.smul_apply, _root_.smul_apply, ha g h h1 h2 h3]

variable {X} (π : ∀ j, CoefA (X j))

variable (ψ : AddChar (AF D.host.F) ℂ) (om : ∀ j, Om (X j) (X (j + 1))) (f : ∀ j, WO (X j) (X (j + 1)) → ℂ)

variable (μ : ∀ j, Measure (GA D (X j))) (𝓕 : ∀ j, Set (GA D (X j)))

abbrev WAll (X : ℕ → HSp D) : Type := ∀ j, WO (X j) (X (j + 1))

open Classical in

def liftAll (φ : GA D (X 0) → ℂ) (Ψ : WAll X → ℂ) (n : ℕ) : GA D (X n) → WAll X → ℂ :=
  Nat.rec (motive := fun j => GA D (X j) → WAll X → ℂ) (fun g => φ g • Ψ)
    (fun j M h w => ∫ g in 𝓕 j, om j (g, h) (fun x => M g (Function.update w j x)) 0 ∂(μ j)) n

open Classical in

def LiftAllConv (φ : GA D (X 0) → ℂ) (Ψ : WAll X → ℂ) : Prop :=
  ∀ j < D.R.m, ∀ h w,
    IntegrableOn (fun g => om j (g, h) (fun x => liftAll om μ 𝓕 φ Ψ j g (Function.update w j x)) 0) (𝓕 j) (μ j)

abbrev MAll (X : ℕ → HSp D) : Type := ∀ j : Fin D.R.m, MIdx (X j) (X (j + 1))

def mono (α : MAll X) (j : Fin D.R.m) : Pol (X j) (X (j + 1)) := MvPolynomial.monomial (α j) 1

end Chain

example : StrictInterlace 1 {3 / 2, -1 / 2} {0} :=
  ⟨![3 / 2, -1 / 2], ![0], by ext x; simp [Fin.exists_fin_two, eq_comm], by ext x; simp [eq_comm],
    fun i => by fin_cases i; norm_num⟩

example (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ) (g : GA D S) (h : GA D T) :
    polAct θ BS BT e g h 1 = vacChar θ e g h • (1 : Pol S T) := by simp [polAct]

end GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

end
