import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericFrameParameters

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

section Defs

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsGenFrame {c : ι} (X : FD.Data E r) (Rd : ℕ → Submodule K (A c))
    (rd : ℕ → A c → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : Prop :=
  x ∈ X.dom ∧ ∀ k, ∀ g ∈ Rd k, g ≠ 0 → rd k g x ≠ 0

def IsEvalAt {c : ι} (X : FD.Data E r) (Rd : ℕ → Submodule K (A c))
    (rd : ℕ → A c → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (P : Ω c →+* ℂ) : Prop :=
  ∀ k, ∀ f ∈ Rd k, ∀ g ∈ Rd k, ∀ a : Ω c, f = a • g → rd k f x = P a * rd k g x

structure IsReading (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι)
    (sg : K →+* ℂ) (X : FD.Data E r) (L : Wt X.Ψ r)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) : Prop where

  mem : ∀ k, ∀ f ∈ Rd k, f ∈ 𝒜 c (k • d.wL)

  mul_mem : ∀ k l, ∀ f ∈ Rd k, ∀ g ∈ Rd l, f * g ∈ Rd (k + l)

  ratio : ∀ a : Ω c, ∃ k, ∃ f ∈ Rd k, ∃ g ∈ Rd k, g ≠ 0 ∧ f = a • g

  sec : ∀ k, ∀ f ∈ Rd k, X.IsSec (k • L) (rd k f)
  add : ∀ k, ∀ f ∈ Rd k, ∀ g ∈ Rd k, ∀ x ∈ X.dom, rd k (f + g) x = rd k f x + rd k g x
  smul : ∀ k, ∀ f ∈ Rd k, ∀ a : K, ∀ x ∈ X.dom, rd k (a • f) x = sg a * rd k f x
  mul : ∀ k l, ∀ f ∈ Rd k, ∀ g ∈ Rd l, ∀ x ∈ X.dom, rd (k + l) (f * g) x = rd k f x * rd l g x

  onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x, IsGenFrame X Rd rd x ∧ IsEvalAt X Rd rd x P

  unram : ∀ x, IsGenFrame X Rd rd x → ∀ v : V (nd X), v ≠ 0 →
    ∃ k, ∃ f ∈ Rd k, ∃ g ∈ Rd k, g ≠ 0 ∧
      fderiv ℂ (fun z : V (nd X) => rd k f (cpt X x z) / rd k g (cpt X x z)) 0 v ≠ 0

def IsGenParam {D N : ℕ} (sg : K →+* ℂ) (t : TVar D N → ℂ) : Prop :=
  Function.Injective (MvPolynomial.eval₂Hom sg t : KTp K D N →+* ℂ)

def beAlg (d : T0.Data K ι Ω WT A) (c : ι) : A c := d.et c ^ 2 * d.ta1 c ^ d.n1

structure Common (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι)
    (sg : K →+* ℂ) (X : FD.Data E r) (Xa : ArchInM X) (hN : d.N + 1 = Xa.N)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) (t : TVar d.D d.N → ℂ) : Prop where
  evidence : IsReading 𝒜 d c sg X Xa.L Rd rd
  w_mem : ∀ j, d.w j c ∈ Rd 1
  w_rd : ∀ j, ∀ x ∈ X.dom, rd 1 (d.w j c) x = Xa.w (Fin.cast hN j) x
  n_eq : d.n1 = Xa.i * Xa.g0
  be_mem : beAlg d c ∈ Rd (2 * d.n1)
  be_rd : ∀ x ∈ X.dom, rd (2 * d.n1) (beAlg d c) x = Xa.et x ^ 2 * Xa.th1 x ^ d.n1
  param : IsGenParam sg t

example {D N : ℕ} (sg : K →+* ℂ) (e : KTf K D N →+* ℂ)
    (he : ∀ a : K, e (algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C a)) = sg a) :
    IsGenParam sg fun p : TVar D N => e (algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.X p)) := by
  have h : (MvPolynomial.eval₂Hom sg fun p : TVar D N =>
      e (algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.X p))) =
      e.comp (algebraMap (KTp K D N) (KTf K D N)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [he]
    · intro p; simp
  unfold IsGenParam
  rw [h]
  exact e.injective.comp (IsFractionRing.injective (KTp K D N) (KTf K D N))

end Defs

end

end GlobalTheory.IndefiniteRowSideFullHecke.GenericFrameParameters
