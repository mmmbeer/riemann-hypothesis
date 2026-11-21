import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
import Development.WeilBound.CoreStatements.PadicHodgeComparison.UniqueSaturation.DescentOffPrescribedPlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.NoAccumS
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
import Mathlib

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

section Pi

variable {a b : ℕ}

def piG (D : Dom E a b) (π : CuspSub E a) (ι : Type) [Fintype ι] : Submodule ℂ (Hs (ι := ι) D) :=
  (Submodule.span ℂ {f | ∀ i, ∃ ψ ∈ π.V, ∃ u : ℝ → ℂ, Continuous u ∧ HasCompactSupport u ∧
    (f i : H E a b → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (logAbs x.1.val.det)}).topologicalClosure

def TwTrG (μ : Measure (H E a b)) (π : CuspSub E a) (φ : H E a b → ℂ) (t : ℂ) : Prop :=
  ∃ L : π.V →ₗ[ℂ] π.V, (∀ (ψ : π.V) x, (L ψ).1.1 x = ∫ y, φ y * ψ.1.1 (thetaA E a (x * y.1)) ∂μ) ∧
    FiniteDimensional ℂ (LinearMap.range L) ∧
    t = LinearMap.trace ℂ (LinearMap.range L) (L.restrict fun x _ => LinearMap.mem_range_self L x)

def FinOnG (μ : Measure (H E a b)) (π : CuspSub E a) (φ : H E a b → ℂ) : Prop :=
  ∃ W : Submodule ℂ (Sm E a), W ≤ π.V ∧ FiniteDimensional ℂ W ∧ ∀ u : ℝ → ℂ, Continuous u → ∀ ψ ∈ π.V,
    ∃ ψ' ∈ W, ∀ x, ψ'.1 x = ∫ y, φ y * u (logAbs y.1.val.det) * ψ.1 (x * y.1) ∂μ

def GrowthPiAt (D : Dom E a b) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (π : CuspSub E a) : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ)
    (r₀ r₁ ε : ℝ), IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOnG D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ →
    0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ) (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)) (t : ℂ),
      IsTestM Φ → IsROp D Φ (T₁ * U * T₂) → (∀ f ∈ piG D π ι, U f ∈ piG D π ι) → (∀ f ∈ (piG D π ι)ᗮ, U f ∈ (piG D π ι)ᗮ) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → TwTrG D.μ π (trM Φ M) t →
      ‖ellSum2 μ₁ μ₂ (trM Φ M) - t / 2‖ ≤ C * (1 + k) ^ N * ‖U ∘L (piG D π ι)ᗮ.subtypeL‖ + C * ‖U‖ * ε ^ k

end Pi

structure Frame0 (hR : Rd.ReadLimit) (π : CuspSub E n) : Type 1 where
  lam : InfinitePlace E → DomWeight n
  hlam : ∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))
  μ : HChar E
  e : InfinitePlace E → ℤ
  hμ : IsMu μ e
  Sec : Set (Pl E)
  hSec : IsSection Sec
  d₀ : LocData E n
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  Bad₀ : d₀.Bad = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → (∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w
  K'_lev : ∀ w ∈ d₀.S₀, IsLevel (MonoidHom.id _) (KL n w) ((d₀.K' w).subgroupOf (UL n w))
  τ : ∀ w : Pl E, SmIrr (GLw n w)
  hτ : ∀ w, π.IsLocComp w (τ w)
  τ_fix : ∀ w ∈ d₀.S₀, ∃ y ∈ fixed (τ w).ρ (d₀.K' w), y ≠ 0
  u₁ : ∀ a, GL (Fin a) E
  u₂ : ∀ a, GL (Fin (n - a)) E
  hu : ∀ a, IsTransl (u₁ a) ∧ IsTransl (u₂ a)
  C : Chain μ e lam
  A : ∀ i : C.ι, Arch E (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) (C.μG (C.a i)) (C.μG (n - C.a i)) (C.νC (C.a i)) (C.νC (n - C.a i))
  K : ∀ w : Pl E, Subgroup (GLw n w)
  hK : F5.IsLevel K
  Kc : ∀ w, IsCompact (K w : Set (GLw n w))
  K_good : ∀ w : Pl E, (∀ u ∈ d₀.S₀ ∪ d₀.Bad, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) →
    K w = GlobalTheory.LFun.KGL w n
  K_bad : ∀ a (ha : a ≤ n), ∀ w ∈ d₀.S₀ ∪ d₀.Bad, ∀ m X, blk (Nat.add_sub_of_le ha) w m X ∈ K w →
    m ∈ d₀.L a w ∧ μ.loc w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1
  K_conj : ∀ a (ha : a ≤ n), ∀ w ∈ d₀.S₀ ∪ d₀.Bad, IsSplitAt w → ∀ u, ConjPl w u → ∀ m X, blk (Nat.add_sub_of_le ha) u m X ∈ K u →
    μ.loc u (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
      ∃ m' ∈ d₀.L a w, embW a u m.1 = embT a w m'.1 ∧ embW (n - a) u m.2 = embT (n - a) w m'.2
  i₀ : C.ι
  a₀ : C.a i₀ = n
  c₀ : C.c i₀ ≠ 0
  mid : ∀ i, i ≠ i₀ → 0 < C.a i ∧ C.a i < n
  lefM : (A i₀).Ma = fun v => lefE _ (C.l₁ i₀ v).w
  lefT : ∀ v, HEq ((A i₀).Ta v) (lefT _ (C.l₁ i₀ v).w)
  gp : GrowthPiAt (A i₀).D (C.μG (C.a i₀)) (C.μG (n - C.a i₀)) (a₀.symm ▸ π)
  L_fix : ∃ ψ ∈ (a₀.symm ▸ π : CuspSub E (C.a i₀)).V, ψ ≠ 0 ∧ ∀ k ∈ lev₁ Sec d₀ (C.a i₀), finRep E _ k ψ = ψ
  Wx₁ : Submodule ℂ (Kinf E (C.a i₀) → ℂ)
  Wx₂ : Submodule ℂ (Kinf E (n - C.a i₀) → ℂ)
  hWx : FiniteDimensional ℂ Wx₁ ∧ FiniteDimensional ℂ Wx₂ ∧ (fun _ => 1) ∈ Wx₁ ∧ (fun _ => 1) ∈ Wx₂
  pack : Rd.B.PackAt E _ _ (A i₀).Ma (A i₀).Mb Wx₁ Wx₂
  Ωx₁ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))
  Ωx₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))
  hΩx : KTypes E Ωx₁ ∧ KTypes E Ωx₂
  Θx₁ : Subgroup (GL (Fin (C.a i₀)) (Af E)) → Subgroup (GL (Fin (n - C.a i₀)) (Af E)) → ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))
  Θx₂ : Subgroup (GL (Fin (C.a i₀)) (Af E)) → Subgroup (GL (Fin (n - C.a i₀)) (Af E)) → ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))
  hx : ∀ (K₁ : Subgroup (GL (Fin (C.a i₀)) (Af E))) (K₂ : Subgroup (GL (Fin (n - C.a i₀)) (Af E))),
    IsOpen (K₁ : Set (GL (Fin (C.a i₀)) (Af E))) → IsOpen (K₂ : Set (GL (Fin (n - C.a i₀)) (Af E))) →
    Levels E (Θx₁ K₁ K₂) ∧ Levels E (Θx₂ K₁ K₂) ∧ SpectralAccumulation.LimAtS E _ _ Wx₁ Wx₂ Ωx₁ Ωx₂ K₁ K₂ (Θx₁ K₁ K₂) (Θx₂ K₁ K₂)
  W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)
  hW : ∀ N, FiniteDimensional ℂ (W N)
  W_join : ∀ (i : C.ι) (s₁ : Tr E (C.a i)) (s₂ : Tr E (n - C.a i)) Pa Pb (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ rlΩ₁ hR E _ _ (A i).Ma (A i).Mb M ∪ {W' | i = i₀ ∧ W' ∈ Ωx₁ M}, HasType K' W' V) →
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ rlΩ₂ hR E _ _ (A i).Ma (A i).Mb M ∪ {W' | i = i₀ ∧ W' ∈ Ωx₂ M}, HasType K' W' V) →
    ∀ j, HasKType (W (D.N j)) (D.V j)

namespace Frame0

variable {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π)

abbrev π' : CuspSub E (F₀.C.a F₀.i₀) := F₀.a₀.symm ▸ π

structure Cand (d : LocData E n) (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) : Prop where
  ctx : Ctx F₀.μ s₁ s₂ Pa Pb D
  leaves₁ : s₁.AllLeaves fun M V => M = 0 ∨ ∃ K' ∈ rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) M ∪
    {K' | i = F₀.i₀ ∧ K' ∈ F₀.Θx₁ (lev₁ F₀.Sec d (F₀.C.a F₀.i₀)) (lev₂ F₀.Sec d (F₀.C.a F₀.i₀)) M}, ∃ W' ∈ rlΩ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb M ∪ {W' | i = F₀.i₀ ∧ W' ∈ F₀.Ωx₁ M}, HasType K' W' V
  leaves₂ : s₂.AllLeaves fun M V => M = 0 ∨ ∃ K' ∈ rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) M ∪
    {K' | i = F₀.i₀ ∧ K' ∈ F₀.Θx₂ (lev₁ F₀.Sec d (F₀.C.a F₀.i₀)) (lev₂ F₀.Sec d (F₀.C.a F₀.i₀)) M}, ∃ W' ∈ rlΩ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb M ∪ {W' | i = F₀.i₀ ∧ W' ∈ F₀.Ωx₂ M}, HasType K' W' V
  inf₁ : ∀ τ, HasInfCharGL s₁.space τ (mOf (F₀.A i).χa τ)
  inf₂ : ∀ τ, HasInfCharGL s₂.space τ (mOf (F₀.A i).χb τ)
  vec : ∃ G ∈ pairSpace s₁.space s₂.space, G ≠ 0 ∧ ∃ W₁ W₂, TypeH (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) W₁ W₂ G

end Frame0

end PositivityTheory.Rg.BcB.F.FrE

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def RF_same {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop :=
  d.S₀ = F₀.d₀.S₀ ∧ d.Bad = F₀.d₀.Bad ∧ d.μ = F₀.d₀.μ ∧ d.ϖ = F₀.d₀.ϖ ∧ d.K' = F₀.d₀.K' ∧ d.X = F₀.d₀.X ∧
  d.L = F₀.d₀.L ∧ d.fix = F₀.d₀.fix ∧ d.KB = F₀.d₀.KB

def RF_T_in {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (Z : Finset (Pl E)) (βx : Pl E → Fin (n / 2) → ℂˣ) : Prop :=
  ∀ w ∈ d.T, w ∈ F₀.Sec ∧ ¬ IsSplitAt w ∧ w ∉ Z ∧ IsWitt n w (d.b w) ∧ IsExtOf2 π w (βx w)

def valU (d : LocData E n) (w : Pl E) (β : Fin (n / 2) → ℂˣ) : ℂ := (d.c w).sum fun x t => t * (dlt n w (lOf x) * pw β (lOf x))

def valG (d : LocData E n) (a : ℕ) (w : Pl E) (s : Finset (Fin (n / 2))) (h : LocData.admitted n a s) (ξa : Fin a → ℂˣ)
    (ξb : Fin (n - a) → ℂˣ) : ℂ :=
  (d.c w).sum fun x t => t * (-qh w) ^ (-vRes n a (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)

def RF_choiceT {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop :=
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ d.T, ∀ s (h : LocData.admitted n (F₀.C.a i) s) ξa ξb,
  JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → valG d _ w s h ξa ξb ≠ 0 → N3.Mono ξa ∧ N3.Mono ξb ∧ (CG.mk π).HasSat w
    ((Finset.univ.val.map ξa).map (· * (F₀.μ ^ (n - F₀.C.a i)).val w) + (Finset.univ.val.map ξb).map (· * (F₀.μ ^ F₀.C.a i).val w))

def RF_choiceM {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (m : ℕ) : Prop :=
  ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ d.T, Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 (F₀.C.a i) (n - F₀.C.a i) w)) ≤ m

def RF_choiceP {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (m : ℕ) (βx : Pl E → Fin (n / 2) → ℂˣ) :
    Prop :=
  ∀ (Pa : Pre E (F₀.C.a F₀.i₀)) (Pb : Pre E (n - F₀.C.a F₀.i₀)), IsOne Pa F₀.π' → Pb.c = 0 → ∀ w ∈ d.T,
    Module.finrank ℂ ↥(fixed (pairAt Pa Pb w) (I2 _ _ w)) ≤ m ∧ ∀ s (h : LocData.admitted n (F₀.C.a F₀.i₀) s) ξb, ∃ ξ,
      N3.Mono ξ ∧ (∀ x : Fin n → ℤ, pw ξ (restr x _ h.2.1) = pw (βx w) (lOf x)) ∧ JEig Pa Pb w (F₀.d₀.ϖ w) ξ ξb ∧
        valG d _ w s h ξ ξb = 1 ∧ ∀ ξ', JEig Pa Pb w (F₀.d₀.ϖ w) ξ' ξb → valG d _ w s h ξ' ξb ≠ 0 → ξ' = ξ

def RF_eP {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop :=
  ∀ w ∈ d.S₀, ∃ v₀ ∈ fixed (F₀.τ w).ρ (d.K' w), ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧ ∀ v ∈ fixed (F₀.τ w).ρ (d.K' w),
    hk (F₀.τ w).ρ (d.K' w) (d.e w) v = (((d.K' w).relIndex (GlobalTheory.LFun.KGL w n) : ℕ) : ℂ) • l v • v₀

def RF_choiceU {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (m : ℕ) (βx : Pl E → Fin (n / 2) → ℂˣ) (fam : U.UFam F₀.Sec F₀.lam d.KU) : Prop :=
  ∀ j : fam.ι, (∀ w ∈ d.S₀, locOp (fam.σ j w) (d.KU w) (d.g₀ w) ≠ 0 → Comp (fam.π j) w (F₀.τ w)) ∧
    ∀ w ∈ d.T, Module.finrank ℂ ↥(fixed (fam.σ j w).ρ (d.KU w)) ≤ m ∧ ∀ β : Fin (n / 2) → ℂˣ,
      (∃ y ∈ fixed (fam.σ j w).ρ (iwU n w (d.b w)), y ≠ 0 ∧ ∀ l : Fin (n / 2) → ℤ, Cone l →
        levOp (fam.σ j w).ρ (KL n w) (iwU n w (d.b w)) (fU n w (d.b w) (d.ϖ w) l) LinearMap.id y =
          ((((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * dlt n w l * pw β l) • y) → valU d w β ≠ 0 → β = βx w

def DOut {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) (D : Pre E n) : Prop :=
  (∀ v : InfinitePlace E, ∑ i, D.m i v.embedding = infOfWeight (F₀.lam v)) ∧
  (∀ τ m, π.HasInfChar τ m → ∑ i, D.m i τ = m) ∧ SplitLike D π ∧
  (∀ w ∈ d.T, ∀ B, (CG.mk π).HasSat w B → D.Sat w B) ∧ (∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (F₀.K w)) ∧
  ∀ i, HasKType (F₀.W (D.N i)) (D.V i)

def RF_sep {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (d : LocData E n) : Prop := ∀ D : Pre E n, DOut F₀ d D → IsOne D π

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RunFrame {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π) (Z T₀ : Finset (Pl E)) : Type 1 where
  d : LocData E n
  same : RF_same F₀ d
  m : ℕ
  m_pos : 1 ≤ m
  ok : d.Ok
  mok : MLM.MOk d
  T_ne : d.T.Nonempty
  T_sup : T₀ ⊆ d.T
  βx : Pl E → Fin (n / 2) → ℂˣ
  T_in : RF_T_in F₀ d Z βx
  levOff : U.LevelOff F₀.Sec d.B d.KU
  fam : U.UFam F₀.Sec F₀.lam d.KU
  R : U.UMod fam d.B (d.gU m)
  choiceT : RF_choiceT F₀ d
  choiceM : RF_choiceM F₀ d m
  choiceP : RF_choiceP F₀ d m βx
  eP : RF_eP F₀ d
  choiceU : RF_choiceU F₀ d m βx fam
  sep : RF_sep F₀ d

end PositivityTheory.Rg.BcB.F.FrE

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace RunFrame

variable {hR : Rd.ReadLimit} {π : CuspSub E n} {Z T₀ : Finset (Pl E)} {F₀ : Frame0 hR π} (F : RunFrame F₀ Z T₀)

abbrev κ : Type := ∀ w : F.d.P, F.d.kap w

abbrev B (i : F₀.C.ι) : Block E := (F₀.A i).blk F.κ

def ψ (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) : Matrix F.κ F.κ (Hf E (F₀.C.a i) (n - F₀.C.a i) → ℂ) :=
  fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) L

def ptL (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) : PT (F.B i) :=
  (F₀.A i).pt (fun _ => []) (fun _ => []) (F.ψ i L) (sizeOf (F.ψ i L))

def t₀ (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.eL _)

def β (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.betaL _ (F₀.C.le i))

def t₁ (i : F₀.C.ι) : PT (F.B i) := F.ptL i (F.d.fixL _)

def t₂ (i : F₀.C.ι) : PT (F.B i) :=
  (F₀.A i).pt (fun _ => []) (fun _ => []) (rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (F.d.eL _)))
    (sizeOf (rt (F₀.u₁ _) (F₀.u₂ _) (F.ψ i (F.d.eL _))))

abbrev Γ : Type := Unit ⊕ (F₀.C.ι × InfinitePlace E × Bool × ℕ × Bool) ⊕ ({w : Pl E // w ∈ F₀.Sec ∧ F.d.Good w} × ℕ × Bool)

def dval (_ : RunFrame F₀ Z T₀) (x : F₀.C.ι × InfinitePlace E × Bool × ℕ × Bool) : ℂ :=
  if x.2.2.2.2 then zVal [(x.2.2.1, x.2.2.2.1)] ((F₀.A x.1).χb x.2.1) else zVal [(x.2.2.1, x.2.2.2.1)] ((F₀.A x.1).χa x.2.1)

def tD (i : F₀.C.ι) (v : InfinitePlace E) (s : Bool) (m : ℕ) (side : Bool) : PT (F.B i) :=
  (F₀.A i).pt (fun v' => if v' = v ∧ side = false then [(s, m)] else []) (fun v' => if v' = v ∧ side = true then [(s, m)] else [])
    (F.ψ i (F.d.eL _)) (sizeOf (F.ψ i (F.d.eL _)))

def g : F.Γ → ∀ i, BGen (F.B i)
  | .inl _, i => .inr (F.t₀ i)
  | .inr (.inl x), i => if i = x.1 then .inr (F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) else .inl (F.dval x)
  | .inr (.inr x), i => .inr (F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2))

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
instance instIPS_FB (i : F₀.C.ι) : InnerProductSpace ℂ (F.B i).Hb := inferInstance
instance instCS_FB (i : F₀.C.ι) : CompleteSpace (F.B i).Hb := inferInstance

structure Struct : Prop where
  ok : ∀ x i, (F.g x i).Ok
  βok : ∀ i, (F.β i).Ok
  tok : ∀ i, (F.t₁ i).Ok ∧ (F.t₂ i).Ok
  comm : ∀ x y i, Commute (F.g x i).op (F.g y i).op
  commStar : ∀ x y i, Commute (F.g x i).op (star (F.g y i).op)
  βcomm : ∀ i x, Commute (F.β i).op (F.g x i).op ∧ Commute (F.β i).op (star (F.g x i).op)

end RunFrame

section Frame

variable {hR : Rd.ReadLimit} {π : CuspSub E n} {Z T₀ : Finset (Pl E)} {F₀ : Frame0 hR π} (F : RunFrame F₀ Z T₀)

def gl (i : F₀.C.ι) (p : F.Γ × Bool) : BGen (F.B i) := if p.2 then (F.g p.1 i).adj else F.g p.1 i

def bw (i : F₀.C.ι) (w : List (F.Γ × Bool)) : List (BGen (F.B i)) := List.replicate F.m (Sum.inr (F.β i)) ++ w.map (gl F i)

def tw (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) : PT (F.B i) :=
  BGen.wd (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten) (F.t₂ i)

end Frame

end PositivityTheory.Rg.BcB.F.FrE

end
end

section
noncomputable section

namespace PositivityTheory.Rg.BcB.F.FrE

abbrev Tup {ι : Type} (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)]
    (J : Type) : Type := (∀ s, H s →L[ℂ] H s) × (J → ℂ) × ℂ

end PositivityTheory.Rg.BcB.F.FrE

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

section Frame

variable {hR : Rd.ReadLimit} {π : CuspSub E n} {Z T₀ : Finset (Pl E)} {F₀ : Frame0 hR π} (F : RunFrame F₀ Z T₀)

end Frame

def Hyp (π : CuspSub E n) : Prop := (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.PolarizedPair π (GlobalTheory.GalOfCusp.quadChar E ^ n) ∧
  (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) ∧ InertBC π

def All (P : ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
    (Z T₀ : Finset (Pl E)) (F₀ : Frame0 hR π), RunFrame F₀ Z T₀ → Prop) : Prop :=
  ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
    Hyp π → ∀ (Z T₀ : Finset (Pl E)) (F₀ : Frame0 hR π) (F : RunFrame F₀ Z T₀), P hR E n π Z T₀ F₀ F

def FrameEx : Prop := ∀ (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : CuspSub E n, Hyp π → ∀ (F₀ : Frame0 hR π) (Z T₀ : Finset (Pl E)), Disjoint T₀ Z → (∀ w ∈ T₀, ¬ IsSplitAt w) →
    Nonempty (RunFrame F₀ Z T₀)

end PositivityTheory.Rg.BcB.F.FrE

end
end
