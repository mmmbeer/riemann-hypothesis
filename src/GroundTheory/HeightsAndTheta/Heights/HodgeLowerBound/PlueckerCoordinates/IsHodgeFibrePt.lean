import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsPlueckerCoord
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure RegData (P : Ideal (MRing ι)) (d : ℕ) (Bd : Set ((Σ k, ι k) → ℂ)) where

  nc : ℕ

  chart : Fin nc → SncChart P d Bd

  r1 : ℝ

  r3 : ℝ

  r2 : ℝ
  r1_pos : 0 < r1
  r1_lt_r3 : r1 < r3
  r3_lt_r2 : r3 < r2
  r2_lt_one : r2 < 1
  cover : ∀ z ∈ mcPts P, ∃ a, ∃ t : Fin d → ℂ, ‖t‖ ≤ r1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
    z = torusSmul c ((chart a).γ t)

  eta : Fin nc → (Fin d → ℂ) → ℝ
  eta_smooth : ∀ a, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eta a)
  eta_le : ∀ a t, eta a t ≤ 0
  le_eta : ∀ a t, -1 ≤ eta a t
  eta_inner : ∀ a t, ‖t‖ ≤ r1 → eta a t = 0
  eta_outer : ∀ a t, r3 ≤ ‖t‖ → eta a t = -1

  rho : ℝ → ℝ
  rho_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho
  rho_nonneg : ∀ s, 0 ≤ rho s
  rho_supp : ∀ s, rho s ≠ 0 → 1 / 2 ≤ s ∧ s ≤ 1
  rho_ne : ∃ s, rho s ≠ 0

  rho0 : ℝ → ℝ
  rho_contDiff_alt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho0
  rho_nonneg_alt : ∀ s, 0 ≤ rho0 s
  rho_even : ∀ s, rho0 (-s) = rho0 s
  rho_support_half : ∀ s, rho0 s ≠ 0 → |s| ≤ 1 / 2
  rho_exists_ne_zero : ∃ s, rho0 s ≠ 0

  Ce : ℝ
  Ce_pos : 0 < Ce

namespace RegData

variable {P : Ideal (MRing ι)} {d : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} (R : RegData P d Bd)

def InChart (a : Fin R.nc) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ t : Fin d → ℂ, ‖t‖ < R.r2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((R.chart a).γ t)

open Classical in

def coord (a : Fin R.nc) (z : (Σ k, ι k) → ℂ) : Fin d → ℂ :=
  if h : R.InChart a z then h.choose else 0

open Classical in

def active (z : (Σ k, ι k) → ℂ) : Finset (Fin R.nc) :=
  Finset.univ.filter fun a => R.InChart a z

def massRho : ℝ := ∫ x : ℂ, R.rho ‖x‖

def molli (t : ℝ) (ξ : Fin d → ℂ) : ℝ := ∏ i, R.rho (‖ξ i‖ / t) / (t ^ 2 * R.massRho)

def mollify (u : (Fin d → ℂ) → ℝ) (t : ℝ) (x : Fin d → ℂ) : ℝ :=
  ∫ ξ, u (x - ξ) * R.molli t ξ

def ell (t : ℝ) : ℝ := Real.log (1 / t)

def e1 (t : ℝ) : ℝ := R.Ce * (Real.log (ell t) / ell t + t)

def massRho0 : ℝ := ∫ s, R.rho0 s

def regMax (et : ℝ) (A : Finset (Fin R.nc)) (x : Fin R.nc → ℝ) : ℝ :=
  (∫ h : Fin R.nc → ℝ, (⨆ i : A, x i + et * h i) * ∏ i, R.rho0 (h i) / R.massRho0) + et / 2

def localReg (φ φ0 : ((Σ k, ι k) → ℂ) → ℝ) (a : Fin R.nc) (t : ℝ) (x : Fin d → ℂ) : ℝ :=
  R.mollify (fun x' => φ ((R.chart a).γ x')) t x - φ0 ((R.chart a).γ x)

def regDiff (φ φ0 : ((Σ k, ι k) → ℂ) → ℝ) (t : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  R.regMax (R.e1 t) (R.active z) fun a =>
    R.localReg φ φ0 a t (R.coord a z) + 4 * R.e1 t * R.eta a (R.coord a z)

def regWeight (φ φ0 : ((Σ k, ι k) → ℂ) → ℝ) (t : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  φ0 z + R.regDiff φ φ0 t z

end RegData

def IsSmoothExt (P : Ideal (MRing ι)) (f F : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
    (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → F (torusSmul c z) = F z) ∧ ∀ z ∈ mcPts P, F z = f z

open Classical in

def smoothExt (P : Ideal (MRing ι)) (f : ((Σ k, ι k) → ℂ) → ℝ) : ((Σ k, ι k) → ℂ) → ℝ :=
  if h : ∃ F, IsSmoothExt P f F then h.choose else fun _ => 0

theorem smoothExt_torus (P : Ideal (MRing ι)) (f : ((Σ k, ι k) → ℂ) → ℝ) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) : smoothExt P f (torusSmul c z) = smoothExt P f z := by
  classical
  unfold smoothExt
  split_ifs with h
  · exact h.choose_spec.2.1 c z hc
  · rfl

def twistLine (P : Ideal (MRing ι)) (A0 : HermLine ι) (f : ((Σ k, ι k) → ℂ) → ℝ) : HermLine ι where
  a := A0.a
  h z := A0.h z * Real.exp (smoothExt P f z)
  pos z hz := mul_pos (A0.pos z hz) (Real.exp_pos _)
  smul c z hc := by
    have h1 := smoothExt_torus P f c hc z
    have h2 := A0.smul c z hc
    rw [show (fun p => c p.1 * z p) = torusSmul c z from rfl] at h2 ⊢
    rw [h1, h2]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Generic

def vertNum (P : Ideal (MRing ι)) (n : ℕ) (deg : Fin n → K → ℤ) (f g : MRing ι) : ℝ := by
  classical
  exact (∑ᶠ V ∈ divSupp P f,
      if IsHorizontal V then 0 else (multAt (P ⊔ Ideal.span {f}) V : ℝ) * (geoNum n V deg : ℝ)) -
    ∑ᶠ V ∈ divSupp P g,
      if IsHorizontal V then 0 else (multAt (P ⊔ Ideal.span {g}) V : ℝ) * (geoNum n V deg : ℝ)

def topR (II : IntersectionSystem) (P : Ideal (MRing ι)) (n : ℕ) {r : ℕ} (c : Fin r → ℝ)
    (L : Fin r → HermLine ι) (S : Finset ℕ) (vb : ℕ → K → ℤ) (vf vg : ℕ → MRing ι) : ℝ := by
  classical
  exact ∑ s : Fin (n + 1) → Option (Fin r), (∏ a, (s a).elim 1 c) *
    if h : ∀ a, (s a).isSome then II K ι P (n + 1) (fun a => L ((s a).get (h a)))
    else ∑ p ∈ S, vertNum P n
        (fun a' => match s ((not_forall.1 h).choose.succAbove a') with
          | some i => (L i).a
          | none => vb p) (vf p) (vg p) * Real.log p

end Generic

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentDataHodge II Ψ K ι Ω E}

section FlagReg

def lastIdx (D : ComponentDataHodge II Ψ K ι Ω E) : Fin D.N :=
  ⟨D.N - 1, by have := D.two_le_N; omega⟩

end FlagReg

section Mu

def jIdx (D : ComponentDataHodge II Ψ K ι Ω E) : Fin D.N :=
  ⟨D.j - 1, by have := D.one_le_j; have := D.j_le; have := D.two_le_N; omega⟩

def fibreSub (D : ComponentDataHodge II Ψ K ι Ω E) (τ : Ψ) (bfr : Fin D.N → E τ) (z : (Σ k, ι k) → ℂ) :
    Submodule ℂ (Fin D.N → ℂ) :=
  Submodule.span ℂ {v | ∃ e ∈ D.F τ, ∃ a : Fin D.N → Ω, e = ∑ q, a q • bfr q ∧
    ∀ q, IsValueAt D.y (a q) z (v q)}

abbrev MuBlocks (D : ComponentDataHodge II Ψ K ι Ω E) : Type := K ⊕ (Ψ ⊕ Ψ)

def ιMu (P : PlueckerData D) : MuBlocks D → Type
  | Sum.inl k => ι k
  | Sum.inr (Sum.inl τ) => Fin (P.M τ (jIdx D))
  | Sum.inr (Sum.inr τ) => Fin (P.M τ (lastIdx D))

instance instFintypeιMu (P : PlueckerData D) : ∀ k, Fintype (ιMu P k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr (Sum.inl τ) => inferInstanceAs (Fintype (Fin (P.M τ (jIdx D))))
  | Sum.inr (Sum.inr τ) => inferInstanceAs (Fintype (Fin (P.M τ (lastIdx D))))

def zMu (P : PlueckerData D) (u : (Σ k : MuBlocks D, ιMu P k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => u ⟨Sum.inl p.1, p.2⟩

def wFMu (P : PlueckerData D) (u : (Σ k : MuBlocks D, ιMu P k) → ℂ) (τ : Ψ) : Fin (P.M τ (jIdx D)) → ℂ :=
  fun m => u ⟨Sum.inr (Sum.inl τ), m⟩

def wWMu (P : PlueckerData D) (u : (Σ k : MuBlocks D, ιMu P k) → ℂ) (τ : Ψ) : Fin (P.M τ (lastIdx D)) → ℂ :=
  fun m => u ⟨Sum.inr (Sum.inr τ), m⟩

def IsHodgeFibrePt (P : PlueckerData D) (τ : Ψ) (z : (Σ k, ι k) → ℂ) (wF : Fin (P.M τ (jIdx D)) → ℂ)
    (wW : Fin (P.M τ (lastIdx D)) → ℂ) : Prop :=
  ∃ (c : (k : K) → ι k) (f : Ω) (bfr : Fin D.N → E τ) (g : Matrix (Fin D.N) (Fin D.N) ℂ) (lF lW : ℂ),
    IsFrameOver D.y (D.W τ) c f bfr ∧ InFrameDomain D.y c f z ∧ g.det ≠ 0 ∧ lF ≠ 0 ∧ lW ≠ 0 ∧
    Submodule.span ℂ (Set.range fun a : Fin ((jIdx D : ℕ) + 1) => fun p =>
      firstCols g ((jIdx D : ℕ) + 1) (jIdx D).isLt p a) = fibreSub D τ bfr z ∧
    (∀ m, ∃ v, IsPlueckerCoord D.y c P.b (P.gen τ (jIdx D) m) bfr z
      (firstCols g ((jIdx D : ℕ) + 1) (jIdx D).isLt) v ∧ wF m = lF * v) ∧
    ∀ m, ∃ v, IsPlueckerCoord D.y c P.b (P.gen τ (lastIdx D) m) bfr z
      (firstCols g ((lastIdx D : ℕ) + 1) (lastIdx D).isLt) v ∧ wW m = lW * v

def muPts (P : PlueckerData D) : Set ((Σ k : MuBlocks D, ιMu P k) → ℂ) :=
  {u | zMu P u ∈ mcPts (mCoordIdeal D.y) ∧ ∀ τ, IsHodgeFibrePt P τ (zMu P u) (wFMu P u τ) (wWMu P u τ)}

def PXmu (P : PlueckerData D) : Ideal (MRing (ιMu P)) :=
  ⨅ u ∈ muPts P, RingHom.ker ((MvPolynomial.eval u).comp (MvPolynomial.map (Int.castRingHom ℂ)))

def BdMu (P : PlueckerData D) : Set ((Σ k : MuBlocks D, ιMu P k) → ℂ) := {u | zMu P u ∈ D.Bd}

def muDeg (D : ComponentDataHodge II Ψ K ι Ω E) : MuBlocks D → ℤ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr _) => 1

def muRefLine (P : PlueckerData D) : HermLine (ιMu P) :=
  HermLine.ofMetrics (fun k => fsMetric (ιMu P k)) (muDeg D)

def phMu (P : PlueckerData D) (u : (Σ k : MuBlocks D, ιMu P k) → ℂ) : ℝ :=
  ∑ τ, (Real.log (detNorm P τ (lastIdx D) (zMu P u) (wWMu P u τ)) -
    Real.log (detNorm P τ (jIdx D) (zMu P u) (wFMu P u τ)))

def phMuReg (P : PlueckerData D) (R : RegData (PXmu P) D.toComponentData.n (BdMu P)) (t : ℝ) :
    ((Σ k : MuBlocks D, ιMu P k) → ℂ) → ℝ :=
  fun u => R.regDiff (phMu P) (fun u => Real.log ((muRefLine P).h u)) t u

def muRegLine (P : PlueckerData D) (R : RegData (PXmu P) D.toComponentData.n (BdMu P)) (t : ℝ) :
    HermLine (ιMu P) :=
  twistLine (PXmu P) (muRefLine P) (phMuReg P R t)

def A'Mu (P : PlueckerData D) : HermLine (ιMu P) where
  a := Sum.elim D.a' 0
  h u := D.A'.h (zMu P u)
  pos u hu := D.A'.pos _ fun k => hu (Sum.inl k)
  smul c u hc := by
    have h := D.A'.smul (fun k => c (Sum.inl k)) (zMu P u) fun k => hc (Sum.inl k)
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one]
    rw [D.A'_deg] at h
    exact h

def liftMu (P : PlueckerData D) (f : MRing ι) : MRing (ιMu P) :=
  rename (fun p : Σ k, ι k => (⟨Sum.inl p.1, p.2⟩ : Σ k : MuBlocks D, ιMu P k)) f

def SB (D : ComponentDataHodge II Ψ K ι Ω E) (B : ℕ) : Finset ℕ := D.S.filter (· ≤ B)

def arLimFun (P : PlueckerData D) (R : RegData (PXmu P) D.toComponentData.n (BdMu P)) (B : ℕ) (t : ℝ) : ℝ :=
  topR II (PXmu P) D.toComponentData.n ![1] ![muRegLine P R t] (SB D B)
    (fun p => Sum.elim (D.vdeg p) 0) (fun p => liftMu P (D.vnum p)) (fun p => liftMu P (D.vden p))

def arLim (P : PlueckerData D) (R : RegData (PXmu P) D.toComponentData.n (BdMu P)) (B : ℕ) : ℝ :=
  limUnder (𝓝[>] 0) (arLimFun P R B)

def ArLimExists.Statement (P : PlueckerData D) (R : RegData (PXmu P) D.toComponentData.n (BdMu P))
    (B : ℕ) : Prop :=
  ∃ L, Tendsto (arLimFun P R B) (𝓝[>] 0) (𝓝 L)

def degMu (P : PlueckerData D) : ℝ := geomDeg (PXmu P) (muRefLine P) D.toComponentData.n

end Mu

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end
