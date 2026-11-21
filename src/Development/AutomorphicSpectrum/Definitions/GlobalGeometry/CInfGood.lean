import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ChartSpec
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Forms

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev WZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : WZ E) : Ix Dw → ℤ
  | none => 0
  | some x => a (x.1, x.2)

def secWZ {K : Type} [Field K] {ι : Type} [Fintype ι] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop) (e : ι → ℤ) :
    Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
    f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) : f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f :=
  ⟨fun ⟨g, hg, e⟩ => e ▸ ⟨g.2, hg⟩, fun h => ⟨⟨f, h.1⟩, h.2, rfl⟩⟩

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : secZ Xo c (fun x => (a x : ℤ)) = sec Xo c a 0 := by
  have h : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      (∏ i, ((t i ^ exZ Dw (fun x => (a x : ℤ)) i : Sˣ) : S)) = wchar (ex Dw a 0) t := by
    intro S _ t
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, ex]
  ext f
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun t => forall_congr' fun y => forall_congr' fun y' =>
    forall_congr' fun _ => ?_)
  rw [h]

variable {Xo c} in
open Classical in

def laZ {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : WZ E) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ))


variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ))


variable {Xo c}

def evL (h : GenFrEx Xo c) (Z : Comp Xo c) : Rul Xo c →ₗ[c.F] Om Z :=
  evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)

theorem evL_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : evL h Z f = evC h Z f := rfl

def cuspOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule c.F (Rul Xo c) :=
  cuspZ Xo c U a ⊓ ⨅ (Z' : Comp Xo c) (_ : Z' ≠ Z), LinearMap.ker (evL h Z')

def latOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule (𝓞 c.F) (Rul Xo c) :=
  latIn (cuspOn U h a Z) (valSet Xo c (algCls Xo c)) isVal_valSet

def volL (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) (Dn : ℕ) : ℝ :=
  limsup (fun n : ℕ => (Dn.factorial : ℝ) * (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Dn) atTop

def lieFacZ (Dw : Datum H) (x : ℝ) (a : WZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

variable {D : D7} (W : HSp D) (dict : ∀ σ, GA D W → Σ k, Frame ((U σ).X k).Ψ r)

def ipAll (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  ∫ q, jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) f q * conj (jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) g q) ∂(muQ1 W)

open Classical in

def ipOn (x : ℝ) (a : WZ E) (e : Rul Xo c) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g / ipAll U W dict (goodOf c σ) e e
  if GoodEmb c σ then z else conj z

open Classical in

def ipGl (x : ℝ) (a : WZ E) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g
  if GoodEmb c σ then z else conj z

end Forms

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Numbers

open Formalism.BasicNotions Formalism.MainNotions
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb)

variable (D : D7) (i : Fin D.R.m)

def jp : ℕ := D.R.m - ((i : ℕ) + 1)

def pp : ℕ := (D.R.sigW ((i : ℕ) + 1)).1


def anc : ℕ := D.R.k - 2

def Dn : ℕ := D.R.f * D.R.r.choose 2

def entZ {N : ℕ} (v : Fin N → ℝ) (n : ℕ) : ℤ := if h : n < N then ⌊v ⟨n, h⟩⌋ else 0

open Classical in

def wtZ' (lam : D.what₂.Tau → Fin D.R.r → ℝ) : WZ D.host.E := fun x =>
  ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t ∧ x.2 < pp D i then entZ (lam t) x.2 else 0) +
    if x.1 = conjEmb (DV.tauEmb D t) ∧ x.2 < jp D i then -entZ (lam t) (D.R.r - 1 - x.2) else 0)

end Numbers

section Geo

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure SharpGeo (Q : Par D) (M : ℕ) : Type 1 where
  l : Level Q.H
  c : Coeff l
  Xo : ∀ i : Fin D.R.m, Moduli (Q.Dw ((i : ℕ) + 1)) l
  U : ∀ i (σ : c.F →+* ℂ), Unf (Xo i) c σ D.R.r
  dict : ∀ (i : Fin D.R.m) σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U i σ).X k).Ψ D.R.r

  e : ∀ i, Comp (Xo i) c → Rul (Xo i) c
  gen : ∀ i, GenFrEx (Xo i) c
  pins : Q.Pins
  level : l.M = M ∧ l.A = 1 ∧ l.Mb ≤ Q.l.Mb
  field : Q.c.F ≤ c.F

  comps : ∀ i, Nat.card (Comp (Xo i) c) = Fintype.card (U i c.F.val.toRingHom).Comp
  genT : ∀ i, GenFromTest (Xo i) c (gen i)
  evalWD : ∀ i, EvalWD (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z)
  unf : ∀ i σ, GoodEmb c σ → IsUnf (U i σ)
  unTest : ∀ i σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt (Xo i) c S) (fun φ y z => FrMap φ y z) ((U i σ).un k x)
  chiTriv : ∀ i σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U i σ).X k).Γ,
    ((U i σ).X k).χ (laU (U i σ) a n k) γ = 1

  dictU : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W ((i : ℕ) + 1)) l.M Kf ∧
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W ((i : ℕ) + 1)) (dict i σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U i σ).X (dict i σ g).1).Gm (dict i σ g).2 τ k‖ = 1
  modelW : ∀ (i : Fin D.R.m) σ, GoodEmb c σ → ∃ hr : (D.sp.W ((i : ℕ) + 1)).rank = D.R.r,
    ∀ k, ModelW (D.sp.W ((i : ℕ) + 1)) hr ((U i σ).X k)
  xiAbs : ∀ i σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U i σ).X k).ξ0‖ = xiR D
  finVol : ∀ i : Fin D.R.m, FinVol (D.sp.W ((i : ℕ) + 1))
  ptNe : ∀ i, IntFrNe (Xo i) c (algCls (Xo i) c)
  intAll : ∀ i, IntAll (Xo i) c
  e_sec : ∀ i Z, e i Z ∈ sec (Xo i) c 0 0
  e_val : ∀ i Z, evC (gen i) Z (e i Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC (gen i) Z' (e i Z) = 0

theorem SharpGeo.card_pos {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : 0 < Nat.card (Comp (S.Xo i) S.c) := by
  rw [S.comps i]
  exact Fintype.card_pos_iff.mpr ⟨(S.dict i _ 1).1⟩

instance SharpGeo.ne {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : Nonempty (Comp (S.Xo i) S.c) :=
  (Nat.card_pos_iff.mp (S.card_pos i)).1

instance SharpGeo.fin {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) : Fintype (Comp (S.Xo i) S.c) :=
  @Fintype.ofFinite _ (Nat.card_pos_iff.mp (S.card_pos i)).2

variable {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m)

abbrev RW (D : D7) : Type := D.what₂.Tau → Fin D.R.r → ℝ

abbrev Cmp : Type := Comp (S.Xo i) S.c

abbrev latW (lam : RW D) (Z : Cmp S i) : Submodule (𝓞 S.c.F) (Rul (S.Xo i) S.c) :=
  latOn (S.U i) (S.gen i) (wtZ' D i lam) Z

abbrev ipW (lam : RW D) (Z : Cmp S i) :
    (S.c.F →+* ℂ) → Rul (S.Xo i) S.c → Rul (S.Xo i) S.c → ℂ :=
  ipOn (S.U i) (D.sp.W ((i : ℕ) + 1)) (S.dict i) (xiR D) (wtZ' D i lam) (S.e i Z)

def degC (uT : RW D) (Z : Cmp S i) : ℝ := degL S.c.F (latW S i uT Z) (ipW S i uT Z)

def volC (up : RW D) (Z : Cmp S i) : ℝ := volL (S.U i) (S.gen i) (wtZ' D i up) Z (Dn D)

structure MbarIn (up : RW D) where
  top : Cmp S i → ℚ → ℝ
  dg : Cmp S i → ℚ → ℝ
  dg_lim : ∀ Z, Tendsto (dg Z) (𝓝[>] 0) (𝓝 (volC S i up Z))
  conv : ∀ Z, ∃ y, Tendsto (fun s => top Z s / (((Dn D : ℝ) + 1) * dg Z s)) (𝓝[>] 0) (𝓝 y)

def slC {up : RW D} (B : MbarIn S i up) (Z : Cmp S i) : ℝ :=
  limUnder (𝓝[>] (0 : ℚ)) fun s => B.top Z s / (((Dn D : ℝ) + 1) * B.dg Z s)


def rndDown {K : Type} [Field K] (la : HeightOneSpectrum (𝓞 K)) (q : ℕ) (m : ℝ) : ℝ :=
  (⌊(multiplicity la.asIdeal (Ideal.span {((q : ℕ) : 𝓞 K)}) : ℝ) * m⌋ : ℝ) /
    (multiplicity la.asIdeal (Ideal.span {((q : ℕ) : 𝓞 K)}) : ℝ)

structure ELocIn where
  supNu : HeightOneSpectrum (𝓞 S.c.F) → Cmp S i → ℝ
  mEta : HeightOneSpectrum (𝓞 S.c.F) → Cmp S i → ℝ
  fin : {la : HeightOneSpectrum (𝓞 S.c.F) | ∃ (q : ℕ) (Z : Cmp S i), q.Prime ∧ ((q : ℕ) : 𝓞 S.c.F) ∈ la.asIdeal ∧
    0 < supNu la Z - rndDown la q (mEta la Z)}.Finite

end Geo

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (K : Type) [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

def delG (D : ℕ) {N : ℕ} (x : Fin (N + 1) → Ω) : ℕ :=
  Module.finrank (IntermediateField.adjoin K (Set.range
    (ReciprocityTheory.ChartRestriction.G.T0.sImg (D := D) (0 : Fin (N + 1)) (fun k : Fin N => x k.succ / x 0))))
    (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)

variable {K}

end GlobalTheory.CompanionTheory.Ar.Deg
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

structure CompLaws (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) : Prop where
  comps : Nat.card (Comp Xo c) = Fintype.card (U c.F.val.toRingHom).Comp
  ne : Nonempty (Comp Xo c)
  genT : GenFromTest Xo c h
  evalWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  unTest : ∀ σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)
  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  ptNe : IntFrNe Xo c (algCls Xo c)
  intAll : IntAll Xo c
  e_sec : ∀ Z, e Z ∈ sec Xo c 0 0
  e_val : ∀ Z, evC h Z (e Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC h Z' (e Z) = 0

def Over {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (e₀ : Rul Xo c) (k : U.Comp) : Prop :=
  ∀ x ∈ (U.X k).dom, rdU U e₀ k x = 1

def WEq (Dw : Datum H) (a b : WZ E) : Prop := ∀ τ i, i < Dw.mult τ → a (τ, i) = b (τ, i)

def towerWt (Dw : Datum H) (a : WZ E) : Top.Wt (CMType H) (Dw.p + Dw.q) :=
  fun τ n => if (n : ℕ) < Dw.p then (a (τ.1, n) : ℝ) else -(a (conjEmb τ.1, Dw.p + Dw.q - 1 - n) : ℝ)

open Classical in

def flatZ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (w : CMType H → ℤ) : WZ E :=
  fun x => if h : x.1 (H.rt : E) = H.rt0 then w ⟨x.1, h⟩ else -w ⟨conjEmb x.1, Small.conjEmb_rt_of_ne h⟩

def OntoZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (a : WZ E)
    (Z : Comp Xo c) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k → ∀ P ∈ ((U σ).X k).SS (laZ (U σ) a k),
    ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cuspOn U h a Z) ∧
      ∀ x ∈ ((U σ).X k).dom, P x = ∑ i, as i * rdU (U σ) (fs i) k x

structure FlatSec (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (e₀ : Rul Xo c) (b : WZ E) where

  s : Rul Xo c

  s' : Rul Xo c
  s_sec : s ∈ secZ Xo c b
  s'_sec : s' ∈ secZ Xo c (-b)
  mul_eq : s * s' = e₀
  s_supp : s * e₀ = s
  s'_supp : s' * e₀ = s'

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  cInf_good : ∀ σ, cInf σ = cInf (goodOf c σ)
  inf_eq : ∀ σ, GoodEmb c σ → ∀ k, Over (U σ) e₀ k → ∀ y ∈ ((U σ).X k).dom,
    lieFacZ Dw x b * ((U σ).X k).pnorm (laZ (U σ) b k) (rdU (U σ) s k) y = cInf σ

  cFin : HeightOneSpectrum (𝓞 c.F) →₀ ℝ
  fin_eq : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, v e₀ = 0 → v s = ((cFin la : ℝ) : EReal)

def FlatSec.deg {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {e₀ : Rul Xo c} {b : WZ E} (F : FlatSec U x e₀ b) : ℝ :=
  ((F.cFin.sum fun la t => t * Real.log (Ideal.absNorm la.asIdeal)) - ∑ σ : c.F →+* ℂ, Real.log (F.cInf σ)) /
    (Module.finrank ℚ c.F : ℝ)

def BirOn (h : GenFrEx Xo c) (Z : Comp Xo c) {N : ℕ} (g : Fin (N + 1) → Rul Xo c) : Prop :=
  evC h Z (g 0) ≠ 0 ∧ IntermediateField.adjoin c.F (Set.range fun j => evC h Z (g j) / evC h Z (g 0)) = ⊤

section Read

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx}

structure Reading (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c) where

  φ : Om Z →+* RM.Ω
  φ_cst : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a

  t : Ix Dw → (RM.Ω)ˣ
  rd_eq : ∀ a : WZ E, ∀ f ∈ secZ Xo c a, Fr.rd f = ((∏ i, t i ^ exZ Dw a i : (RM.Ω)ˣ) : RM.Ω) * φ (evC h Z f)
  deg : letI := φ.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg

end Read

def CompOf {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (Dw.p + Dw.q)}
    (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp) : Prop :=
  ∀ Z, GlobalTheory.CompanionTheory.Ar.genPt (o.Fx (κ Z)).ξf = Y.j (Formalism.L2.Pj.genPt Z)

end GlobalTheory.CompanionTheory.Ar.Rec
end
end
