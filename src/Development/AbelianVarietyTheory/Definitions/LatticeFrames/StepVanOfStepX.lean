import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.TupModel

variable {D : D7} {u : D.what₂.Word}

theorem exists_haar_fin (V : HSp D) : ∃ μ : Measure (GfC V), μ.IsHaarMeasure := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have : LocallyCompactSpace (GfC V) := (GlobalTheory.Ker.CongTop.isClosed_GfC V).locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

theorem exists_haar_sub (V : HSp D) (R : Subgroup (GA D V)) (hR : IsClosed (R : Set (GA D V))) :
    ∃ μ : Measure (R.subgroupOf (GfC V)), μ.IsHaarMeasure := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have : LocallyCompactSpace (GfC V) := (GlobalTheory.Ker.CongTop.isClosed_GfC V).locallyCompactSpace
  have hc : IsClosed ((R.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := hR.preimage continuous_subtype_val
  have : LocallyCompactSpace (R.subgroupOf (GfC V)) := hc.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩


variable (d : Dat D u) (hb : d.Base)

def vol (j : ℕ) : Vol (d.st j).V :=
  if h : j < D.R.m then ⟨(d.st j).ν, (d.st j).fd, (hb.st j h).haar, (hb.st j h).fund⟩ else (GlobalTheory.Unf.Inhab.nonempty_vol _).some

theorem vol_μ {j : ℕ} (h : j < D.R.m) : (vol d hb j).μ = (d.st j).ν := by rw [vol, dif_pos h]


@[reducible] def comm : Comm D where
  θ := d.c.θ
  ψ := d.c.ψ
  V j := (d.st j).V
  par j := (d.st j).par
  M j := (d.st j).M
  T := D.sp.X'
  parT := d.top.par
  MT := d.top.M
  It j := (d.p j).It
  ItT j h := (d.pT j h).It
  vol := vol d hb
  volT := ⟨d.top.ν, d.top.fd, hb.top.haar, hb.top.fund⟩
  X := D.sp.X
  x := d.x
  vac j := (d.k j).vac
  bes := d.bes
  jac := d.jac
  lnk := d.lnk
  vL := d.vL
  Lz := d.Lz
  oT := d.oT
  μf j := (exists_haar_fin _).choose
  ρJ j ρ h := (exists_haar_sub _ _ (GlobalTheory.QuotZero.jac_haar_inv ((d.jac j ρ h).lev (d.x (j + 1)).vol)).1).choose
  ρB j ρ h := (exists_haar_sub _ _ (GlobalTheory.QuotZero.bes_haar_inv ((d.bes j ρ h).lev (d.x j).vol)).1).choose
  Fr j := (D.mem u).C.Y j


open Classical in

@[reducible] def tup : Tup (comm d hb) where
  om j := (d.p j).ω
  omT j h := (d.pT j h).ω
  pt j := (d.p j).pt
  ptT j h := (d.pT j h).pt
  sBF := d.sBF
  sFB := d.sFB
  CC j := (d.st j).CC d.c
  CT := d.top.st.CC d.c
  io j := (d.p j).io
  ioT j h := (d.pT j h).io
  kom j := (d.k j).om
  Ch _ := Unit
  dd j _ _ := (d.k j).c
  e j _ := Finsupp.single (d.t j) 1
  eT _ _ _ := Finsupp.single 1 1
  Col := Col D u
  Ram j := d.Ram j
  S j := d.S j
  K j := (D.mem u).C.K j
  rd j _ := d.rd j
  tail n h ψ F := if hF : ∃ F', d.eT F' = F then
    (D.mem u).P.Ptil (Eq.rec (motive := fun n _ => Col D u n) ψ h) hF.choose else 0
  cI _ := 1
  cV _ := 1
  cK _ := 1
  cP := 1


theorem trc_single {V : HSp D} (g : GA D V) (f : GA D V → ℂ) : trc (Finsupp.single g 1) f = rTrans g f := by
  rw [trc, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]


theorem per_eq (j ρ h ψ G y v) :
    (tup d hb).per j ρ h ψ G y v = (d.B j ρ h).per d.c.ψ (d.rd j ψ y) (rTrans (d.t j) (G.1 v)) := by
  unfold Tup.per Tup.perF
  rw [Fintype.sum_unique, trc_single]

theorem two_eq (j φ C β) : (tup d hb).two j (fun _ => φ) C β = d.two j φ C := by
  unfold Tup.two
  rw [Fintype.sum_unique, Fintype.sum_unique]
  rfl







section Ind

variable {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c)

theorem up_mem {t : Tup c} (ht : t.Is) {ψ : t.Col 0} (hψ : ψ ∈ t.Ram 0) : ∀ i, 2 * i ≤ D.R.m → t.up i ψ ∈ t.Ram (2 * i) := by
  intro i
  induction i with
  | zero => exact fun _ => hψ
  | succ i ih =>
    intro h
    exact ht.stabK (2 * i + 1) (by omega) _ (ht.stabK (2 * i) (by omega) _ (ht.stabS (2 * i) (by omega) _ (ih (by omega))))

theorem down (ht : ∀ s, (t s).Is) (hS : StepX t) (n : ℕ) (h₀ : 0 + 2 * n + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯)
    (ψ : ∀ i, (t (s i)).Col 0) (hψ : ∀ i, ψ i ∈ (t (s i)).Ram 0) :
    ∀ k ρ (h : 2 * k + 2 * ρ + 2 = D.R.m) (α : I → ℂ) (G : ∀ i, (t (s i)).CC (2 * k)),
      (∀ y v, ∑ i, α i * (∏ l ∈ Finset.range k, (t (s i)).cV (2 * l) * (t (s i)).cK (2 * l) * (t (s i)).cK (2 * l + 1)) *
        (t (s i)).per (2 * k) ρ h ((t (s i)).up k (ψ i)) (G i) y v = 0) →
      ∀ y v, ∑ i, α i * (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) * (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * k) (G i)) y v = 0 := by
  intro k
  induction k with
  | zero =>
    intro ρ h α G hyp y v
    obtain rfl : ρ = n := by omega
    exact hyp y v
  | succ k ih =>
    intro ρ h α G hyp y v
    have h' : 2 * k + 2 * (ρ + 1) + 2 = D.R.m := by omega
    have e := hS (2 * k) ρ h' I s
      (fun i => α i * ∏ l ∈ Finset.range k, (t (s i)).cV (2 * l) * (t (s i)).cK (2 * l) * (t (s i)).cK (2 * l + 1))
      (fun i => (t (s i)).up k (ψ i)) G (fun i => up_mem (ht _) (hψ i) k (by omega)) (fun y v => by
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
        rw [Finset.prod_range_succ, mul_assoc (α i)]
        rfl)
    have e2 := ih (ρ + 1) h' (fun i => α i * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1)))
      (fun i => (t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i))) (fun y v => by
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (e y v)
        ring) y v
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e2
    rw [show Finset.range (2 * (k + 1)) = Finset.range (2 * k + 1 + 1) from rfl, Finset.prod_range_succ, Finset.prod_range_succ]
    congr 1
    ring


end Ind


example (f : Unit → Unit → ℂ) (z : ℂ) :
    Iter2 (G₁ := Unit) (G₂ := Unit) (R₁ := ⊥) (R₂ := ⊥) (Measure.dirac 1) (Measure.dirac ()) (Measure.dirac 1) (Measure.dirac ()) f z ↔
      z = f () () := by
  unfold Iter2
  simp only [isQuotIntL1_bot, integral_dirac]
  constructor
  · rintro ⟨f₁, ⟨-, h1⟩, h2⟩
    rw [h1, (h2 ()).2]
  · rintro rfl
    exact ⟨fun _ => f () (), ⟨integrable_const _, rfl⟩, fun q => ⟨Integrable.of_finite, rfl⟩⟩

end GlobalTheory.SeeSaw.TupModel

end
