import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CubeFib

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators

attribute [local instance] Over.cartesianMonoidalCategory

section Series

variable {k : Type} [CommRing k] {d g : ℕ}

def beta (Φ : PS k 3 d) (l : ℕ) (cv : Fin d → PowerSeries k) : PS k 1 d :=
  fun mu => MvPowerSeries.coeff
    (mu.mapDomain Sum.inr + Finsupp.single (Sum.inl 0) (l - 1) + Finsupp.single (Sum.inl 1) 1)
    (MvPowerSeries.subst (fun p : Fin 3 × Fin d =>
      if h : p.1 = 2 then (MvPowerSeries.X (Sum.inr (0, p.2)) : MvPowerSeries (Fin 2 ⊕ Fin 1 × Fin d) k)
      else MvPowerSeries.subst (fun _ : Unit =>
        (MvPowerSeries.X (Sum.inl (if p.1 = 0 then 0 else 1)) : MvPowerSeries (Fin 2 ⊕ Fin 1 × Fin d) k)) (cv p.2)) Φ)

def pullS {n : ℕ} (ψ : Fin g → PS k 1 d) (f : PS k n g) : PS k n d :=
  MvPowerSeries.subst (fun p : Fin n × Fin g => ev (n := n) ![pt k d p.1] (ψ p.2)) f

def linS (ψ : Fin g → PS k 1 d) (u : Fin d → k) : Fin g → k :=
  fun j => ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) (ψ j) * u i

structure CubeLaws (F : Fin d → PS k 2 d) (Φ : PS k 3 d) : Prop where
  face0 : ev (n := 2) ![0, pt k d 0, pt k d 1] Φ = 1
  cubeSymmetric_swap_first : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] Φ = Φ
  cubeSymmetric_swap_last : ev (n := 3) ![pt k d 0, pt k d 2, pt k d 1] Φ = Φ
  cocycle : ev (n := 4) ![addOf F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] Φ *
      ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] Φ =
    ev (n := 4) ![pt k d 0, addOf F (pt k d 1) (pt k d 2), pt k d 3] Φ * ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] Φ

end Series

section Geo

variable {k : Type} [CommRing k] {d g : ℕ}

def jet3 {G : Over (Sp k)} (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G) (m : ℕ) :
    algOver k (JetR k (Fin 3 × Fin d) m) ⟶ G3 G :=
  lift (algOverHom (jetPt (d := d) (0 : Fin 3) m) ≫ x m)
    (lift (algOverHom (jetPt (d := d) (1 : Fin 3) m) ≫ x m) (algOverHom (jetPt (d := d) (2 : Fin 3) m) ≫ x m))

def CubeSer {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G) (i : L.L.ι) (Φ : PS k 3 d) : Prop :=
  ∀ m : ℕ, ∃ h : (⊤ : (Sp (JetR k (Fin 3 × Fin d) m)).Opens) ≤ (jet3 x m).left ⁻¹ᵁ (Theta G L.L).U (fun _ => i),
    (Semi.res h (pullU (jet3 x m).left _ (c.t.s fun _ => i))).val =
      (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) m))).inv.hom (GlobalTheory.JetSer.toJet m Φ)

def MapSer {G B : Over (Sp k)} (q : G ⟶ B) (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G)
    (y : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B) (ψ : Fin g → PS k 1 d) : Prop :=
  ∀ m : ℕ, ∃ a : JetR k (Fin 1 × Fin g) m →ₐ[k] JetR k (Fin 1 × Fin d) m,
    (∀ j, a (zR m ((0 : Fin 1), j)) = GlobalTheory.JetSer.toJet m (ψ j)) ∧ x m ≫ q = algOverHom a ≫ y m




theorem CubeSer.unique {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L}
    {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G} {i : L.L.ι} {Φ Φ' : PS k 3 d}
    (h : CubeSer c x i Φ) (h' : CubeSer c x i Φ') : Φ = Φ' := by
  refine GlobalTheory.JetSer.eq_of_toJet_eq fun m => ?_
  obtain ⟨_, h1⟩ := h m
  obtain ⟨_, h2⟩ := h' m
  exact (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) m))).symm.commRingCatIsoToRingEquiv.injective
    (h1.symm.trans h2)

theorem CubeSer.isUnit {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L}
    {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G} {i : L.L.ι} {Φ : PS k 3 d}
    (h : CubeSer c x i Φ) : IsUnit Φ := by
  obtain ⟨h0, h1⟩ := h 0
  have hu := (Semi.res h0 (pullU (jet3 x 0).left _ (c.t.s fun _ => i))).isUnit
  rw [h1] at hu
  have hu2 := hu.map (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) 0))).hom.hom
  rw [Iso.inv_hom_id_apply] at hu2
  have hu3 := hu2.map (Chart.jetAug k (Fin 3 × Fin d) 0)
  rw [GlobalTheory.JetSer.jetAug_toJet] at hu3
  exact MvPowerSeries.isUnit_iff_constantCoeff.2 hu3


theorem MapSer.constantCoeff_eq_zero {G B : Over (Sp k)} {q : G ⟶ B}
    {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G} {y : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B}
    {ψ : Fin g → PS k 1 d} (h : MapSer q x y ψ) (j : Fin g) : MvPowerSeries.constantCoeff (ψ j) = 0 := by
  obtain ⟨a, ha, -⟩ := h 0
  have h0 : (zR 0 ((0 : Fin 1), j) : JetR k (Fin 1 × Fin g) 0) = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [zero_add, pow_one]
    exact Ideal.subset_span ⟨_, rfl⟩
  have h1 := ha j
  rw [h0, map_zero] at h1
  rw [← GlobalTheory.JetSer.jetAug_toJet 0 (ψ j), ← h1, map_zero]



example (m : ℕ) : GlobalTheory.JetSer.toJet m (1 : PS k 3 0) = 1 := GlobalTheory.JetSer.toJet_one m

example {G B : Over (Sp k)} {q : G ⟶ B} {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin 0) m) ⟶ G}
    {y : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B} {ψ : Fin g → PS k 1 0} (h : MapSer q x y ψ) : ψ = 0 := by
  funext j
  ext e
  rw [Subsingleton.elim e 0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.constantCoeff_eq_zero j]
  simp

end Geo

structure Fib (k : Type) [Field k] where
  G : Over (Sp k)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  smooth : Smooth G.hom
  L : RigLB G
  cub : CubicalStr G L
  P : PolAV (Sp k)
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  cubB : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩
  q : G ⟶ P.A
  [q_hom : IsMonHom q]
  q_flat : Flat q.left
  q_surj : Surjective q.left
  q_affine : IsAffineHom q.left
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  i : splitTorus (Sp k) X ⟶ G
  i_hom : IsMonHom i
  isKernel : IsPullback i (toUnit _) q (η[P.A])
  pull : (CubeMap.ofHom q).IsPullCubical cub cubB

attribute [instance] Fib.grp Fib.comm Fib.q_hom Fib.addX Fib.freeX Fib.finX

end GlobalTheory.CubeFib
