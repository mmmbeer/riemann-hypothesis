import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Definitions.Uniformization.InKLbPowIffPowEqOne

section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.TwistDescent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem memKL_of_lam_eq_zero {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (hx : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0) : GlobalTheory.MemKL A L x := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

end GlobalTheory.DualCon.TwistDescent

namespace GlobalTheory.DualCon

end GlobalTheory.DualCon
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelPointPairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hA : IsAbelianScheme A) {L : LB (G2 A).left} (hL : L.IsLB) {T : Over S} (a b c : T ⟶ G2 A) :
    pull (a * b * c).left (cls L hL) - pull (a * b).left (cls L hL) - pull (a * c).left (cls L hL)
      - pull (b * c).left (cls L hL) + pull a.left (cls L hL) + pull b.left (cls L hL) + pull c.left (cls L hL)
      - pull (1 : T ⟶ G2 A).left (cls L hL) = 0 := by
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨t, ht⟩ := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hA2 L hL T a b c
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_eight] at e
  simp at e
  rw [← e]
  abel

omit [IsCommMonObj A] in

theorem pull_eq_zero_of_factor {X : Scheme.{0}} {c : Pic X} {Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : pull f c = 0) : pull (g ≫ f) c = 0 := by
  rw [pull_comp, h, map_zero]

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem lam_eq_zero (hA : IsAbelianScheme A)
    (h₁ : pull (lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0)
    (h₂ : pull (lift (𝟙 A) (1 : A ⟶ A)).left (cls P hP) = 0) {T : Over S} (x : T ⟶ A)
    (hx : pull (lift (snd A T ≫ x) (fst A T)).left (cls P hP) = 0) :
    lam (cls P hP) (fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A)) (snd T (G2 A)) = 0 := by
  let W := T ⊗ G2 A
  let x' : W ⟶ A := fst T (G2 A) ≫ x
  let b₁ : W ⟶ A := snd T (G2 A) ≫ fst A A
  let b₂ : W ⟶ A := snd T (G2 A) ≫ snd A A
  have l₁ : ∀ b : W ⟶ A, DiagPairing.pc hP 1 b = 0 := fun b => by
    have e : (lift (1 : W ⟶ A) b) = b ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₁
  have l₂ : ∀ a : W ⟶ A, DiagPairing.pc hP a 1 = 0 := fun a => by
    have e : (lift a (1 : W ⟶ A)) = a ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₂
  have l₃ : DiagPairing.pc hP x' b₂ = 0 := by
    have e : (lift x' b₂) = lift b₂ (fst T (G2 A)) ≫ lift (snd A T ≫ x) (fst A T) := by
      rw [comp_lift, lift_snd_assoc, lift_fst]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ hx
  have one : (1 : W ⟶ G2 A) = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ea : fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A) = lift x' 1 := by
    rw [comp_lift, MonObj.comp_one]
  have eb : snd T (G2 A) = lift b₁ b₂ := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have e := cube_cls hA hP (lift x' 1) (lift b₁ 1) (lift 1 b₂)
  simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, one] at e
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP (x' * b₁) 1 - DiagPairing.pc hP x' b₂
    - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP x' 1 + DiagPairing.pc hP b₁ 1 + DiagPairing.pc hP 1 b₂
    - DiagPairing.pc hP 1 1 = 0 at e
  rw [l₁, l₁, l₂, l₂, l₂, l₃] at e
  rw [lam, ea, eb, one, lift_mul_lift, _root_.one_mul]
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP x' 1 - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP 1 1 = 0
  rw [l₁, l₂, ← e]
  abel

end GlobalTheory.KernelPointPairing
end
end

section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

def ofLinear (g : D.La →ₗ[𝓞 F] D.La) (c k : ℕ) (hc : c.Coprime p) (hk : k.Coprime p)
    (hg : ∀ x y, D.EF (g x) (g y) = c * D.EF x y) (hon : ∀ x, ∃ y, g y = k • x) : IntSim D p where
  c := c
  k := k
  c_cop := hc
  k_cop := hk
  g _ := g
  compat n m _ a := ⟨0, by simp⟩
  sim n _ := ⟨1, isCoprime_one_left, fun a b => by rw [hg]; simp⟩
  onto n _ a := let ⟨y, hy⟩ := hon a; ⟨y, 0, by simp [hy]⟩

def scalar (D : Datum F) (m : ℕ) (hm : m.Coprime p) : IntSim D p :=
  ofLinear (D := D) (m • LinearMap.id) (m ^ 2) m (Nat.Coprime.pow_left 2 hm) hm
    (fun x y => by simp [LinearMap.map_smul_of_tower]; ring) (fun x => ⟨x, by simp⟩)

def one (D : Datum F) (p : ℕ) : IntSim D p :=
  ofLinear (D := D) (p := p) LinearMap.id 1 1 (Nat.coprime_one_left p) (Nat.coprime_one_left p) (by simp) (fun x => ⟨x, by simp⟩)

def comp (g₁ g₂ : IntSim D p) : IntSim D p where
  c := g₁.c * g₂.c
  k := g₁.k * g₂.k
  c_cop := Nat.Coprime.mul g₁.c_cop g₂.c_cop
  k_cop := Nat.Coprime.mul g₁.k_cop g₂.k_cop
  g n := g₁.g n ∘ₗ g₂.g n
  compat n m h a := by
    obtain ⟨b₂, hb₂⟩ := g₂.compat n m h a
    obtain ⟨b₁, hb₁⟩ := g₁.compat n m h (g₂.g (n * m) a)
    refine ⟨b₁ + g₁.g n b₂, ?_⟩
    have e : g₂.g n a = g₂.g (n * m) a - n • b₂ := by rw [← hb₂]; abel
    simp only [LinearMap.comp_apply]
    rw [e, map_sub, map_nsmul, smul_add, ← hb₁]
    abel
  sim n h := by
    obtain ⟨u₁, hu₁, h₁⟩ := g₁.sim n h
    obtain ⟨u₂, hu₂, h₂⟩ := g₂.sim n h
    refine ⟨u₁ * u₂, hu₁.mul_left hu₂, fun a b => ?_⟩
    have := dvd_add (h₁ (g₂.g n a) (g₂.g n b)) (Dvd.dvd.mul_left (h₂ a b) (g₁.c * u₁))
    simp only [LinearMap.comp_apply]
    obtain ⟨q, hq⟩ := this
    exact ⟨q, by push_cast; linear_combination hq⟩
  onto n h a := by
    obtain ⟨b₁, d₁, h₁⟩ := g₁.onto n h a
    obtain ⟨b₂, d₂, h₂⟩ := g₂.onto n h b₁
    refine ⟨b₂, g₂.k • d₁ + g₁.g n d₂, ?_⟩
    simp only [LinearMap.comp_apply]
    rw [h₂, map_add, map_nsmul, map_nsmul, h₁]
    module



end IntSim

variable {S : Scheme.{0}}

end GlobalTheory.UPel
end
end

section
noncomputable section

namespace GlobalTheory.UPel.HeckeImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {S : Scheme.{0}}

theorem eta_zero {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem eta_neg {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

theorem eta_nsmul {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (m : ℕ) (x : D.La) :
    o.eta (m • x) = o.eta x ^ m := by
  induction m with
  | zero => simp [eta_zero]
  | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def sub {D : Datum F} {p N' : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s) (g : IntSim D p) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ a, h = o.eta ((N' / g.k) • g.g N' a)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

end GlobalTheory.UPel.HeckeImage
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPel.HeckeImage

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_pow_eq_one_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (m : ℕ), 0 < m → IsUnit ((m : Γ(S, ⊤))) → ∀ (T : Over S) (x : T ⟶ A), x ^ m = 1 → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (q : Sp κ ⟶ T.left), (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = 1) → x = 1 := by
  intro S A _ _ hA m _ hm T x hx hgeo
  let f := (ReciprocityTheory.ChartRestriction.G.Out.mulA A m).left
  haveI : FormallyUnramified f := GlobalTheory.formallyUnramified_mulA S A m hm
  haveI : Smooth A.hom := hA.smooth
  have hfA : f ≫ A.hom = A.hom := Over.w _
  haveI : LocallyOfFiniteType (f ≫ A.hom) := by rw [hfA]; infer_instance
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have hpow : ∀ y : T ⟶ A, y ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA A m = y ^ m := fun y => by
    simp [ReciprocityTheory.ChartRestriction.G.Out.mulA, MonObj.comp_pow]
  have hf : x.left ≫ f = (1 : T ⟶ A).left ≫ f := by
    have e1 := congrArg CommaMorphism.left (hpow x)
    have e2 := congrArg CommaMorphism.left (hpow 1)
    simp only [Over.comp_left] at e1 e2
    rw [e1, e2, hx, one_pow]
  let p : T.left ⟶ pullback f f := pullback.lift x.left (1 : T ⟶ A).left hf
  have hr : Set.range p ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨t, rfl⟩
    let κ : Type := AlgebraicClosure (T.left.residueField t)
    let q : Sp κ ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) κ)) ≫ T.left.fromSpecResidueField t
    have hq : (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ 1 := by
      rw [hgeo κ q, MonObj.comp_one]
    have hq' : q ≫ x.left = q ≫ (1 : T ⟶ A).left := by
      have h0 := congrArg (fun h => h.left) hq
      simp only [Over.comp_left, Over.homMk_left] at h0
      exact h0
    have e : q ≫ p = (q ≫ x.left) ≫ pullback.diagonal f := by
      refine pullback.hom_ext ?_ ?_
      · simp only [p, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [p, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hq']
    refine ⟨(q ≫ x.left) (IsLocalRing.closedPoint κ), ?_⟩
    have hqt : q (IsLocalRing.closedPoint κ) = t :=
      Scheme.fromSpecResidueField_apply t _
    have e2 : p (q (IsLocalRing.closedPoint κ)) =
        pullback.diagonal f ((q ≫ x.left) (IsLocalRing.closedPoint κ)) :=
      congrArg (fun h => h (IsLocalRing.closedPoint κ)) e
    rw [hqt] at e2
    exact e2.symm
  let g := IsOpenImmersion.lift (pullback.diagonal f) p hr
  have hg := IsOpenImmersion.lift_fac (pullback.diagonal f) p hr
  have h1 : x.left = g := by
    have h0 := congrArg (· ≫ pullback.fst f f) hg
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, p, pullback.lift_fst] at h0
    exact h0.symm
  have h2 : (1 : T ⟶ A).left = g := by
    have h0 := congrArg (· ≫ pullback.snd f f) hg
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, p, pullback.lift_snd] at h0
    exact h0.symm
  exact Over.OverMorphism.ext (h1.trans h2.symm)

end GlobalTheory.TorsionRigid
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.KerPowDescent

theorem pow_eq_one_of_lift {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S} [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A')
    [IsMonHom ψ] (m : ℕ) {P' : LB (G2 A').left} (hP' : P'.IsLB)
    (hiso : LBIso (Hecke.lbPow o.P m) (P'.pull (sq2 ψ))) {e₀ : ℕ}
    (hker : ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e₀ = 1)
    {T T' : Over S} (π' : T' ⟶ T) (y : T' ⟶ o.A) (x : T ⟶ A') (hy : y ≫ ψ = π' ≫ x)
    (h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0) : y ^ (m * e₀) = 1 := by
  have hP := o.isLB
  have hPm : (Hecke.lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left
        (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, Hecke.evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rwa [← pow_mul] at h4

theorem kernel_primePower_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b N S s o c hc hpu H A' _ _ ψ hA' hψ hG hH P' hP' r₁ r₂ hiso
  haveI := hψ
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  obtain ⟨e, rfl⟩ := hc
  refine ⟨e₀, he₀, ?_⟩
  intro T x hx
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  have hxc : x ^ (p ^ e * e₀) = 1 := by
    let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
    let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
    let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
      show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
      rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
    have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
      show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
      exact pullback.condition.symm)
    have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker π' y x hy h0
    have h5 : π' ≫ x ^ (p ^ e * e₀) = π' ≫ 1 := by
      rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h6 := congrArg (fun f => f.left) h5
    simp only [Over.comp_left] at h6
    exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6
  have hu : IsUnit (((p ^ e : ℕ) : Γ(S, ⊤))) := by
    have := (hpu.pow e).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  refine GlobalTheory.TorsionRigid.eq_one_of_pow_eq_one_of_geometric S A' hA' (p ^ e)
    (pow_pos (Fact.out : p.Prime).pos e) hu T (x ^ e₀) (by rw [← pow_mul, mul_comm]; exact hxc) ?_
  intro κ _ _ q
  let Tq : Over S := Over.mk (q ≫ T.hom)
  let πq : Tq ⟶ T := Over.homMk q rfl
  obtain ⟨pt, hpt⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left (q ≫ x.left)
  let y : Tq ⟶ o.A := Over.homMk pt (by
    show pt ≫ o.A.hom = q ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← hpt, Category.assoc, Over.w x])
  have hy : y ≫ ψ = πq ≫ x := Over.OverMorphism.ext (by
    show pt ≫ ψ.left = q ≫ x.left
    exact hpt.symm)
  have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker πq y x hy h0
  have hg : (y ^ e₀) ^ (p ^ e) = 1 := by rw [← pow_mul, mul_comm]; exact h4
  have hgψ : (y ^ e₀) ≫ ψ = (πq ≫ x) ^ e₀ := by rw [GlobalTheory.SS.FrobTorsion.pow_comp', hy]

  have hz : GlobalTheory.AbDual.evc hP' (snd A' Tq ≫ (y ^ e₀) ≫ ψ) (fst A' Tq) = 0 := by
    have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst A' Tq) (snd A' Tq ≫ πq)).left) h0
    rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst] at h1
    simp only [Category.assoc] at h1
    rw [hgψ, comp_pow, Hecke.evc_pow_left hA' hP' r₁ r₂, h1, smul_zero]
  have hG0 := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 A') := AbelianSchemeGerms.isAbelianScheme_tensor A' A' hA' hA'
  have hAo2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have s₁ : GlobalTheory.CechPic.pull (lift (1 : A' ⟶ A') (𝟙 A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₁
  have s₂ : GlobalTheory.CechPic.pull (lift (𝟙 A') (1 : A' ⟶ A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₂
  have hK : GlobalTheory.MemKL (G2 A') P' (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') :=
    GlobalTheory.DualCon.TwistDescent.memKL_of_lam_eq_zero hP' _
      (GlobalTheory.KernelPointPairing.lam_eq_zero hP' hA' s₁ s₂ ((y ^ e₀) ≫ ψ) hz)
  have w₀ : Out.WeilIs (G2 A') P' 1 (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') 1 1 :=
    GlobalTheory.DescendedPrincipal.weilIs_one_right hG0 hA2 hP' fun pp => by
      obtain ⟨V, hV, c, hc⟩ := hK pp
      exact ⟨V, hV, GlobalTheory.DescendedPrincipal.exists_theta_of_translDiff hP' _ V c hc⟩
  have hPc : (Hecke.lbPow o.P (p ^ e)).IsLB := LB.isLB_linComb o.isLB _ _
  let ψ2 : G2 o.A ⟶ G2 A' := lift (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
  haveI : IsMonHom ψ2 := inferInstance
  have hw : LBIso (Geo.Tor.lbPow (Hecke.lbPow o.P (p ^ e)) 1) (P'.pull ψ2.left) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hPc 1) hPc (pull_isLB hP' _) (GlobalTheory.lbIso_lbPow_one hPc) hiso
  have hHψ : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hG.inv ⟨h, hh⟩)
  obtain ⟨h, hh, hgh⟩ := hH κ (q ≫ T.hom) (y ^ e₀) hg fun h hh => by
    have e1 : (lift (y ^ e₀) 1 : Tq ⟶ G2 o.A) ≫ ψ2 = lift ((y ^ e₀) ≫ ψ) 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    have e2 : (lift 1 (toUnit Tq ≫ h) : Tq ⟶ G2 o.A) ≫ ψ2 = 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, Category.assoc, hHψ h hh, MonObj.comp_one]
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG0 hAo2 hPc hP' ψ2 hw (n := 1) (x := lift (y ^ e₀) 1)
      (y := lift 1 (toUnit Tq ≫ h)) (c := 1) (by rw [e1, e2]; exact w₀)
    simpa using this
  show πq ≫ x ^ e₀ = 1
  rw [comp_pow, ← hgψ, hgh, Category.assoc, hHψ h hh, MonObj.comp_one]

end GlobalTheory.UPel.HT.ES.KerPowDescent
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_primeToP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (exact GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (intros; apply GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent  <;> assumption)
end
