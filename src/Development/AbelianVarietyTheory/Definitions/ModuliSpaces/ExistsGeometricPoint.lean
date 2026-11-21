import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArcBaseExamples
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.FamTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem coe_rt (S A : ℕ) : (RZ.rt H S A : ℂ) = H.rt0 := by
  show 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring


theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} (β : RZ H n l.A →+* KA l)
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) {S : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    (o : Obj D l (baseKA l) s) : FullObj D (s ≫ spMap β) o.t o.etaA := by
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, fun k _ _ _ x gam hx => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  have e : φ.hom.comp β = gam := by
    have h : spMap (φ.hom.comp β) = spMap gam := by
      rw [← hx, ← Category.assoc, ← hφ]
      exact Spec.map_comp (CommRingCat.ofHom β) φ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have e₁ : β (RZ.rt H n l.A) = (baseKA l).ρ := Subtype.ext ((hβ _).trans (coe_rt _ _))
  have e₂ : β (RZ.ze H n l.A) = (baseKA l).ζ := Subtype.ext (hβ _)
  obtain ⟨h₁, I, h₂, h₃, -⟩ := o.geom k x φ.hom hφ.symm
  subst e
  exact ⟨by rw [RingHom.comp_apply, e₁]; exact h₁, I, by rw [RingHom.comp_apply, e₂]; exact h₂, h₃⟩

theorem exists_roots {n N : ℕ} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (β : RZ H n N →+* k) :
    ∃ ζ : ℕ → kˣ, (∀ m, 0 < m → IsPrimitiveRoot (ζ m) m) ∧ (∀ a b, 0 < a → 0 < b → ζ (a * b) ^ b = ζ a) ∧
      (ζ N : k) = β (RZ.ze H n N) := by
  let B : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  let R : Subring ℂ := RZ H n N ⊓ B
  have hz : ∀ m, zeta m ∈ B := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : zeta 0 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    · exact (Complex.isPrimitiveRoot_exp m hm.ne').isIntegral hm
  letI : Algebra R B := (Subring.inclusion inf_le_right).toAlgebra
  haveI : Algebra.IsIntegral ℤ B := inferInstanceAs (Algebra.IsIntegral ℤ (integralClosure ℤ ℂ))
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.tower_top (R := ℤ)
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subring.inclusion_injective _)
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_isIntegral_of_injective (B := B)
    (β.comp (Subring.inclusion (inf_le_left : R ≤ RZ H n N)))
  have hp : ∀ m, 0 < m → IsPrimitiveRoot (ψ ⟨zeta m, hz m⟩) m := fun m hm => by
    have h₀ : IsPrimitiveRoot (⟨zeta m, hz m⟩ : B) m :=
      IsPrimitiveRoot.of_map_of_injective (f := B.subtype) (Complex.isPrimitiveRoot_exp m hm.ne') Subtype.val_injective
    rw [← Polynomial.isRoot_cyclotomic_iff_charZero hm, ← Polynomial.map_cyclotomic m ψ]
    exact (h₀.isRoot_cyclotomic hm).map
  have hne : ∀ m, ψ ⟨zeta m, hz m⟩ ≠ 0 := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : (⟨zeta 0, hz 0⟩ : B) = 1 := Subtype.ext (by simp [zeta])
      rw [this, map_one]; exact one_ne_zero
    · exact (hp m hm).ne_zero hm.ne'
  refine ⟨fun m => Units.mk0 _ (hne m), fun m hm => IsPrimitiveRoot.coe_units_iff.1 (hp m hm), fun a b ha hb => ?_, ?_⟩
  · ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow]
    congr 1
    ext
    have : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
    simp only [SubmonoidClass.mk_pow, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  · exact DFunLike.congr_fun hψ ⟨zeta N, (RZ.ze H n N).2, hz N⟩

theorem weilIs_zero {S : Scheme.{0}} (T : Over S) (m : ℕ) :
    Out.WeilIs (𝟙_ (Over S)) (UU.trivRig (𝟙_ (Over S))).L m (1 : T ⟶ _) 1 1 :=
  (UU.cubWeil_iff_weilIs (c := UU.trivCub (𝟙_ (Over S))) globalFns_holds (UU.isAbelianScheme_unit S)
      (one_pow _) (one_pow _) 1).1 (UU.cubWeil_triv (one_pow _) (one_pow _))

theorem fullObj_zero {n N : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) :
    FullObj (Test.zeroDatum H) s (Inhab.zeroTriple H S) (fun _ => 1) := by
  refine ⟨Inhab.isProper_zeroTriple S, (Out.Inh.zeroPolAV S).ample, (Out.Inh.zeroPolAV S).ktriv,
    fun _ _ => (_root_.mul_one _).symm, fun _ => rfl, fun k _ _ _ x β _ => ⟨fun τ => ?_, ?_⟩⟩
  · have h : LieMult (Inhab.zeroTriple H S).act x τ 0 :=
      ⟨Fin.elim0, fun i => i.elim0, fun w _ => ⟨Fin.elim0, ⟨Fin.elim0, fun i => i.elim0, toUnit_unique _ _⟩,
        fun _ _ => Subsingleton.elim _ _⟩⟩
    exact ⟨fun _ => h, fun _ => h⟩
  · obtain ⟨ζ, h₁, h₂, h₃⟩ := exists_roots β
    refine ⟨⟨ζ, h₁, h₂, fun _ _ => 1, fun _ _ _ => toUnit_unique _ _, fun _ _ _ => toUnit_unique _ _,
      fun _ _ a => ⟨fun _ => ⟨a, rfl⟩, fun _ => rfl⟩, fun _ _ _ => ⟨fun _ => ⟨PUnit.unit, toUnit_unique _ _⟩,
        fun _ => toUnit_unique _ _⟩, fun _ _ _ _ _ => toUnit_unique _ _, fun m _ a b => ?_⟩, h₃,
      fun _ => toUnit_unique _ _⟩
    have e : unitOn (ζ m ^ (Test.zeroDatum H).EF a b) = 1 := by
      show unitOn (ζ m ^ (0 : ℤ)) = 1
      rw [zpow_zero]; exact map_one _
    exact e ▸ weilIs_zero (Over.mk x) m


variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ}


section Frames
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LN

variable {Z : Scheme.{0}} (G : Over Z) (N : ℕ)

def oneSec {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Sec (LB.LinComb (Inh.trivLB X) φ ε) :=
  ⟨fun _ => 1, fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem gs_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 1 = 1 := by
  rw [gs_eq _ _ _ h, map_one, map_one]

theorem mem_wchart_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j) (y : Y) :
    y ∈ LB.wchart (Inh.trivLB X) φ j := Set.mem_iInter.2 fun _ => trivial

theorem lin_one {T T' : Over Z} (h : T' ⟶ T) :
    Lin G (Inh.trivLB G.left) N h (fun _ : Fin 1 => oneSec _ _) (fun _ => 1) (oneSec _ _) := by
  intro z J hJ
  rw [Fin.sum_univ_one]
  exact (gs_one _ _ _ (hJ.mem _ _)).trans ((congrArg₂ (· * ·) (gs_one _ _ ⊤ trivial)
    (gs_one _ _ _ (mem_wchart_triv _ _ _))).trans (_root_.one_mul _)).symm



end Frames



section RankZero

variable {S : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {lv}

theorem torsion_eq_one (h : FullObj (Test.zeroDatum H) s t lv) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (x : Sp k ⟶ S) {m : ℕ} (hm : 0 < m) (g : Over.mk x ⟶ t.G) (hg : g ^ m = 1) : g = 1 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := h.geom k x φ.hom hφ.symm
  obtain ⟨a, rfl⟩ := (I.onto m hm g).1 hg
  exact (I.ker m hm a).2 ⟨a, rfl⟩


theorem exists_geometric_point_over {X : Scheme.{0}} (K : Type) [Field K] (u : Sp K ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X) (q : Sp k) (q' : Sp K), z q = u q' :=
  ⟨AlgebraicClosure K, inferInstance, inferInstance, spMap (algebraMap K _) ≫ u, IsLocalRing.closedPoint _, _,
    Scheme.Hom.comp_apply _ _ _⟩

theorem exists_geom {X : Scheme.{0}} (y : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X) (q : Sp k), z q = y := by
  obtain ⟨k, _, _, z, q, q', h⟩ := exists_geometric_point_over (X.residueField y) (X.fromSpecResidueField y)
  exact ⟨k, inferInstance, inferInstance, z, q, h.trans (Scheme.fromSpecResidueField_apply y q')⟩

theorem exists_geom_specializes {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R] (f : X ⟶ Sp R)
    [Flat f] (y : X) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharZero k) (z : Sp k ⟶ X) (q : Sp k),
      z q ⤳ y := by
  obtain ⟨y', hy', hb⟩ := Flat.generalizingMap f
    (show (⊥ : PrimeSpectrum R) ⤳ f y from (PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
  obtain ⟨k, _, _, z, q, hz⟩ := exists_geom y'
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (z ≫ f)
  have hinj : Function.Injective φ.hom := by
    have e : Spec.map φ q = (⊥ : PrimeSpectrum R) := by
      rw [hφ, Scheme.Hom.comp_apply, hz]; exact hb
    have e' : Ideal.comap φ.hom q.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal e
    rw [RingHom.injective_iff_ker_eq_bot, ← le_bot_iff, ← e']
    exact Ideal.comap_mono bot_le
  exact ⟨k, inferInstance, inferInstance, charZero_of_injective_ringHom (R := R) hinj, z, q, hz ▸ hy'⟩




end RankZero



end GlobalTheory.Models.FamTest

end
