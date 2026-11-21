import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.OfRingsLoc
variable {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))

instance ls : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance li : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [CommRing R] in
theorem ι_comp_apply {X U : Scheme.{0}} (f : X ⟶ U) (W : X.Opens) (y : X) (h : y ∈ W) :
    (Scheme.Opens.ι W ≫ f) ⟨y, h⟩ = f y :=
  rfl

omit [CommRing R] in

theorem cov_pt {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S.arrows j := by
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := (𝒰.X i).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : IsAffine W := hW
  have : Etale (𝒰.f i) := 𝒰.mem₀.2 ⟨i⟩
  refine ⟨W, Scheme.Opens.ι W ≫ 𝒰.f i, ⟨y, hyW⟩, inferInstance, inferInstance, ?_, ?_⟩
  · exact (ι_comp_apply (𝒰.f i) W y hyW).trans hy
  · exact S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) (Scheme.Opens.ι W)
theorem loc_surj {U : Scheme.{0}} (x : Sec (ofRings R M) U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)),
      IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x := by
  obtain ⟨V, j, v, hV, hj, hv, hS⟩ := cov_pt _
    (Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (U := op U) x) u
  obtain ⟨t, ht⟩ := hS
  exact ⟨V, j, v, t, hV, hj, hv, ht⟩

theorem loc_inj {U : Scheme.{0}} (m : M.obj Γ(U, ⊤)) (hm : ofRings.sec M U m = 0) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0 := by
  have h0 : ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) m =
      ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) 0 := by
    rw [map_zero]; exact hm
  obtain ⟨V, j, v, hV, hj, hv, hS⟩ := cov_pt _
    (Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) m 0 h0) u
  refine ⟨V, j, v, hV, hj, hv, ?_⟩
  have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) m =
      ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) 0 := hS
  rw [map_zero] at h1
  exact h1
end LateralTheory.EtaleFoundations.OfRingsLoc
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

def LateralTheory.EtaleFoundations.twF_gen_inj : Prop :=
  ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nontrivial B → ∀ (i : ℤ) (ζ : Prim q B),
    Function.Injective (fun c : ZMod q =>
      (c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj (CommRingCat.of B)) :
        (twF q i).obj (CommRingCat.of B)))

namespace LateralTheory.EtaleFoundations.GenConn

theorem twF_map_mk {q : ℕ} (i : ℤ) {B C : CommRingCat.{0}} (f : B ⟶ C) (ζ : Prim q B) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map f.hom) 1) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]

theorem inj_of (h : LateralTheory.EtaleFoundations.twF_gen_inj) (q : ℕ) [NeZero q] (U : Scheme.{0}) [Nonempty U] (i : ℤ)
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (fun c : ZMod q => c.val • twGen i ζ) := by
  intro c1 c2 hc
  simp only at hc
  let φ := ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom
  let m : (Scheme.Γ ⋙ twF q i).obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have hsec : φ (c1.val • m - c2.val • m) = 0 := by
    rw [map_sub, map_nsmul, map_nsmul]; exact sub_eq_zero.2 hc
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  obtain ⟨V, j, v, -, -, -, hV⟩ := LateralTheory.EtaleFoundations.OfRingsLoc.loc_inj (twF q i) (c1.val • m - c2.val • m) hsec u
  let ψ := ((twF q i).map j.appTop).hom
  have hV2 : ψ (c1.val • m) = ψ (c2.val • m) := sub_eq_zero.1 ((ψ.map_sub _ _).symm.trans hV)
  erw [map_nsmul, map_nsmul] at hV2
  have hm : ψ m = Submodule.Quotient.mk (Finsupp.single (ζ.map j.appTop.hom) 1) := twF_map_mk i j.appTop ζ
  rw [hm] at hV2
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := AlgebraicGeometry.Scheme.component_nontrivial V ⊤
  exact h q Γ(V, ⊤) inferInstance i (ζ.map j.appTop.hom) hV2

end LateralTheory.EtaleFoundations.GenConn
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwFInj

theorem prim_field {q : ℕ} {k : Type} [Field k] (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int] using h

theorem pow_mod_eq {k : Type} [Field k] {q : ℕ} {z : k} (hz : IsPrimitiveRoot z q) (n : ℕ) :
    z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

theorem unit_unique {k : Type} [Field k] {q : ℕ} [NeZero q] {z : k} (hz : IsPrimitiveRoot z q)
    {u v : (ZMod q)ˣ} (h : z ^ (u : ZMod q).val = z ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective _ (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_unit {k : Type} [Field k] {q : ℕ} [NeZero q] {z x : k} (hz : IsPrimitiveRoot z q)
    (hx : IsPrimitiveRoot x q) : ∃ u : (ZMod q)ˣ, x = z ^ (u : ZMod q).val := by
  obtain ⟨j, hj, hjx⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : j.Coprime q := (hz.pow_iff_coprime (NeZero.pos q) j).1 (hjx ▸ hx)
  refine ⟨ZMod.unitOfCoprime j hc, ?_⟩
  rw [← hjx]
  congr 1
  simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

end LateralTheory.EtaleFoundations.TwFInj

namespace LateralTheory.EtaleFoundations.TwFInj

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] {k : Type} [Field k] (π : B →+* k) {z : k}
  (hz : IsPrimitiveRoot z q)

noncomputable def ex (ξ : Prim q B) : (ZMod q)ˣ := Classical.choose (exists_unit hz (prim_field (ξ.map π)))

theorem ex_spec (ξ : Prim q B) : π ξ.1 = z ^ (ex π hz ξ : ZMod q).val :=
  Classical.choose_spec (exists_unit hz (prim_field (ξ.map π)))

theorem ex_rel {ζ ξ : Prim q B} {a : (ZMod q)ˣ} (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ex π hz ξ = ex π hz ζ * a := by
  apply unit_unique hz
  rw [← ex_spec, h, map_pow, ex_spec π hz ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_mod_eq hz]

noncomputable def L (i : ℤ) : (Prim q B →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (((ex π hz ξ) ^ i : (ZMod q)ˣ) : ZMod q))

theorem twRel_le_ker (i : ℤ) : twRel q i B ≤ LinearMap.ker (L π hz i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
  apply ULift.ext
  simp [ex_rel π hz h, mul_zpow, mul_comm]

end LateralTheory.EtaleFoundations.TwFInj

theorem LateralTheory.EtaleFoundations.twF_gen_inj_of : LateralTheory.EtaleFoundations.twF_gen_inj := by
  intro q _ B _ hB i ζ c1 c2 hc
  simp only at hc
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  have hz := LateralTheory.EtaleFoundations.TwFInj.prim_field (ζ.map π)
  let Φ := Submodule.liftQ _ (LateralTheory.EtaleFoundations.TwFInj.L π hz i) (LateralTheory.EtaleFoundations.TwFInj.twRel_le_ker π hz i)
  have h2 := congrArg Φ hc
  simp only [Φ, map_nsmul, Submodule.liftQ_apply, LateralTheory.EtaleFoundations.TwFInj.L, Finsupp.linearCombination_single, one_smul] at h2
  have h3 := congrArg ULift.down h2
  have h4 : (c1.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) =
      (c2.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) := by
    simp only [nsmul_eq_mul] at h3
    exact h3
  simpa [ZMod.natCast_zmod_val] using (Units.mul_left_inj _).1 h4
end
